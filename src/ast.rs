use itertools::Itertools;
use ordered_float::OrderedFloat;
use std::{
    f64::{INFINITY, NEG_INFINITY},
    fmt::{Debug, Display},
    hash::{DefaultHasher, Hash, Hasher},
    ops::{Add, Div, Mul, Neg, RangeInclusive, Sub},
    sync::Arc,
};

use crate::{
    error::{Error, SpanInfo},
    factorial, lookup_env,
    parse::precedence,
    predefined::PREDEFINED,
    utils::{snap_to_int, Either, Vars},
    Env,
};

#[derive(Debug)]
pub enum Stmt {
    Definition(String, Expr, SpanInfo),
    Print(Expr, i64),
    Simplify(Expr, i64),
}

#[derive(Debug, Clone)]
/// An expression.
///
/// This is the main AST object of the implementation that results from parsing
/// and evaluates to a [`Val`] during interpretation.
pub enum Expr {
    /// a constant value
    Const(Val, SpanInfo),
    /// an identifier
    Ident(String, SpanInfo),
    /// function application, like f(x), defined by
    /// - the function name (e.g. f)
    /// - the list of argument expressions
    /// - the span of the function name
    /// - the span of the arguments
    ///
    /// ATTENTION
    /// This could also represent an implicit multiplication since e.g. f(x+2)
    /// is ambigous until the type of f (number or function?) is known.
    /// [`Expr::FnApp`] might be interpreted as IMul in eval, since the input grammar is
    /// context free but this problem is context sensitive.
    /// This ambiguity is resolved in the [`disambiguate`] pass.
    FnApp(String, Vec<Expr>, SpanInfo, SpanInfo),

    /// the square root of a number
    Sqrt(Box<Expr>, SpanInfo),
    /// the general n-th root of a number, where n need not be an integer defined by:
    /// - the expression that evaluates to the degree
    /// - the expression that evaluates to the radicant
    /// - the span of the degree expression
    /// - the span of the radicant expression
    /// this defines the x-th root of y as y^(1/x), throwing an error for the zero-th root
    Root(Box<Expr>, Box<Expr>, SpanInfo, SpanInfo),
    /// unary, prefix negation of an expression
    Neg(Box<Expr>, SpanInfo),
    /// unary, postifx factorial of an integer expression.
    /// for non-integers, a gamma function is appropriate and an error is thrown
    Fac(Box<Expr>, SpanInfo),

    /// addition of two expressions
    Add(Box<Expr>, Box<Expr>, SpanInfo),
    /// subtraction of two expressions
    Sub(Box<Expr>, Box<Expr>, SpanInfo),
    /// addition of two expressions
    Mul(Box<Expr>, Box<Expr>, SpanInfo),
    /// implicit multiplication of two expressions
    /// without a multiplication symbol (e.g. 2x, not 2\cdot x)
    IMul(Box<Expr>, Box<Expr>, SpanInfo),
    /// divison of two expressions, can throw an error for x/0
    Div(Box<Expr>, Box<Expr>, SpanInfo),
    /// exponentiation of two expressions
    /// can throw an error for x<0, 0<=y<1, x^{1/y} -> complex results
    Pow(Box<Expr>, Box<Expr>, SpanInfo),

    /// sigma-symbol sum, i.e.
    /// - an expression body
    /// - a loop variable closing that expression
    /// - a range of integer values for the loop variable to take on
    Sum(Box<Expr>, String, RangeInclusive<i64>, SpanInfo),

    /// pi-symbol product, i.e.
    /// - an expression body
    /// - a loop variable closing that expression
    /// - a range of integer values for the loop variable to take on
    Prod(Box<Expr>, String, RangeInclusive<i64>, SpanInfo),

    /// numeric integration of a R (\times R)* -> R function, i.e.
    /// - an expression for the lower limit of the integration variable
    /// - an expression for the upper limit of the integration variable
    /// - the name of the single integration variable
    /// - the body expression that is closed by the integration variable
    ///
    /// Uses G7K15 quadrature with 1e-4 relative error at 20 points.
    /// Multidimensional integration is possible by nesting this construct.
    Int(Box<Expr>, Box<Expr>, String, Box<Expr>, SpanInfo),

    /// a partial derivative consisting of
    /// - a variable name to differentiate with respect to
    /// - an expression to differentiate
    Ddx(String, Box<Expr>, SpanInfo),
}

#[derive(Clone)]
pub struct PredefinedFunction {
    pub closure: Arc<dyn Fn(Vec<Val>, &Env, SpanInfo) -> Result<Val, Error> + Send + Sync>,
    pub identifier: String,
    /// `param_count` is None if any number of arguments is taken
    pub param_count: Option<usize>,
    pub derivative: Option<
        Arc<dyn Fn(Vec<Expr>, SpanInfo) -> Result<(Expr, Vec<&'static str>), Error> + Send + Sync>,
    >,
}

#[derive(Clone)]
/// The value that an expression evaluates to.
pub enum Val {
    /// numeric value represented as `f64`
    Num(f64),
    /// Lambda containing:
    /// - parameter names (empty vector if it is a predefined function)
    /// - either:
    ///   - the body of the function
    ///   - or a closure representing a predefined function as well as its name
    /// A negative argument count allows any number of arguments
    Lambda(Either<PredefinedFunction, (Vec<String>, Box<Expr>)>),
}

pub enum Typ {
    Num,
    Lam,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
/// A representation of mathematical expressions that is more suited
/// for simplicification and manipulation than [`Expr`].
/// It derives many more traits that [`Expr`] can't (`Hash, Eq, Ord` etc.)
///
///
/// Note that in contrast to [`Expr`]:
/// - some redundant operators are removed. `Sub` is expressed with unary negation, `Sqrt` as a `Root` etc.
/// - there is no [`SpanInfo`], since generated expressions have only vaguely corresponding source code
/// - associative n-ary operators like [`Expr::Add`] and [`Expr::Mul`] are flattened into arrays
///   - this allows for easier grouping and simplifying of terms in sums and products
pub enum SExpr {
    Const(SVal),
    Ident(String),
    FnApp(String, Vec<SExpr>),
    Neg(Box<SExpr>),
    // associative operations are n-ary over vectors:
    Add(Vec<SExpr>),
    Mul(Vec<SExpr>),
    //non-associative operations use binary nodes:
    Div(Box<SExpr>, Box<SExpr>),
    Pow(Box<SExpr>, Box<SExpr>),
    // Special operations
    /// degree, radicant
    Root(Box<SExpr>, Box<SExpr>),
    Fac(Box<SExpr>),
    /// body, loop variable, lower, upper
    Sum(Box<SExpr>, String, i64, i64),
    /// body, loop variable, lower, upper
    Prod(Box<SExpr>, String, i64, i64),
    /// lower limit, upper limit, integration variable, body
    Int(Box<SExpr>, Box<SExpr>, String, Box<SExpr>),
}

/// Negation of an [`SExpr`]
impl Neg for SExpr {
    type Output = SExpr;
    fn neg(self) -> Self::Output {
        SExpr::Neg(Box::new(self))
    }
}
/// Addition for [`SExpr`]
impl Add for SExpr {
    type Output = SExpr;
    fn add(self, rhs: Self) -> Self::Output {
        // make sure the sum is ordered
        if self < rhs {
            SExpr::Add(vec![self, rhs])
        } else {
            SExpr::Add(vec![rhs, self])
        }
    }
}
/// Multiplication for [`SExpr`]
impl Mul for SExpr {
    type Output = SExpr;
    fn mul(self, rhs: Self) -> Self::Output {
        // make sure the product is ordered
        if self < rhs {
            SExpr::Mul(vec![self, rhs])
        } else {
            SExpr::Mul(vec![rhs, self])
        }
    }
}
/// Subtraction for [`SExpr`]
impl Sub for SExpr {
    type Output = SExpr;
    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}
/// Division for [`SExpr`]
impl Div for SExpr {
    type Output = SExpr;
    fn div(self, rhs: Self) -> Self::Output {
        SExpr::Div(Box::new(self.clone()), Box::new(rhs))
    }
}
/// A trait that allows [`i64`] and [`f64`] to be
/// converted to the corresponding [`SExpr`]
pub trait ToSExprConst {
    fn to_const(&self) -> SExpr;
}
impl ToSExprConst for f64 {
    fn to_const(&self) -> SExpr {
        SExpr::Const(SVal::Real((*self).into()))
    }
}
impl ToSExprConst for i64 {
    fn to_const(&self) -> SExpr {
        SExpr::Const(SVal::Int(*self))
    }
}
pub fn cnst<T: ToSExprConst>(c: T) -> SExpr {
    c.to_const()
}
impl SExpr {
    /// Apply a unary function to an [`SExpr`] by name
    pub fn unary(&self, fn_name: &str) -> Self {
        SExpr::FnApp(fn_name.to_owned(), vec![self.clone()])
    }
    /// Create the square root of an [`SExpr`]
    pub fn sqrt(&self) -> Self {
        SExpr::Root(Box::new(cnst(2)), Box::new(self.clone()))
    }
    /// Take an [`SExpr`] to the power of another [`SExpr`]
    pub fn pow(&self, rhs: Self) -> Self {
        SExpr::Pow(Box::new(self.clone()), Box::new(rhs))
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
/// A Value for use in Expression manipulation and simplification.
/// Derives many useful traits (`Hash, Eq, Ord` etc.) that [`Val`] cannot.
/// In return, some other conveniences (the closures attached to predefined function objects etc.) are lost.
/// - `f64` is wrapped into [`OrderedFloat<f64>`]
/// - Integers are created if the distance from the original [`f64`] is less than [`f64::EPSILON`]
pub enum SVal {
    Int(i64),
    Real(OrderedFloat<f64>),
    Lambda(Either<SPredefinedFunction, (Vec<String>, Box<SExpr>)>),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct SPredefinedFunction {
    pub identifier: String,
    pub param_count: Option<usize>,
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Const(val, _) => write!(f, "{}", val),
            Expr::Ident(name, _) => write!(f, "{}", name),
            Expr::FnApp(func_name, args, _, _) => {
                let args_str: String = args.iter().map(|expr| format!("{}", expr)).join(", ");
                write!(f, r"{}\left({}\right)", func_name, args_str)
            }
            Expr::Sqrt(expr, _) => write!(f, r"\sqrt{{ {} }}", expr),
            Expr::Root(degree, radicant, _, _) => write!(f, r"\sqrt[{}]{{ {} }}", degree, radicant),
            Expr::Neg(expr, _) => write!(f, r"\left(-{}\right)", expr),
            Expr::Fac(expr, _) => write!(f, r"\left({}!\right)", expr),
            Expr::Add(expr, expr1, _) => write!(f, r"\left({} + {}\right)", expr, expr1),
            Expr::Sub(expr, expr1, _) => write!(f, r"\left({} - {}\right)", expr, expr1),
            Expr::Mul(expr, expr1, _) => write!(f, r"\left({} \cdot {}\right)", expr, expr1),
            Expr::IMul(expr, expr1, _) => write!(f, r"\left({} {}\right)", expr, expr1),
            Expr::Div(expr, expr1, _) => write!(f, r"\frac{{ {} }}{{ {} }}", expr, expr1),
            Expr::Pow(expr, expr1, _) => write!(f, r"{}^{{ {} }}", expr, expr1),
            Expr::Sum(expr, loop_var, range, _) => write!(
                f,
                r"\sum_{{ {} = {} }}^{{ {} }}\left({}\right)",
                loop_var,
                range.start(),
                range.end(),
                expr
            ),
            Expr::Prod(expr, loop_var, range, _) => write!(
                f,
                r"\prod_{{ {} = {} }}^{{ {} }}\left({}\right)",
                loop_var,
                range.start(),
                range.end(),
                expr
            ),
            Expr::Int(lower, upper, int_var, body, _) => write!(
                f,
                r"\int_{{ {} }}^{{ {} }}\left({}\right)\,d{}",
                lower, upper, body, int_var
            ),
            Expr::Ddx(x, expr, _) => write!(
                f,
                r"\frac{{\partial}}{{\partial {} }} \left({}\right)",
                x, expr
            ),
        }
    }
}
impl Display for PredefinedFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, r"{}", self.identifier)
    }
}

impl Into<Typ> for Val {
    fn into(self) -> Typ {
        match self {
            Val::Num(_) => Typ::Num,
            Val::Lambda(_) => Typ::Lam,
        }
    }
}
impl Into<Typ> for &Val {
    fn into(self) -> Typ {
        match self {
            Val::Num(_) => Typ::Num,
            Val::Lambda(_) => Typ::Lam,
        }
    }
}
impl Typ {
    pub fn name(&self) -> String {
        match self {
            Self::Num => "number".to_owned(),
            Self::Lam => "function".to_owned(),
        }
    }
}
impl Display for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Val::Num(INFINITY) => write!(f, r"\infty"),
            Val::Num(NEG_INFINITY) => write!(f, r"-\infty"),
            Val::Num(x) => write!(f, "{}", snap_to_int(*x)),
            Val::Lambda(func) => match func {
                Either::Left(predef) => {
                    if let Some(count) = predef.param_count {
                        if count > 0 {
                            let params = Vars::default().into_iter().take(count).join(", ");
                            return write!(
                                f,
                                r"{} \\mapsto {}\left({}\right)",
                                params, predef.identifier, params
                            );
                        }
                    };
                    write!(f, "{}", predef)
                }
                Either::Right((params, expr)) => {
                    if params.is_empty() {
                        write!(f, "{}", expr)
                    } else {
                        write!(f, "{} \\mapsto {}", params.join(", "), expr)
                    }
                }
            },
        }
    }
}

impl Debug for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl Into<SExpr> for Expr {
    fn into(self) -> SExpr {
        fn flatten_add(expr: Expr, vec: &mut Vec<SExpr>) {
            match expr {
                Expr::Add(ref lhs, ref rhs, _) => {
                    flatten_add((**lhs).clone(), vec);
                    flatten_add((**rhs).clone(), vec);
                }
                Expr::Sub(ref lhs, ref rhs, _) => {
                    flatten_add((**lhs).clone(), vec);
                    flatten_add(Expr::Neg(rhs.clone(), SpanInfo::default()), vec);
                }
                _ => {
                    vec.push(expr.clone().into());
                }
            }
        }
        fn flatten_mul(expr: Expr, vec: &mut Vec<SExpr>) {
            match expr {
                Expr::Mul(ref lhs, ref rhs, _) => {
                    flatten_mul((**lhs).clone(), vec);
                    flatten_mul((**rhs).clone(), vec);
                }
                Expr::IMul(ref lhs, ref rhs, _) => {
                    flatten_mul((**lhs).clone(), vec);
                    flatten_mul((**rhs).clone(), vec);
                }
                _ => {
                    vec.push(expr.clone().into());
                }
            }
        }
        match self {
            Expr::Const(val, _) => SExpr::Const(val.into()),
            Expr::Ident(name, _) => SExpr::Ident(name),
            Expr::Sqrt(expr, _) => SExpr::Root(
                Box::new(SExpr::Const(SVal::Int(2))),
                Box::new((*expr).into()),
            ),
            Expr::Neg(expr, _) => SExpr::Neg(Box::new((*expr).into())),
            Expr::Fac(expr, _) => SExpr::Fac(Box::new((*expr).into())),
            Expr::Root(expr, expr1, _, _) => {
                SExpr::Root(Box::new((*expr).into()), Box::new((*expr1).into()))
            }
            Expr::Div(expr, expr1, _) => {
                SExpr::Div(Box::new((*expr).into()), Box::new((*expr1).into()))
            }
            Expr::Pow(expr, expr1, _) => {
                SExpr::Pow(Box::new((*expr).into()), Box::new((*expr1).into()))
            }
            Expr::Sum(expr, loop_var, range_inclusive, _) => SExpr::Sum(
                Box::new((*expr).into()),
                loop_var,
                *range_inclusive.start(),
                *range_inclusive.end(),
            ),
            Expr::Prod(expr, loop_var, range_inclusive, _) => SExpr::Prod(
                Box::new((*expr).into()),
                loop_var,
                *range_inclusive.start(),
                *range_inclusive.end(),
            ),
            Expr::Int(lower, upper, int_var, body, _) => SExpr::Int(
                Box::new((*lower).into()),
                Box::new((*upper).into()),
                int_var,
                Box::new((*body).into()),
            ),
            Expr::FnApp(fn_name, args, _, _) => {
                SExpr::FnApp(fn_name, args.into_iter().map(|arg| arg.into()).collect())
            }
            Expr::Sub(lhs, rhs, _) => {
                let s = SpanInfo::default();
                Expr::Add(lhs, Box::new(Expr::Neg(rhs, s)), s).into()
            }
            Expr::Add(lhs, rhs, _) => {
                let mut res = vec![];
                flatten_add(*lhs, &mut res);
                flatten_add(*rhs, &mut res);
                res.sort();
                SExpr::Add(res)
            }
            Expr::Mul(lhs, rhs, _) => {
                let mut res = vec![];
                flatten_mul(*lhs, &mut res);
                flatten_mul(*rhs, &mut res);
                res.sort();
                SExpr::Mul(res)
            }
            Expr::IMul(lhs, rhs, _) => {
                let mut res = vec![];
                flatten_mul(*lhs, &mut res);
                flatten_mul(*rhs, &mut res);
                res.sort();
                SExpr::Mul(res)
            }
            Expr::Ddx(_, _, _) => unreachable!(),
        }
    }
}

impl Into<SVal> for Val {
    fn into(self) -> SVal {
        match self {
            Val::Num(x) => {
                let x_int = x.floor();
                if (x_int - x).abs() < f64::EPSILON && x.is_finite() {
                    SVal::Int(x_int as i64)
                } else {
                    SVal::Real(x.into())
                }
            }
            Val::Lambda(either) => match either {
                Either::Left(predef) => SVal::Lambda(Either::Left(predef.into())),
                Either::Right((params, expr)) => {
                    SVal::Lambda(Either::Right((params, Box::new((*expr).into()))))
                }
            },
        }
    }
}

impl SVal {
    pub fn snap(&self) -> Self {
        match self {
            SVal::Int(x) => SVal::Int(*x),
            SVal::Real(x) => {
                let x_int = x.floor();
                if (x_int - **x).abs() < f64::EPSILON && x.is_finite() {
                    SVal::Int(x_int as i64)
                } else {
                    self.clone()
                }
            }
            SVal::Lambda(_) => self.clone(),
        }
    }

    pub fn is_numeric(&self) -> bool {
        match self {
            SVal::Int(_) => true,
            SVal::Real(_) => true,
            SVal::Lambda(_) => false,
        }
    }
}
pub fn sval_to_val(sval: SVal, env: &Env) -> Result<Val, Error> {
    match sval {
        SVal::Int(i) => Ok(Val::Num(i as f64)),
        SVal::Real(ordered_float) => Ok(Val::Num(ordered_float.into_inner())),
        SVal::Lambda(either) => {
            let span = SpanInfo::default();
            match either {
                Either::Left(predef) => lookup_env(&predef.identifier, env, span),
                Either::Right((params, box body)) => Ok(Val::Lambda(Either::Right((
                    params,
                    Box::new(sexpr_to_expr(body, env, span)),
                )))),
            }
        }
    }
}
pub fn _val_to_sval(val: Val) -> SVal {
    val.into()
}
impl Display for SVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SVal::Real(val) if *val == INFINITY => write!(f, r"\infty"),
            SVal::Real(val) if *val == NEG_INFINITY => write!(f, r"-\infty"),
            SVal::Real(x) => write!(f, r"{}", x),
            SVal::Int(i) => write!(f, r"{}", i),
            SVal::Lambda(func) => match func {
                Either::Left(predef) => {
                    if let Some(count) = predef.param_count {
                        if count > 0 {
                            let params = Vars::default().into_iter().take(count).join(", ");
                            return write!(
                                f,
                                r"{} \\mapsto {}\left({}\right)",
                                params, predef.identifier, params
                            );
                        }
                    };
                    write!(f, "{}", predef)
                }
                Either::Right((params, box expr)) => {
                    if params.is_empty() {
                        write!(f, "{}", expr.pretty(None))
                    } else {
                        write!(f, "{} \\mapsto {}", params.join(", "), expr.pretty(None))
                    }
                }
            },
        }
    }
}

impl Into<SPredefinedFunction> for PredefinedFunction {
    fn into(self) -> SPredefinedFunction {
        SPredefinedFunction {
            identifier: self.identifier,
            param_count: self.param_count,
        }
    }
}
impl Into<PredefinedFunction> for SPredefinedFunction {
    fn into(self) -> PredefinedFunction {
        if let Some(Val::Lambda(Either::Left(p))) = PREDEFINED.get(&self.identifier) {
            p.clone()
        } else {
            unreachable!()
        }
    }
}
impl Display for SPredefinedFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, r"{}", self.identifier)
    }
}

pub fn sexpr_to_expr(expr: SExpr, env: &Env, s: SpanInfo) -> Expr {
    fn associative(
        sexprs: Vec<SExpr>,
        constructor: fn(Box<Expr>, Box<Expr>, SpanInfo) -> Expr,
        s_constructor: fn(Vec<SExpr>) -> SExpr,
        neutral_element: f64,
        env: &Env,
        s: SpanInfo,
    ) -> Expr {
        match &sexprs[..] {
            [] => Expr::Const(Val::Num(neutral_element), s), // TODO: is this always correct?
            [singleton] => sexpr_to_expr(singleton.clone(), env, s),
            _ => {
                let mut rest = sexprs;
                let first = rest.pop().unwrap();
                constructor(
                    Box::new(sexpr_to_expr(first, env, s)),
                    Box::new(sexpr_to_expr(s_constructor(rest), env, s)),
                    s,
                )
            }
        }
    }
    match expr {
        // base cases
        SExpr::Const(sval) => match sval {
            SVal::Int(x) => Expr::Const(Val::Num(x as f64), s),
            SVal::Real(x) => Expr::Const(Val::Num(x.into_inner()), s),
            SVal::Lambda(either) => match either {
                Either::Left(predef) => {
                    Expr::Const(lookup_env(&predef.identifier, env, s).unwrap(), s)
                }
                Either::Right((params, expr)) => Expr::Const(
                    Val::Lambda(Either::Right((
                        params,
                        Box::new(sexpr_to_expr(*expr, env, s)),
                    ))),
                    s,
                ),
            },
        },
        SExpr::Ident(name) => Expr::Ident(name, s),
        // un-flatten associative operators
        SExpr::Add(sexprs) => associative(sexprs, Expr::Add, SExpr::Add, 0., env, s),
        SExpr::Mul(sexprs) => associative(sexprs, Expr::Mul, SExpr::Mul, 1., env, s),
        // unary recursive cases
        SExpr::Neg(sexpr) => Expr::Neg(Box::new(sexpr_to_expr(*sexpr, env, s)), s),
        SExpr::Fac(sexpr) => Expr::Fac(Box::new(sexpr_to_expr(*sexpr, env, s)), s),
        // binary recursive cases
        SExpr::Div(sexpr, sexpr1) => Expr::Div(
            Box::new(sexpr_to_expr(*sexpr, env, s)),
            Box::new(sexpr_to_expr(*sexpr1, env, s)),
            s,
        ),
        SExpr::Pow(sexpr, sexpr1) => Expr::Pow(
            Box::new(sexpr_to_expr(*sexpr, env, s)),
            Box::new(sexpr_to_expr(*sexpr1, env, s)),
            s,
        ),
        SExpr::Root(sexpr, sexpr1) => Expr::Root(
            Box::new(sexpr_to_expr(*sexpr, env, s)),
            Box::new(sexpr_to_expr(*sexpr1, env, s)),
            s,
            s,
        ),
        // other recursive cases
        SExpr::FnApp(fn_name, sexprs) => Expr::FnApp(
            fn_name,
            sexprs
                .into_iter()
                .map(|arg| sexpr_to_expr(arg, env, s))
                .collect(),
            s,
            s,
        ),
        SExpr::Sum(sexpr, loop_var, lower, upper) => Expr::Sum(
            Box::new(sexpr_to_expr(*sexpr, env, s)),
            loop_var,
            lower..=upper,
            s,
        ),
        SExpr::Prod(sexpr, loop_var, lower, upper) => Expr::Prod(
            Box::new(sexpr_to_expr(*sexpr, env, s)),
            loop_var,
            lower..=upper,
            s,
        ),
        SExpr::Int(lower, upper, int_var, body) => Expr::Int(
            Box::new(sexpr_to_expr(*lower, env, s)),
            Box::new(sexpr_to_expr(*upper, env, s)),
            int_var,
            Box::new(sexpr_to_expr(*body, env, s)),
            s,
        ),
    }
}

impl SExpr {
    pub fn calculate_hash(&self) -> u64 {
        let mut s = DefaultHasher::new();
        self.hash(&mut s);
        s.finish()
    }
}

impl SExpr {
    pub fn pretty(&self, prec: Option<usize>) -> String {
        let mut res = String::new();
        let inner = precedence(self);
        let outer = prec.unwrap_or(0);
        let prec = Some(inner);
        // open bracket if applicable
        if outer > inner {
            res.push_str(r"\left(");
        }
        res.push_str(&match self {
            SExpr::Const(sval) => format!("{}", sval),
            SExpr::Ident(name) => name.to_owned(),
            SExpr::FnApp(fn_name, sexprs) => format!(
                r"{}\left({}\right)",
                fn_name,
                sexprs.iter().map(|expr| expr.pretty(Some(0))).join(", ")
            ),
            SExpr::Neg(sexpr) => format!("-{}", sexpr.pretty(prec)),
            SExpr::Fac(sexpr) => format!("{}!", sexpr.pretty(prec)),
            SExpr::Add(sexprs) => match sexprs.len() {
                0 => String::new(),
                1 => sexprs.first().unwrap().pretty(prec),
                _ => {
                    let mut sorted = sexprs.clone();
                    sorted.sort_unstable();
                    let mut out = sorted.last().unwrap().pretty(prec);

                    for expr in sorted.iter().rev().skip(1) {
                        match expr {
                            SExpr::Neg(inner) => {
                                let neg_prec = Some(precedence(expr));
                                out.push_str("-");
                                out.push_str(&inner.pretty(neg_prec));
                            }
                            SExpr::Const(val) if val.is_negative() => {
                                out.push_str(&expr.pretty(prec));
                            }
                            _ => {
                                out.push_str("+");
                                out.push_str(&expr.pretty(prec));
                            }
                        }
                    }
                    out
                }
            },
            SExpr::Mul(sexprs) => sexprs
                .iter()
                .sorted()
                .map(|expr| expr.pretty(prec))
                .join(r" "),
            SExpr::Div(sexpr, sexpr1) => format!(
                r"\frac{{ {} }}{{ {} }}",
                sexpr.pretty(Some(0)),
                sexpr1.pretty(Some(0)),
            ),
            SExpr::Pow(sexpr, sexpr1) => format!(
                r"{{ {} }}^{{ {} }}",
                sexpr.pretty(prec),
                sexpr1.pretty(prec),
            ),
            SExpr::Root(sexpr, sexpr1) => format!(
                r"\sqrt[ {} ]{{ {} }}",
                sexpr.pretty(prec),
                sexpr1.pretty(prec),
            ),
            SExpr::Sum(sexpr, loop_var, from, to) => format!(
                r"\sum_{{ {} = {} }}^{{ {} }} {}",
                loop_var,
                from,
                to,
                sexpr.pretty(prec)
            ),
            SExpr::Prod(sexpr, loop_var, from, to) => format!(
                r"\prod_{{ {} = {} }}^{{ {} }} {}",
                loop_var,
                from,
                to,
                sexpr.pretty(prec)
            ),
            SExpr::Int(lower, upper, int_var, body) => format!(
                r"\int_{{ {} }}^{{ {} }} {} \,d{}",
                lower.pretty(prec),
                upper.pretty(prec),
                body.pretty(prec),
                int_var
            ),
        });
        if outer > inner {
            res.push_str(r"\right)");
        }
        res
    }
}

fn sval_binop<T: Fn(f64, f64) -> f64>(
    lhs: &SVal,
    rhs: &SVal,
    op_r: T,
    op_i: Option<Box<dyn Fn(i64, i64) -> i64>>,
) -> Option<SVal> {
    match lhs {
        SVal::Int(l) => match rhs {
            SVal::Int(r) if let Some(op_i) = op_i => Some(SVal::Int(op_i(*l, *r))),
            SVal::Int(r) => Some(SVal::Real(OrderedFloat(op_r(*l as f64, *r as f64))).snap()),
            SVal::Real(r) => Some(SVal::Real(op_r(*l as f64, **r).into()).snap()),
            SVal::Lambda(_) => None,
        },
        SVal::Real(l) => match rhs {
            SVal::Int(r) => Some(SVal::Real(OrderedFloat(op_r(**l, *r as f64))).snap()),
            SVal::Real(r) => Some(SVal::Real((op_r(**l, **r)).into()).snap()),
            SVal::Lambda(_) => None,
        },
        SVal::Lambda(_) => None,
    }
}

impl SVal {
    pub fn pow(&self, rhs: &SVal) -> Option<SVal> {
        match self {
            SVal::Int(l) => match rhs {
                SVal::Int(r) if *r >= 0 => {
                    if let Ok(r) = (*r).try_into() {
                        Some(SVal::Int((*l).pow(r)))
                    } else {
                        Some(SVal::Real(((*l as f64).powf(*r as f64)).into()).snap())
                    }
                }
                SVal::Int(r) => Some(SVal::Real(((*l as f64).powf(*r as f64)).into()).snap()),
                SVal::Real(r) => Some(SVal::Real(((*l as f64).powf(**r)).into()).snap()),
                SVal::Lambda(_) => None,
            },
            SVal::Real(l) => match rhs {
                SVal::Int(r) if let Ok(r) = (*r).try_into() => {
                    Some(SVal::Real((**l).powi(r).into()).snap())
                }
                SVal::Int(r) => Some(SVal::Real((**l).powf(*r as f64).into()).snap()),
                SVal::Real(r) => Some(SVal::Real(((*l).powf(**r)).into()).snap()),
                SVal::Lambda(_) => None,
            },
            SVal::Lambda(_) => None,
        }
    }

    pub fn invert(&self) -> Option<SVal> {
        match self {
            SVal::Int(0) => None,
            SVal::Int(1) => Some(SVal::Int(1)),
            SVal::Int(i) => Some(SVal::Real((1. / (*i as f64)).into())),
            SVal::Real(x) => Some(SVal::Real((1. / **x).into())),
            SVal::Lambda(_) => None,
        }
    }

    pub fn fact(&self) -> Option<SVal> {
        match self {
            SVal::Int(i) if 0 <= *i && *i < 20 => Some(SVal::Int((1..=*i).product())),
            SVal::Int(x) if let Some(res) = factorial(*x as f64) => {
                Some(SVal::Real(res.into()).snap())
            }
            SVal::Real(x) if let Some(res) = factorial(**x) => Some(SVal::Real(res.into()).snap()),
            SVal::Real(_) => None,
            SVal::Int(_) => None,
            SVal::Lambda(_) => None,
        }
    }
}

impl Add for &SVal {
    type Output = Option<SVal>;
    fn add(self, rhs: Self) -> Self::Output {
        sval_binop(self, rhs, |a, b| a + b, Some(Box::new(|a, b| a + b)))
    }
}

impl Mul for &SVal {
    type Output = Option<SVal>;
    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (SVal::Int(0), _) => Some(SVal::Int(0)),
            (_, SVal::Int(0)) => Some(SVal::Int(0)),
            (SVal::Real(x), _) if x.abs() < f64::EPSILON => Some(SVal::Int(0)),
            (_, SVal::Real(x)) if x.abs() < f64::EPSILON => Some(SVal::Int(0)),
            _ => sval_binop(self, rhs, |a, b| a * b, Some(Box::new(|a, b| a * b))),
        }
    }
}

impl Div for &SVal {
    type Output = Option<SVal>;

    fn div(self, rhs: Self) -> Self::Output {
        sval_binop(self, rhs, |a, b| a / b, None)
    }
}

impl Neg for &SVal {
    type Output = Option<SVal>;
    fn neg(self) -> Self::Output {
        match self {
            SVal::Int(x) => Some(SVal::Int(-x)),
            SVal::Real(ordered_float) => Some(SVal::Real(-ordered_float).snap()),
            SVal::Lambda(_) => None,
        }
    }
}

impl Sub for &SVal {
    type Output = Option<SVal>;
    fn sub(self, rhs: Self) -> Self::Output {
        if let Some(neg) = -rhs {
            if let Some(res) = self + &neg {
                return Some(res);
            }
        }
        None
    }
}

impl SVal {
    pub fn is_near(&self, n: i64) -> bool {
        match self {
            SVal::Int(i) => *i == n,
            SVal::Real(x) => {
                let x_int = x.round();
                if (x_int - **x).abs() < f64::EPSILON && x.is_finite() {
                    x_int as i64 == n
                } else {
                    false
                }
            }
            SVal::Lambda(_) => false,
        }
    }

    pub fn is_negative(&self) -> bool {
        match self {
            SVal::Int(i) => i.is_negative(),
            SVal::Real(r) => r.is_sign_negative(),
            SVal::Lambda(_) => false,
        }
    }

    pub fn to_f64(&self) -> Option<f64> {
        match self {
            SVal::Int(i) => Some(*i as f64),
            SVal::Real(r) => Some((*r).into()),
            SVal::Lambda(_) => None,
        }
    }
}
