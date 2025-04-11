use std::{
    f64::{INFINITY, NEG_INFINITY},
    fmt::Display,
    hash::{DefaultHasher, Hash, Hasher},
    ops::{Add, Mul},
};

use itertools::Itertools;
use ordered_float::OrderedFloat;

use crate::{
    differentiate::ddx, error::SpanInfo, lookup_env, parse::precedence, utils::Either, Env, Expr, PredefinedFunction, Val, Vars
};

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
    Root(Box<SExpr>, Box<SExpr>),
    Fac(Box<SExpr>),
    Sum(Box<SExpr>, String, i64, i64),
    Prod(Box<SExpr>, String, i64, i64),
    Int(Box<SExpr>, Box<SExpr>, String, Box<SExpr>),
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
    identifier: String,
    param_count: Option<usize>,
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
            Expr::Ddx(x, expr, _) => {
                println!("{:?}, {}", expr, x);
                todo!()
            },
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
    fn calculate_hash(&self) -> u64 {
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
            SExpr::Add(sexprs) => sexprs.iter().map(|expr| expr.pretty(prec)).join("+"),
            SExpr::Mul(sexprs) => sexprs.iter().map(|expr| expr.pretty(prec)).join(r"\cdot "),
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

/// The rules to simplify expressions with.
/// Order matters!
const RULES: [fn(SExpr, &Env) -> SExpr; 6] = [
    absorbing_element,
    idempotence,
    constant_fold,
    bounds_make_it_trivial,
    annihilating_ops,
    shift_neg_out_of_mul,
];

/// Simplify an expression.
/// TODO RULES:
/// - single element sums or products are their body, with the loop variable subsituted for its single value
pub fn simplify(expr: &Expr, env: &Env) -> SExpr {
    let mut current: SExpr = expr.clone().into();
    let mut prev_hash: u64 = 0;
    loop {
        println!("SIMPLIFYING {:?}", current);
        current = apply(current, env, &RULES);
        let new_hash = current.calculate_hash();
        if prev_hash == new_hash {
            break;
        };
        prev_hash = new_hash;
    }
    return current;
}

/// Traverse the [`SExpr`] AST, applying all `rules` once, bottom-up in a recursive descent.
fn apply<F: Fn(SExpr, &Env) -> SExpr>(sexpr: SExpr, env: &Env, rules: &[F]) -> SExpr {
    // first, recurse through the ast, applying all rules to all children
    let updated = match sexpr {
        // atomic, cannot be simplified
        SExpr::Const(_) => sexpr,
        SExpr::Ident(_) => sexpr,
        // unary recursive
        SExpr::Neg(box sexpr) => SExpr::Neg(Box::new(apply(sexpr, env, rules))),
        SExpr::Fac(box sexpr) => SExpr::Fac(Box::new(apply(sexpr, env, rules))),
        // binary recursive
        SExpr::Div(box sexpr, box sexpr1) => SExpr::Div(
            Box::new(apply(sexpr, env, rules)),
            Box::new(apply(sexpr1, env, rules)),
        ),
        SExpr::Pow(box sexpr, box sexpr1) => SExpr::Pow(
            Box::new(apply(sexpr, env, rules)),
            Box::new(apply(sexpr1, env, rules)),
        ),
        SExpr::Root(box sexpr, box sexpr1) => SExpr::Root(
            Box::new(apply(sexpr, env, rules)),
            Box::new(apply(sexpr1, env, rules)),
        ),
        // associative relations
        SExpr::Add(sexprs) => SExpr::Add(
            sexprs
                .into_iter()
                .map(|sexpr| apply(sexpr, env, rules))
                .collect(),
        ),
        SExpr::Mul(sexprs) => SExpr::Mul(
            sexprs
                .into_iter()
                .map(|sexpr| apply(sexpr, env, rules))
                .collect(),
        ),
        // reductions
        SExpr::Sum(box sexpr, loop_var, lower, upper) => {
            SExpr::Sum(Box::new(apply(sexpr, env, rules)), loop_var, lower, upper)
        }
        SExpr::Prod(box sexpr, loop_var, lower, upper) => {
            SExpr::Prod(Box::new(apply(sexpr, env, rules)), loop_var, lower, upper)
        }
        // others
        SExpr::FnApp(name, sexprs) => SExpr::FnApp(
            name,
            sexprs
                .into_iter()
                .map(|sexpr| apply(sexpr, env, rules))
                .collect(),
        ),
        SExpr::Int(box lower, box upper, int_var, box body) => SExpr::Int(
            Box::new(apply(lower, env, rules)),
            Box::new(apply(upper, env, rules)),
            int_var,
            Box::new(apply(body, env, rules)),
        ),
    };
    // then, apply the rules to the current node
    rules.iter().fold(updated, |acc, rule| rule(acc, env))
}

/// Remove operations when they have no effect, i.e. when the neutral element is used or the inverse is applied next.
/// For each operation in the AST, this function asks *on which argument(s) does this operation have no effect?*
///
/// - x + 0 = x
/// - x * 1 = x
/// - x / 1 = x
/// - 1st root of x = x
/// - x ^ 1 = x
fn idempotence(sexpr: SExpr, _: &Env) -> SExpr {
    fn associative(
        mut sexprs: Vec<SExpr>,
        constructor: fn(Vec<SExpr>) -> SExpr,
        neutral_element: i64,
    ) -> SExpr {
        sexprs.retain(|expr| match expr {
            SExpr::Const(SVal::Int(x)) => *x != neutral_element,
            _ => true,
        });
        constructor(sexprs)
    }
    match sexpr {
        SExpr::Neg(box SExpr::Neg(x)) => *x,
        SExpr::Add(sexprs) => associative(sexprs, SExpr::Add, 0),
        SExpr::Mul(sexprs) => associative(sexprs, SExpr::Mul, 1),
        SExpr::Div(numerator, box SExpr::Const(SVal::Int(1))) => *numerator,
        SExpr::Root(box SExpr::Const(SVal::Int(1)), radicant) => *radicant,
        SExpr::Pow(base, box SExpr::Const(SVal::Int(1))) => *base,
        _ => sexpr,
    }
}

/// Simplify expressions where the bounds of the sum, product or integral make it trivial
/// - empty sum is zero
/// - empty product is one
/// - integrals with equal lower and upper bound is zero
fn bounds_make_it_trivial(sexpr: SExpr, _: &Env) -> SExpr {
    match sexpr {
        // empty sum is zero
        SExpr::Add(summands) if summands.is_empty() => SExpr::Const(SVal::Int(0)),
        SExpr::Sum(_, _, lower, upper) if lower > upper => SExpr::Const(SVal::Int(0)),
        // empty product is one
        SExpr::Mul(factors) if factors.is_empty() => SExpr::Const(SVal::Int(1)),
        SExpr::Prod(_, _, lower, upper) if lower > upper => SExpr::Const(SVal::Int(1)),
        // integrals with equal lower and upper bound is zero
        SExpr::Int(box ref lower, box ref upper, _, _) if lower == upper => {
            SExpr::Const(SVal::Int(0))
        }
        _ => sexpr,
    }
}

/// Checks for absorbing elements
/// - zero in a multiplication
fn absorbing_element(sexpr: SExpr, _: &Env) -> SExpr {
    match sexpr {
        SExpr::Mul(ref sexprs)
            if sexprs.iter().any(|expr| match expr {
                SExpr::Const(SVal::Int(0)) => true,
                _ => false,
            }) =>
        {
            SExpr::Const(SVal::Int(0))
        }
        _ => sexpr,
    }
}

/// Remove subsequent applications of operators that annihilate one another
///
/// Unary minus with itself
/// - -(-x) = x
/// Roots and Powers
/// - \sqrt[y]{x^y} = x
/// - sqrt[y]{x}^y = x
/// Addition and Negation
/// - x + (-x) = 0
/// - (-x) + x = 0
/// TODO: multiplication and division
fn annihilating_ops(sexpr: SExpr, _: &Env) -> SExpr {
    match sexpr {
        SExpr::Neg(box SExpr::Neg(box x)) => x,
        SExpr::Root(box deg1, box SExpr::Pow(box x, box deg2)) if deg1 == deg2 => x,
        SExpr::Pow(box SExpr::Root(box y1, box x), box y2) if y1 == y2 => x,
        SExpr::Add(sexprs)
            if sexprs.iter().permutations(2).any(|pair| match &pair[..] {
                [&ref a, &SExpr::Neg(box ref b)] if *a == *b => true,
                [&SExpr::Neg(box ref a), &ref b] if *a == *b => true,
                _ => false,
            }) =>
        {
            // remove the duplicate pair(s)
            let mut exprs = sexprs.clone();
            for i in 0..exprs.len() {
                for j in (i + 1)..exprs.len() {
                    if match [&exprs[i], &exprs[j]] {
                        [&ref a, SExpr::Neg(box ref b)] if *a == *b => true,
                        [SExpr::Neg(box ref a), &ref b] if *a == *b => true,
                        _ => false,
                    } {
                        println!("{:?} AND {:?}", exprs[i], exprs[j]);
                        // remove upper index first to avoid the left-shift causing the wrong element
                        // to be removed
                        exprs.remove(j);
                        exprs.remove(i);
                    }
                }
            }
            SExpr::Add(exprs)
        }
        // SExpr::Mul(sexprs) => todo!(),
        // SExpr::Div(sexpr, sexpr1) => todo!(),
        _ => sexpr,
    }
}

/// Negations in products can be reduced since only their parity matters
/// - -5x * 2y * -6i = 5x * 2y * 6i
fn shift_neg_out_of_mul(sexpr: SExpr, _: &Env) -> SExpr {
    match sexpr {
        SExpr::Mul(sexprs)
            if sexprs.iter().any(|expr| match expr {
                SExpr::Neg(_) => true,
                _ => false,
            }) =>
        {
            let mut exprs: Vec<SExpr> = vec![];
            let mut positive = true;
            for expr in &sexprs {
                if let SExpr::Neg(x) = expr {
                    positive = !positive;
                    exprs.push(*(*x).clone());
                } else {
                    exprs.push(expr.clone())
                }
            }
            if positive {
                SExpr::Mul(exprs)
            } else {
                SExpr::Neg(Box::new(SExpr::Mul(exprs)))
            }
        }
        _ => sexpr,
    }
}

fn constant_fold(sexpr: SExpr, _env: &Env) -> SExpr {
    match sexpr {
        SExpr::Const(_) => sexpr,
        SExpr::Ident(_) => sexpr,
        SExpr::FnApp(name, sexprs) => SExpr::FnApp(
            name,
            sexprs
                .into_iter()
                .map(|arg| constant_fold(arg, _env))
                .collect(),
        ),
        SExpr::Neg(box SExpr::Const(SVal::Int(x))) => SExpr::Const(SVal::Int(-x)),
        SExpr::Neg(box SExpr::Const(SVal::Real(x))) => SExpr::Const(SVal::Real(-x)),
        SExpr::Neg(_) => sexpr,
        SExpr::Add(ref sexprs) if sexprs.len() >= 2 => match &sexprs[0..2] {
            [SExpr::Const(ref l), SExpr::Const(ref r)] if let Some(res) = l + r => {
                let mut res = vec![SExpr::Const(res)];
                res.extend_from_slice(&sexprs[2..]);
                res.sort();
                SExpr::Add(res)
            }
            _ => sexpr,
        },
        SExpr::Mul(ref sexprs) if sexprs.len() >= 2 => match &sexprs[0..2] {
            [SExpr::Const(ref l), SExpr::Const(ref r)] if let Some(res) = l * r => {
                let mut res = vec![SExpr::Const(res)];
                res.extend_from_slice(&sexprs[2..]);
                res.sort();
                SExpr::Mul(res)
            }
            _ => sexpr,
        },
        _ => sexpr,
    }
}

impl Add for &SVal {
    type Output = Option<SVal>;
    fn add(self, rhs: Self) -> Self::Output {
        match self {
            SVal::Int(l) => match rhs {
                SVal::Int(r) => Some(SVal::Int(l + r)),
                SVal::Real(r) => Some(SVal::Real((*l as f64 + **r).into())),
                SVal::Lambda(_) => None,
            },
            SVal::Real(l) => match rhs {
                SVal::Int(r) => Some(SVal::Real(l + *r as f64)),
                SVal::Real(r) => Some(SVal::Real((*l + *r).into())),
                SVal::Lambda(_) => None,
            },
            SVal::Lambda(_) => None,
        }
    }
}

impl Mul for &SVal {
    type Output = Option<SVal>;
    fn mul(self, rhs: Self) -> Self::Output {
        match self {
            SVal::Int(l) => match rhs {
                SVal::Int(r) => Some(SVal::Int(l * r)),
                SVal::Real(r) => Some(SVal::Real((*l as f64 * **r).into())),
                SVal::Lambda(_) => None,
            },
            SVal::Real(l) => match rhs {
                SVal::Int(r) => Some(SVal::Real(l * *r as f64)),
                SVal::Real(r) => Some(SVal::Real((*l * *r).into())),
                SVal::Lambda(_) => None,
            },
            SVal::Lambda(_) => None,
        }
    }
}
