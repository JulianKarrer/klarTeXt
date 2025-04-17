#![feature(box_patterns)]
#![feature(if_let_guard)]

use differentiate::{apply_derivatives, ddx};
use disambiguate_fnapp::disambiguate;
use error::{handle_errs, span_merge, Error, SpanInfo, Warning, WARNINGS};
use io::{delete_matching_files, get_file_name, write_to_sibling_file};
use itertools::Itertools;
use parse::parse_main;
use peroxide::fuga::{gamma, integrate};
use predefined::PREDEFINED;
use resolve_def::resolve_const_definitions;
use simplify::simplify;
use utils::Either;

use std::{
    collections::{HashMap, HashSet},
    f64::{self, INFINITY, NEG_INFINITY},
    fmt::{Debug, Display},
    fs,
    ops::RangeInclusive,
    sync::Arc,
};
mod differentiate;
mod disambiguate_fnapp;
mod error;
mod io;
mod parse;
mod predefined;
mod resolve_def;
mod simplify;
mod utils;

type Program = Vec<Stmt>;
type Env = HashMap<String, Val>;

#[derive(Debug)]
enum Stmt {
    Definition(String, Expr, SpanInfo),
    Print(Expr, i64),
    Simplify(Expr, i64),
}

#[derive(Debug, Clone)]
/// An expression.
///
/// This is the main AST object of the implementation that results from parsing
/// and evaluates to a [`Val`] during interpretation.
enum Expr {
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
    /// - an expression to differenciate
    Ddx(String, Box<Expr>, SpanInfo),
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

#[derive(Clone)]
struct PredefinedFunction {
    closure: Arc<dyn Fn(Vec<Val>, &Env, SpanInfo) -> Result<Val, Error> + Send + Sync>,
    identifier: String,
    /// `param_count` is None if any number of arguments is taken
    param_count: Option<usize>,
    derivative: Option<
        Arc<dyn Fn(Vec<Expr>, SpanInfo) -> Result<(Expr, Vec<&'static str>), Error> + Send + Sync>,
    >,
}
impl Display for PredefinedFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, r"{}", self.identifier)
    }
}

#[derive(Clone)]
/// The value that an expression evaluates to.
enum Val {
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

#[derive(Clone, Copy, Debug, Default)]
/// create infinite x_i variable names
struct Vars {
    counter: usize,
}
impl Iterator for Vars {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        self.counter += 1;
        Some(format!(r"x_{{ {} }}", self.counter))
    }
}

enum Typ {
    Num,
    Lam,
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

/// Multiplication that defines zero to be the absorbing element even if the respective other argument is undefined. This allows expressions like `0 + \frac{5}{0}` to evaluate to `0`.
fn custom_mul(lhs: &Expr, rhs: &Expr, env: &Env, fo: &HashSet<String>) -> Result<f64, Error> {
    let lhs_res = eval_num(lhs, env, None, fo);
    let rhs_res = eval_num(rhs, env, None, fo);
    // if any of the two arguments is close enough to zero, return it
    // therefore, the other value may be undefined!
    if let Ok(vl) = lhs_res {
        if vl.abs() < std::f64::EPSILON {
            return Ok(0.);
        }
    }
    if let Ok(vr) = rhs_res {
        if vr.abs() < std::f64::EPSILON {
            return Ok(0.);
        }
    }
    // otherwise, perform the multiplication
    Ok(lhs_res? * rhs_res?)
}

fn factorial(val: f64) -> Option<f64> {
    let val_int = val.round() as i64;
    if val < 0. || (val - val_int as f64).abs() > std::f64::EPSILON {
        let res = gamma(val);
        if res.is_nan() {
            None
        } else {
            Some(res)
        }
    } else {
        // 170! is the maximum representable factorial in f64
        // -> precalculate everything
        const FACTORIALS: [f64; 172] = {
            let mut facts: [f64; 172] = [1.; 172];
            let mut i: usize = 1;
            while i < 172 {
                facts[i] = facts[i - 1] * i as f64;
                i += 1
            }
            // 171! and onwards is note f64-representable
            facts
        };
        Some(FACTORIALS[val_int.min(171) as usize])
    }
}

/// A version of [`eval_expr`] that guarantees the returned value to be a f64 number or an error.
/// An error to throw instead of the generic type error can be supplied.
fn eval_num(
    expr: &Expr,
    env: &Env,
    err: Option<Error>,
    fo: &HashSet<String>,
) -> Result<f64, Error> {
    let span = expr.span();
    let res = eval_expr(expr, env, fo)?;
    match res {
        Val::Num(x) => Ok(x),
        Val::Lambda(_) => {
            if let Some(err) = err {
                Err(err)
            } else {
                Err(Error::TypeError(Typ::Num.name(), Typ::Lam.name(), span))
            }
        }
    }
}

/// Look up a value in the current environment, including predefined values like e and π or
/// predefined function values like \min, \cos, ...
fn lookup_env(name: &String, env: &Env, span: SpanInfo) -> Result<Val, Error> {
    // look for user-defined constants first
    if let Some(cnst) = env.get(name) {
        Ok(cnst.clone())
    } else {
        // otherwise look for predefined constants
        if let Some(cnst) = PREDEFINED.get(name) {
            Ok(cnst.clone())
        } else {
            // if both are not present, throw an error
            Err(Error::DefMissing(span, name.clone()))
        }
    }
}

/// Evaluate an expression using an environment of names and the values bound to them.
/// This function pretty much defines the semantics of expressions in the language.
///
/// Might result in math errors and missing definition errors.
fn eval_expr(expr: &Expr, env: &Env, fo: &HashSet<String>) -> Result<Val, Error> {
    let span = expr.span();
    match expr {
        Expr::Ident(name, _) => lookup_env(name, env, span),
        Expr::FnApp(func_name, args, _, _) => {
            // check if the function name is in the environment
            // if so, get the corresponding value
            let func_val = lookup_env(func_name, env, span)?;
            match &func_val {
                Val::Num(_) => Err(Error::TypeError(Typ::Lam.name(), Typ::Num.name(), span)),
                // otherwise, there is a function value to work with
                Val::Lambda(func) => {
                    // evaluate the arguments
                    let arg_vals = args
                        .iter()
                        .map(|arg| eval_expr(arg, env, fo))
                        .collect::<Result<Vec<Val>, Error>>()?;

                    // if the number of arguments doesn't match the parameters, throw an error
                    match func {
                        Either::Left(predef) => {
                            if let Some(count) = predef.param_count {
                                if count != arg_vals.len() {
                                    return Err(Error::FnArgCount(
                                        format!("{}", func_val),
                                        count,
                                        arg_vals.len(),
                                        span,
                                    ));
                                }
                            }
                        }
                        Either::Right((params, _)) => {
                            if arg_vals.len() != params.len() {
                                return Err(Error::FnArgCount(
                                    format!("{}", func_val),
                                    params.len(),
                                    arg_vals.len(),
                                    span,
                                ));
                            }
                        }
                    }

                    match func {
                        Either::Left(predefined) => (predefined.closure)(arg_vals, env, span),
                        Either::Right((params, body)) => {
                            // there is a user-defined function
                            // add arguments to the environment and then evaluate the body
                            let mut env_inner = env.clone();
                            for (param, arg) in params.iter().zip(arg_vals) {
                                env_inner.insert(param.to_owned(), arg);
                            }
                            eval_expr(&body, &env_inner, fo)
                        }
                    }
                }
            }
        }
        Expr::Const(val, _) => match val {
            Val::Num(x) => Ok(Val::Num(*x)),
            Val::Lambda(_) => Ok(val.clone()),
        },
        Expr::Neg(x, _) => Ok(Val::Num(-eval_num(x, env, None, fo)?)),
        Expr::Fac(x, span) => {
            let val = eval_num(x, env, None, fo)?;
            if (val.floor() - val).abs() > f64::EPSILON {
                WARNINGS
                    .lock()
                    .unwrap()
                    .push(Warning::FactorialIsGamma(format!("{}", val), *span));
            }
            if let Some(res) = factorial(val) {
                Ok(Val::Num(res))
            } else {
                Err(Error::GammaUndefined(*span))
            }
        }
        Expr::Add(lhs, rhs, _) => Ok(Val::Num(
            eval_num(lhs, env, None, fo)? + eval_num(rhs, env, None, fo)?,
        )),
        Expr::Sub(lhs, rhs, _) => Ok(Val::Num(
            eval_num(lhs, env, None, fo)? - eval_num(rhs, env, None, fo)?,
        )),
        Expr::IMul(lhs, rhs, _) => {
            // check if two numbers are implicitly multiplied
            match **rhs {
                Expr::Const(Val::Num(_), _) => match **lhs {
                    Expr::Const(Val::Num(_), _) => {
                        return Err(Error::ImpMulNumNum(lhs.span(), rhs.span()))
                    }
                    _ => return Err(Error::ImpMulRhsNum(lhs.span(), rhs.span())),
                },
                _ => {}
            };
            // otherwise perform the multiplication
            Ok(Val::Num(custom_mul(lhs, rhs, env, fo)?))
        }
        Expr::Mul(lhs, rhs, _) => Ok(Val::Num(custom_mul(lhs, rhs, env, fo)?)),
        Expr::Div(lhs, rhs, _) => {
            let lhs = eval_num(lhs, env, None, fo)?;
            let rhs = eval_num(rhs, env, None, fo)?;
            let res = lhs / rhs;
            if !res.is_nan() {
                Ok(Val::Num(res))
            } else {
                if rhs == f64::INFINITY {
                    Err(Error::MathError(
                        "Divide by Infinity".to_owned(),
                        "division".to_owned(),
                        span,
                    ))
                } else {
                    Err(Error::DivByZero(span))
                }
            }
        }
        Expr::Pow(lhs, rhs, _) => {
            let res = eval_num(lhs, env, None, fo)?.powf(eval_num(rhs, env, None, fo)?);
            if !res.is_nan() {
                Ok(Val::Num(res))
            } else {
                Err(Error::ComplexNumber(span_merge(lhs.span(), rhs.span())))
            }
        }
        Expr::Sqrt(expr, _) => {
            let res = eval_num(expr, env, None, fo)?.sqrt();
            if !res.is_nan() {
                Ok(Val::Num(res))
            } else {
                Err(Error::ComplexNumber(span))
            }
        }
        Expr::Root(degree, radicant, degree_span, radicant_span) => {
            let degree = eval_num(degree, env, None, fo)?;
            if degree.abs() < f64::EPSILON {
                // Check for zero-th root
                Err(Error::ZerothRoot(*degree_span))
            } else {
                let res = eval_num(radicant, env, None, fo)?.powf(1.0 / degree);
                if !res.is_nan() {
                    Ok(Val::Num(res))
                } else {
                    Err(Error::ComplexNumber(*radicant_span))
                }
            }
        }
        Expr::Sum(body, loop_var, range, _) => {
            eval_reduction(body, loop_var, env, range, span, |a, b| a + b, 0., fo)
        }
        Expr::Prod(body, loop_var, range, _) => {
            eval_reduction(body, loop_var, env, range, span, |a, b| a * b, 1., fo)
        }
        Expr::Int(from, to, dx, body, _) => {
            let from = eval_num(from, env, None, fo)?;
            let to = eval_num(to, env, None, fo)?;
            let func = move |x: f64| {
                let mut env_inner = env.clone();
                env_inner.insert(dx.to_owned(), Val::Num(x));
                eval_num(&body, &env_inner, None, fo).unwrap_or(f64::NAN)
            };
            let res = integrate(func, (from, to), peroxide::fuga::Integral::G7K15(1e-4, 20));
            if res.is_nan() {
                Err(Error::IntegralInternalErr(dx.to_owned(), span))
            } else {
                Ok(Val::Num(res))
            }
        }
        Expr::Ddx(x, box expr, _) => eval_expr(&ddx(x, expr.clone(), env, fo)?, env, fo),
    }
}

fn eval_reduction<R: Fn(f64, f64) -> f64>(
    body: &Expr,
    loop_var: &String,
    env: &Env,
    range: &RangeInclusive<i64>,
    span: SpanInfo,
    reduction_op: R,
    neutral_element: f64,
    fo: &HashSet<String>,
) -> Result<Val, Error> {
    let mut res = neutral_element;
    let mut env_inner = env.clone();
    for i in range.clone() {
        // update the loop variable
        env_inner.insert(loop_var.to_owned(), Val::Num(i as f64));
        let update = eval_num(
            body,
            &env_inner,
            Some(Error::ReductionBodyNotNumeric(span)),
            fo,
        )?;
        res = reduction_op(res, update);
    }
    Ok(Val::Num(res))
}

fn snap_to_int(val: f64) -> f64 {
    // if distance to next integer is below the f64 precision limit,
    // round
    if (val.round() - val).abs() < f64::EPSILON {
        // additionally, avoid -0.0
        if val.abs() < f64::EPSILON {
            0.
        } else {
            val.round()
        }
    } else {
        val
    }
}

/// Print debug information to `stdout` while executing the program instead of writing results to output files.
/// Throws the same errors as the regular [`run`] function.
fn debug_run(prog: Program, env: &Env, fo: &HashSet<String>) -> Result<(), Error> {
    // println!("PROGRAM: -----------");
    // println!("{:#?}", prog);
    println!("DEFINITIONS: -----------");
    for (k, v) in env {
        println!("{} = {}", k, v);
    }
    println!("PRINTS: ----------------");
    Ok(for stmt in prog {
        match stmt {
            Stmt::Print(expr, c) => println!("{} >>> {:#?}", c, eval_expr(&expr, &env, fo)?),
            Stmt::Definition(_, _, _) => {}
            Stmt::Simplify(expr, c) => {
                println!("{} >>> {}", c, simplify(&expr, &env, fo).pretty(None))
            }
        }
    })
}

/// Run the program using the specified environment of definitions.
/// - **Deletes** all program output files that are siblings to the source code file
/// - **Writes** the results of IO statements to output files to be included by a corresponding LaTeX package.
fn run(
    prog: Program,
    env: &Env,
    filename: &str,
    err_file_name: &str,
    fo: &HashSet<String>,
) -> Result<(), Error> {
    Ok({
        // execute the program
        for stmt in prog {
            match stmt {
                Stmt::Print(expr, c) => {
                    let res = eval_expr(&expr, &env, fo)?;
                    write_to_sibling_file(
                        filename,
                        &format!("klarTeXt_{}_{}.tex", get_file_name(filename), c),
                        &format!("{}", res),
                    );
                }
                Stmt::Simplify(expr, c) => {
                    let res = simplify(&expr, env, fo);
                    write_to_sibling_file(
                        filename,
                        &format!("klarTeXt_{}_{}.tex", get_file_name(filename), c),
                        &res.pretty(None),
                    );
                }
                _ => {}
            }
        }
        // no error is indicated by an empty error file
        // otherwise this will be written in by `handle_errs`
        write_to_sibling_file(filename, &err_file_name, &"")
    })
}

#[derive(clap::Parser)]
#[command(version, about, long_about = None)] // Read from `Cargo.toml`
/// A derived `clap` parser to parse command line arguments and provide help information and basic CLI capabilities
struct CliParser {
    /// The path to the source code file to interpret
    src: String,
    /// Whether this program was called by a LaTeX process and should write its results to output files or not, in which case it writes to `stdout`.
    ///
    /// Defaults to `false` for use as a CLI
    latex_called: Option<bool>,
}

pub fn main() {
    // Read command line arguments
    let cli = <CliParser as clap::Parser>::parse();
    let filename = cli.src;
    let err_wrn_file_name: Option<(String, String)> = if cli.latex_called.unwrap_or(false) {
        Some((
            format!("klarTeXt_{}_error.txt", get_file_name(&filename)),
            format!("klarTeXt_{}_warning.txt", get_file_name(&filename)),
        ))
    } else {
        None
    };

    // clear previous program output
    delete_matching_files(&filename, &get_file_name(&filename)).unwrap();

    // PASS 0 - PARSING
    let src = fs::read_to_string(&filename).expect("Unable to read input file");
    let p0 = handle_errs(parse_main(&src), &src, &filename, &err_wrn_file_name);

    // PASS 1 - RESOLVING DEFINITIONS
    let (p1, mut env, fo) = handle_errs(
        resolve_const_definitions(p0),
        &src,
        &filename,
        &err_wrn_file_name,
    );
    // println!("{:?}",env);

    // PASS 2 - DISAMBIGUATING FUNCTION APPLICATION AND IMPLICIT MULTIPLICATION
    // e.g. f(x+2) could be read as f*(x+2), if f is a number
    let p2 = handle_errs(disambiguate(p1, &env), &src, &filename, &err_wrn_file_name);

    // println!("--------P2  {:?}",p2);
    // PASS 3 - APPLY PARTIAL DERIVATIVES
    let p3 = handle_errs(
        apply_derivatives(p2, &mut env, &fo),
        &src,
        &filename,
        &err_wrn_file_name,
    );
    // println!("--------P3  {:?}",p3);

    // Run the program by interpreting the AST directly.
    // - `debug_run` writes to `stdout`
    // - `run` writes output files in the directory of the source code file
    if let Some((err_file_name, _)) = &err_wrn_file_name {
        handle_errs(
            run(p3, &env, &filename, err_file_name, &fo),
            &src,
            &filename,
            &err_wrn_file_name,
        );
    } else {
        handle_errs(debug_run(p3, &env, &fo), &src, &filename, &None);
    }

    // test
    // let test_src = r"2x\cdot 1+0+0+0+5\cdot 0";
    // let test = parse_expr(
    //     TexParser::parse(parse::Rule::expr, test_src).unwrap(),
    //     None,
    //     test_src,
    // )
    // .unwrap();
    // let test_str = format!("{}", test);

    // println!(
    //     "TEST SIMPLIFICATION\n{}",
    //     simplify::simplify(&test, &env).pretty(None)
    // );
    // println!(
    //     "TEST DIFFERENTIATION\n{}\n{}",
    //     test_str,
    //     ddx("x", test, &env, &fn_overwritten).unwrap()
    // );
}
