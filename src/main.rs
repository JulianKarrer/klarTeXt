// #[macro_use]
// extern crate peroxide;
// use peroxide::prelude::*;

use error::{handle_errs, span_merge, Error, SpanInfo};
use io::{delete_matching_files, get_file_name, write_to_sibling_file};
use parse::parse_main;
use predefined::PREDEFINED;
use resolve_def::resolve_const_definitions;

use std::{
    collections::{HashMap, HashSet}, f64::{self, INFINITY, NEG_INFINITY}, fmt::{Debug, Display}, fs, ops::RangeInclusive, sync::Arc
};
mod error;
mod io;
mod parse;
mod predefined;
mod resolve_def;
mod utils;

type Program = Vec<Stmt>;
type Env = HashMap<String, Val>;

#[derive(Debug)]
enum Stmt {
    Definition(String, Expr, SpanInfo),
    Print(Expr, i64),
}

#[derive(Debug, Clone)]
enum Expr {
    Val(Val, SpanInfo),
    Ident(String, SpanInfo),

    FnApp(String, Vec<Box<Expr>>, SpanInfo, SpanInfo),

    Sqrt(Box<Expr>, SpanInfo),
    Root(Box<Expr>, Box<Expr>, SpanInfo, SpanInfo),
    Neg(Box<Expr>, SpanInfo),
    Fac(Box<Expr>, SpanInfo),

    Add(Box<Expr>, Box<Expr>, SpanInfo),
    Sub(Box<Expr>, Box<Expr>, SpanInfo),
    Mul(Box<Expr>, Box<Expr>, SpanInfo),
    IMul(Box<Expr>, Box<Expr>, SpanInfo),
    Div(Box<Expr>, Box<Expr>, SpanInfo),
    Pow(Box<Expr>, Box<Expr>, SpanInfo),

    Sum(RangeInclusive<i64>, Val, SpanInfo),
    Prod(RangeInclusive<i64>, Val, SpanInfo),
}

#[derive(Clone)]
pub enum Val {
    /// numeric value represented as `f64`
    Num(f64),
    /// Lambda containing:
    /// - the function name
    /// - the set of identifiers it depends on
    /// - parameter names (empty vector if it is a predefined function)
    /// - the actual function as a closure
    /// A negative argument count allows any number of arguments
    Lambda(
        String,
        HashSet<String>,
        Vec<String>,
        Arc<dyn Fn(Vec<Val>, &Env, SpanInfo) -> Result<Val, Error> + Send + Sync>,
    ),
}

enum Typ {
    Num,
    Lam,
}
impl Into<Typ> for Val {
    fn into(self) -> Typ {
        match self {
            Val::Num(_) => Typ::Num,
            Val::Lambda(_, _, _, _) => Typ::Lam,
        }
    }
}
impl Into<Typ> for &Val {
    fn into(self) -> Typ {
        match self {
            Val::Num(_) => Typ::Num,
            Val::Lambda(_, _, _, _) => Typ::Lam,
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
            Val::Num(x) => write!(f, "{}", x),
            Val::Lambda(name, _, params, _) => {
                if params.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(f, "{} \\mapsto {}", params.join(", "), name)
                }
            }
        }
    }
}
impl Debug for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

/// Multiplication that defines zero to be the absorbing element even if the respective other argument is undefined. This allows expressions like `0 + \frac{5}{0}` to evaluate to `0`.
fn custom_mul(lhs: &Expr, rhs: &Expr, env: &Env) -> Result<f64, Error> {
    let lhs_res = eval_num(lhs, env);
    let rhs_res = eval_num(rhs, env);
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

/// A version of [`eval_expr`] that guarantees the returned value to be a f64 number or an error.
fn eval_num(expr: &Expr, env: &Env) -> Result<f64, Error> {
    let span = expr.span();
    let res = eval_expr(expr, env)?;
    match res {
        Val::Num(x) => Ok(x),
        Val::Lambda(_, _, _, _) => Err(Error::TypeError(Typ::Num.name(), Typ::Lam.name(), span)),
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
fn eval_expr(expr: &Expr, env: &Env) -> Result<Val, Error> {
    let span = expr.span();
    match expr {
        Expr::Ident(name, _) => lookup_env(name, env, span),
        Expr::FnApp(func_name, args, name_span, _) => {
                            // check if the function name is in the environment
                            // if so, get the corresponding value
                            let func_val = lookup_env(func_name, env, span)?;
        
                            match func_val {
                                // check if this is ACTUALLY an implicit multiplication
                                // - if fn_name is actually a numeric type
                                // - AND there is a single argument
                                // then interpret this as an implicit multiplication
                                Val::Num(x) => match &args[..] {
                                    [arg] => {
                                        return eval_expr(
                                            &Expr::IMul(
                                                Box::new(Expr::Val(Val::Num(x), *name_span)),
                                                arg.clone(),
                                                span,
                                            ),
                                            env,
                                        )
                                    }
                                    _ => Err(Error::TypeError(Typ::Lam.name(), Typ::Num.name(), span)),
                                },
                                // otherwise, there is a function value to work with
                                Val::Lambda(_, _, _, func) => {
                                    // evaluate the arguments
                                    let arg_vals = args
                                        .iter()
                                        .map(|arg| eval_expr(arg, env))
                                        .collect::<Result<Vec<Val>, Error>>()?;
                                    // call the function
                                    func(arg_vals, env, span)
                                }
                            }
                }
        Expr::Val(val, _) => match val {
                    Val::Num(x) => Ok(Val::Num(*x)),
                    Val::Lambda(_, _, _, _) => Ok(val.clone()),
                },
        Expr::Neg(x, _) => Ok(Val::Num(-eval_num(x, env)?)),
        Expr::Fac(x, span) => {
                    let val = eval_num(x, env)?;
                    let val_int = val.round() as u64;
                    if val < 0. {
                        Err(Error::FactorialNeg(*span))
                    } else if (val - val_int as f64).abs() > std::f64::EPSILON {
                        Err(Error::FactorialFloat(*span))
                    } else {
                        Ok(Val::Num((1..=val_int).map(|x| x as f64).product()))
                    }
                }
        Expr::Add(lhs, rhs, _) => Ok(Val::Num(eval_num(lhs, env)? + eval_num(rhs, env)?)),
        Expr::Sub(lhs, rhs, _) => Ok(Val::Num(eval_num(lhs, env)? - eval_num(rhs, env)?)),
        Expr::IMul(lhs, rhs, _) => {
                    // check if two numbers are implicitly multiplied
                    match **rhs {
                        Expr::Val(Val::Num(_), _) => match **lhs {
                            Expr::Val(Val::Num(_), _) => {
                                return Err(Error::ImpMulNumNum(lhs.span(), rhs.span()))
                            }
                            _ => return Err(Error::ImpMulRhsNum(lhs.span(), rhs.span())),
                        },
                        _ => {}
                    };
                    // otherwise perform the multiplication
                    Ok(Val::Num(custom_mul(lhs, rhs, env)?))
                }
        Expr::Mul(lhs, rhs, _) => Ok(Val::Num(custom_mul(lhs, rhs, env)?)),
        Expr::Div(lhs, rhs, _) => {
                    let lhs = eval_num(lhs, env)?;
                    let rhs = eval_num(rhs, env)?;
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
                    let res = eval_num(lhs, env)?.powf(eval_num(rhs, env)?);
                    if !res.is_nan() {
                        Ok(Val::Num(res))
                    } else {
                        Err(Error::ComplexNumber(span_merge(lhs.span(), rhs.span())))
                    }
                }
        Expr::Sqrt(expr, _) => {
                    let res = eval_num(expr, env)?.sqrt();
                    if !res.is_nan() {
                        Ok(Val::Num(res))
                    } else {
                        Err(Error::ComplexNumber(span))
                    }
                }
        Expr::Root(degree, radicant, degree_span, radicant_span) => {
                    let degree = eval_num(degree, env)?;
                    if degree.abs() < f64::EPSILON {
                        // Check for zero-th root
                        Err(Error::ZerothRoot(*degree_span))
                    } else {
                        let res = eval_num(radicant, env)?.powf(1.0 / degree);
                        if !res.is_nan() {
                            Ok(Val::Num(res))
                        } else {
                            Err(Error::ComplexNumber(*radicant_span))
                        }
                    }
                },
        Expr::Sum(range, val, _) => {
            eval_reduction(env, range, val, span, |a,b|{a+b}, 0.)
        },
        Expr::Prod(range, val, _) => {
            eval_reduction(env, range, val, span, |a,b|{a*b}, 1.)
        },
    }
}

fn eval_reduction<R: Fn(f64, f64)->f64>(env:&Env, range:&RangeInclusive<i64>, val:&Val, span:SpanInfo, reduction_op:R, neutral_element:f64)->Result<Val, Error>{
    match val{
        Val::Num(_) => unreachable!(),
        Val::Lambda(_, _, _, func) => {
            let mut res = neutral_element;
            for i in range.clone(){
                let ith_val = func(vec![Val::Num(i as f64)], env, span)?;
                match ith_val{
                    Val::Num(ith_f64) => {res = reduction_op(res, ith_f64)},
                    _ => return Err(Error::SumBodyNotNumeric(span)),
                }
            }
            Ok(Val::Num(res))
        },
    }
}

/// Print debug information to `stdout` while executing the program instead of writing results to output files.
/// Throws the same errors as the regular [`run`] function.
fn debug_run(prog: Program, env: Env) -> Result<(), Error> {
    println!("PROGRAM: -----------");
    println!("{:#?}", prog);
    println!("DEFINITIONS: -----------");
    for (k, v) in &env {
        println!("{} = {}", k, v);
    }
    println!("PRINTS: ----------------");
    Ok(for stmt in prog {
        match stmt {
            Stmt::Print(expr, c) => println!("{} >>> {:#?}", c, eval_expr(&expr, &env)?),
            _ => {}
        }
    })
}

/// Run the program using the specified environment of definitions.
/// - **Deletes** all program output files that are siblings to the source code file
/// - **Writes** the results of IO statements to output files to be included by a corresponding LaTeX package.
fn run(prog: Program, env: Env, filename: &str, err_file_name: &str) -> Result<(), Error> {
    Ok({
        // execute the program
        for stmt in prog {
            match stmt {
                Stmt::Print(expr, c) => {
                    let res = eval_expr(&expr, &env)?;
                    write_to_sibling_file(
                        filename,
                        &format!("klarTeXt_{}_{}.tex", get_file_name(filename), c),
                        &format!("{}", res),
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
    let (p1, env) = handle_errs(
        resolve_const_definitions(p0),
        &src,
        &filename,
        &err_wrn_file_name,
    );

    // Run the program by interpreting the AST directly.
    // - `debug_run` writes to `stdout`
    // - `run` writes output files in the directory of the source code file
    if let Some((err_file_name, _)) = &err_wrn_file_name {
        handle_errs(
            run(p1, env, &filename, err_file_name),
            &src,
            &filename,
            &err_wrn_file_name,
        );
    } else {
        handle_errs(debug_run(p1, env), &src, &filename, &None);
    }
}
