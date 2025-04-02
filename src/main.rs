use error::{handle_errs, span_merge, Error, SpanInfo};
use io::{delete_matching_files, get_file_name, to_sibling_file};
use lazy_static::lazy_static;
use parse::parse_main;
use resolve_def::resolve_const_definitions;

use std::{
    collections::HashMap,
    f64::consts::{E, PI},
    fs,
};
mod error;
mod io;
mod parse;
mod resolve_def;

type Program = Vec<Stmt>;
type Program1 = (Program, HashMap<String, f64>);

#[derive(Debug)]
enum Stmt {
    Definition(String, Expr),
    Print(Expr, i64),
}

#[derive(Debug)]
enum Expr {
    Num(f64, SpanInfo),
    Ident(String, SpanInfo),

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
}

lazy_static! {
    static ref PREDEFINED_CONSTANTS: HashMap<String, f64> =
        HashMap::from([(r"e".to_owned(), E), (r"\pi".to_owned(), PI),]);
}

/// Multiplication that defines zero to be the absorbing element even if the respective other argument is undefined. This allows expressions like `0 + \frac{5}{0}` to evaluate to `0`.
fn custom_mul(lhs: &Expr, rhs: &Expr, env: &HashMap<String, f64>) -> Result<f64, Error> {
    let lhs = eval_expr(lhs, env);
    let rhs = eval_expr(rhs, env);
    // if any of the two arguments is close enough to zero, return it
    if let Ok(vl) = lhs {
        if vl.abs() < std::f64::EPSILON {
            return Ok(vl);
        }
    }
    if let Ok(vr) = rhs {
        if vr.abs() < std::f64::EPSILON {
            return Ok(vr);
        }
    }
    // otherwise, perform the multiplication
    Ok(lhs? * rhs?)
}

/// Evaluate an expression using an environment of names and the values bound to them. 
/// This function pretty much defines the semantics of expressions in the language.
/// 
/// Might result in math errors. 
fn eval_expr(expr: &Expr, env: &HashMap<String, f64>) -> Result<f64, Error> {
    let span = expr.span();
    match expr {
        Expr::Num(x, _) => Ok(*x),
        Expr::Neg(x, _) => Ok(-eval_expr(x, env)?),
        Expr::Fac(x, span) => {
                            let val = eval_expr(x, env)?;
                            let val_int = val.round() as u64;
                            if val < 0. {
                                Err(Error::FactorialNeg(*span))
                            } else if (val - val_int as f64).abs() > std::f64::EPSILON {
                                Err(Error::FactorialFloat(*span))
                            } else {
                                Ok((1..=val_int).map(|x| x as f64).product())
                            }
                }
        Expr::Add(lhs, rhs, _) => Ok(eval_expr(lhs, env)? + eval_expr(rhs, env)?),
        Expr::Sub(lhs, rhs, _) => Ok(eval_expr(lhs, env)? - eval_expr(rhs, env)?),
        Expr::IMul(lhs, rhs, _) => {
                    // check if two numbers are implicitly multiplied
                    match **rhs {
                        Expr::Num(_, _) => match **lhs {
                            Expr::Num(_, _) => return Err(Error::ImpMulNumNum(lhs.span(), rhs.span())),
                            _ => return Err(Error::ImpMulRhsNum(lhs.span(), rhs.span())),
                        },
                        _ => {}
                    };
                    // otherwise perform the multiplication
                    Ok(custom_mul(lhs, rhs, env)?)
                }
        Expr::Mul(lhs, rhs, _) => Ok(custom_mul(lhs, rhs, env)?),
        Expr::Div(lhs, rhs, _) => {
                    let res = eval_expr(lhs, env)? / eval_expr(rhs, env)?;
                    if res.is_finite() {
                        Ok(res)
                    } else {
                        Err(Error::DivByZero(span))
                    }
                }
        Expr::Pow(lhs, rhs, _) => {
                let res = eval_expr(lhs, env)?.powf(eval_expr(rhs, env)?);
                if res.is_finite(){
                    Ok(res)
                } else {
                    Err(Error::ComplexNumber(span_merge(lhs.span(), rhs.span())))
                }
            },
        Expr::Ident(name, _) => {
                    if let Some(cnst) = env.get(name) {
                        // look for user-defined constants
                        Ok(*cnst)
                    } else {
                        if let Some(cnst) = PREDEFINED_CONSTANTS.get(name) {
                            // look for predefined constants
                            Ok(*cnst)
                        } else {
                            Err(Error::DefMissing(span, name.clone()))
                        }
                    }
                }
        Expr::Sqrt(expr, _) => {
                let res = eval_expr(expr, env)?.sqrt();
                if res.is_finite(){
                    Ok(res)
                } else {
                    Err(Error::ComplexNumber(span))
                }
            },
        Expr::Root(degree, radicant, degree_span, radicant_span) => {
            let degree = eval_expr(degree, env)?;
            if degree.abs() < f64::EPSILON{
                // Check for zero-th root
                Err(Error::ZerothRoot(*degree_span))
            } else {
                let res = eval_expr(radicant, env)?.powf(1.0/degree);
                if res.is_finite(){
                    Ok(res)
                } else {
                    Err(Error::ComplexNumber(*radicant_span))
                }
            }
        },
    }
}

/// Print debug information to `stdout` while executing the program instead of writing results to output files.
/// Throws the same errors as the regular [`run`] function.
fn debug_run(prog: Program, env: HashMap<String, f64>) -> Result<(), Error> {
    println!("DEFINITIONS: -----------");
    for (k, v) in &env {
        println!("{} = {}", k, v)
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
fn run(
    prog: Program,
    env: HashMap<String, f64>,
    filename: &str,
    err_file_name: &str,
) -> Result<(), Error> {
    Ok({
        // clear the program output
        delete_matching_files(filename, &get_file_name(filename)).unwrap();
        // execute the program
        for stmt in prog {
            match stmt {
                Stmt::Print(expr, c) => {
                    to_sibling_file(
                        filename,
                        &format!("klarTeXt_{}_{}.tex", get_file_name(filename), c),
                        &format!("{}", eval_expr(&expr, &env)?),
                    );
                }
                _ => {}
            }
        }
        // no error is indicated by an empty error file
        // otherwise this will be written in by `handle_errs`
        to_sibling_file(filename, &err_file_name, &"")
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
    let err_file_name = if cli.latex_called.unwrap_or(false) {
        Some(format!("klarTeXt_{}_error.txt", get_file_name(&filename)))
    } else {
        None
    };

    // PASS 0 - PARSING
    let src = fs::read_to_string(&filename).expect("Unable to read input file");
    let p0 = handle_errs(parse_main(&src), &src, &filename, &err_file_name);

    // PASS 1 - RESOLVING DEFINITIONS
    let (p1, env) = handle_errs(
        resolve_const_definitions(p0),
        &src,
        &filename,
        &err_file_name,
    );

    // Run the program by interpreting the AST directly.
    // - `debug_run` writes to `stdout`
    // - `run` writes output files in the directory of the source code file
    if let Some(err_file_name) = err_file_name {
        handle_errs(
            run(p1, env, &filename, &err_file_name),
            &src,
            &filename,
            &Some(err_file_name),
        );
    } else {
        handle_errs(debug_run(p1, env), &src, &filename, &None);
    }
}
