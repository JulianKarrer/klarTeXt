use either::Either;
use error::{handle_errs, lambda_arg_err, span_merge, Error, SpanInfo};
use io::{delete_matching_files, get_file_name, to_sibling_file};
use lazy_static::lazy_static;
use parse::parse_main;
use resolve_def::resolve_const_definitions;
use strum_macros::EnumDiscriminants;

use std::{
    collections::{HashMap, HashSet},
    f64::{
        self,
        consts::{E, PI},
        INFINITY, NEG_INFINITY,
    },
    fmt::{Debug, Display},
    fs,
    sync::Arc,
};
mod error;
mod io;
mod parse;
mod resolve_def;

type Program = Vec<Stmt>;
type Env = HashMap<String, Val>;

#[derive(Debug)]
enum Stmt {
    Definition(String, Expr),
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
}

#[derive(EnumDiscriminants, Clone)]
enum Val {
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
impl ValDiscriminants {
    pub fn name(&self) -> String {
        match self {
            ValDiscriminants::Num => "number".to_owned(),
            ValDiscriminants::Lambda => "function".to_owned(),
        }
    }
}
impl Display for Val{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self{
            Val::Num(INFINITY) => write!(f, r"\infty"),
            Val::Num(NEG_INFINITY) => write!(f, r"-\infty"),
            Val::Num(x) => write!(f, "{}", x),
            Val::Lambda(name, _, params,  _) => {
                if params.is_empty(){
                    write!(f, "{}", name)
                } else {
                    write!(f, "{} \\mapsto {}", params.join(", "), name)
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

/// This wrapper conveniently creates a `Val::Lambda` for defining built-in unary functions
/// - from a name, an error name to be shown in error messages and a function
/// - e.g. `predefined_unary_fn("sin", "sine", |x|{x.sin()})`
fn predefined_unary_fn(
    name: &'static str,
    readable_name: &'static str,
    error_description: Option<&'static str>,
    func: fn(f64) -> f64,
) -> (String, Val) {
    (
        name.to_owned(),
        Val::Lambda(
            name.to_owned(),
            HashSet::new(),
            vec![],
            Arc::new(move |xs: Vec<Val>, _, span| match xs.as_slice() {
                [Val::Num(x)] => {
                    let res = func(*x);
                    if let Some(err_descr) = error_description {
                        if res.is_nan() {
                            return Err(Error::MathError(
                                err_descr.to_owned(),
                                readable_name.to_owned(),
                                span,
                            ));
                        }
                    }
                    Ok(Val::Num(res))
                }
                _ => Err(lambda_arg_err(
                    readable_name,
                    span,
                    &xs,
                    Either::Left(vec![ValDiscriminants::Num]),
                )),
            }),
        ),
    )
}

lazy_static! {
    static ref PREDEFINED: Env = HashMap::from([
        // CONSTANT NUMBERS
        (r"e".to_owned(), Val::Num(E)),
        (r"\pi".to_owned(), Val::Num(PI)),
        // TRIGONOMETRIC
        // regular
        predefined_unary_fn(r"\sin", "sine", None, |x|{x.sin()}),
        predefined_unary_fn(r"\cos", "cosine", None, |x|{x.cos()}),
        predefined_unary_fn(r"\tan", "tangent", Some("Tangent at (n+1/2)π"),|x|{x.tan()}),
        // inverse
        predefined_unary_fn(r"\arcsin", "arcsine", Some("Arcsine outside of [-1;1]"), |x|{x.asin()}),
        predefined_unary_fn(r"\arccos", "arccosine", Some("Arccosine outside of [-1;1]"), |x|{x.acos()}),
        predefined_unary_fn(r"\arctan", "arctangent", None, |x|{x.atan()}),
        // hyperbolic
        predefined_unary_fn(r"\sinh", "hyperbolic sine", None,|x|{x.cosh()}),
        predefined_unary_fn(r"\cosh", "hyperbolic cosine", None, |x|{x.cosh()}),
        predefined_unary_fn(r"\tanh", "hyperbolic tangent", None,|x|{x.tanh()}),
        // EXPONENTIAL
        predefined_unary_fn(r"\ln", "natural logarithm", Some("Negative Logarithm"),|x|{x.ln()}),
        predefined_unary_fn(r"\log", "base-10 logarithm", Some("Negative Logarithm"),|x|{x.log10()}),
        predefined_unary_fn(r"\lg", "base-10 logarithm", Some("Negative Logarithm"), |x|{x.log10()}),
        predefined_unary_fn(r"\exp", "exponential function", None, |x|{x.exp()}),
        predefined_unary_fn(r"\Theta", "Heaviside theta function", None, |x|{if x.abs()<f64::EPSILON{0.5}else {if x.is_sign_negative() {0.} else {1.}}}),
        // SPECIAL

        // MIN / MAX
        (
            r"\min".to_owned(),
            Val::Lambda(
                r"\min".to_owned(),
                HashSet::new(),
                vec![],
                Arc::new(move |args: Vec<Val>, _, span|{
                    let mut res = f64::INFINITY;
                    for arg in &args{
                        match arg {
                            Val::Num(x) => {res = res.min(*x);},
                            Val::Lambda(_, _, _, _) => {
                                return Err(lambda_arg_err(
                                    "minimum",
                                    span,
                                    &args,
                                    Either::Right(ValDiscriminants::Num)
                                ))
                            },
                        };
                    };
                    Ok(Val::Num(res))
                })
            ),
        ),
        (
            r"\max".to_owned(),
            Val::Lambda(
                r"\max".to_owned(),
                HashSet::new(),
                vec![],
                Arc::new(move |args: Vec<Val>, _, span|{
                    let mut res = f64::NEG_INFINITY;
                    for arg in &args{
                        match arg {
                            Val::Num(x) => {res = res.max(*x);},
                            Val::Lambda(_, _, _, _) => {
                                return Err(lambda_arg_err(
                                    "maximum",
                                    span,
                                    &args,
                                    Either::Right(ValDiscriminants::Num)
                                ))
                            },
                        };
                    };
                    Ok(Val::Num(res))
                })
            ),
        )
    ]);
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
    match res{
        Val::Num(x) => Ok(x),
        Val::Lambda(_, _, _, _) => Err(Error::TypeError(ValDiscriminants::Num.name(), ValDiscriminants::Lambda.name(), span)),
    }
}

/// Look up a value in the current environment, including predefined values like e and π or 
/// predefined function values like \min, \cos, ...
fn lookup_env(name:&String, env: &Env, span:SpanInfo) -> Result<Val, Error> {
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

            match func_val{
                // check if this is ACTUALLY an implicit multiplication
                // - if fn_name is actually a numeric type
                // - AND there is a single argument
                // then interpret this as an implicit multiplication
                Val::Num(x) => {
                    match &args[..]{
                        [arg] => return eval_expr(&Expr::IMul(Box::new(Expr::Val(Val::Num(x), *name_span)), arg.clone(), span), env),
                        _ => {Err(Error::TypeError(ValDiscriminants::Lambda.name(), ValDiscriminants::Num.name(), span))}
                    }
                },
                // otherwise, there is a function value to work with
                Val::Lambda(_, _, _, func) => {
                    // evaluate the arguments
                    let arg_vals = args.iter()
                        .map(|arg|eval_expr(arg, env))
                        .collect::<Result<Vec<Val>, Error>>()?;
                    // call the function
                    func(arg_vals, env, span)
                },
            }
        }
        Expr::Val(val, _) => match val{
            Val::Num(x) => Ok(Val::Num(*x)),
            Val::Lambda(_, _, _, _) => Ok(val.clone()),
        },
        Expr::Neg(x, _) => {
            Ok(Val::Num(-eval_num(x, env)?))
        },
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
                    Expr::Val(Val::Num(_), _) => return Err(Error::ImpMulNumNum(lhs.span(), rhs.span())),
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
        }
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
fn run(
    prog: Program,
    env: Env,
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
                    let res = eval_expr(&expr, &env)?;
                    to_sibling_file(
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
