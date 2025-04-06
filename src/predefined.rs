use std::{
    collections::{HashMap, HashSet},
    f64::consts::{E, PI},
    sync::{Arc, LazyLock},
};

use peroxide::fuga::{gamma, phi};

use crate::{
    error::{lambda_arg_err, Error},
    utils::Either,
    Env, Typ, Val,
};

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
                    Either::Left(vec![Typ::Num]),
                )),
            }),
        ),
    )
}

pub static PREDEFINED: LazyLock<Env> = LazyLock::new(|| {
    HashMap::from([
        // CONSTANT NUMBERS
        (r"e".to_owned(), Val::Num(E)),
        (r"\pi".to_owned(), Val::Num(PI)),
        // TRIGONOMETRIC
        // regular
        predefined_unary_fn(r"\sin", "sine", None, |x| x.sin()),
        predefined_unary_fn(r"\cos", "cosine", None, |x| x.cos()),
        predefined_unary_fn(r"\tan", "tangent", Some("Tangent at (n+1/2)π"), |x| {
            x.tan()
        }),
        // inverse
        predefined_unary_fn(
            r"\arcsin",
            "arcsine",
            Some("Arcsine outside of [-1;1]"),
            |x| x.asin(),
        ),
        predefined_unary_fn(
            r"\arccos",
            "arccosine",
            Some("Arccosine outside of [-1;1]"),
            |x| x.acos(),
        ),
        predefined_unary_fn(r"\arctan", "arctangent", None, |x| x.atan()),
        // hyperbolic
        predefined_unary_fn(r"\sinh", "hyperbolic sine", None, |x| x.cosh()),
        predefined_unary_fn(r"\cosh", "hyperbolic cosine", None, |x| x.cosh()),
        predefined_unary_fn(r"\tanh", "hyperbolic tangent", None, |x| x.tanh()),
        // EXPONENTIAL
        predefined_unary_fn(
            r"\ln",
            "natural logarithm",
            Some("Negative Logarithm"),
            |x| x.ln(),
        ),
        predefined_unary_fn(
            r"\log",
            "base-10 logarithm",
            Some("Negative Logarithm"),
            |x| x.log10(),
        ),
        predefined_unary_fn(
            r"\lg",
            "base-10 logarithm",
            Some("Negative Logarithm"),
            |x| x.log10(),
        ),
        predefined_unary_fn(r"\exp", "exponential function", None, |x| x.exp()),
        predefined_unary_fn(r"\Theta", "Heaviside theta function", None, |x| {
            if x.abs() < f64::EPSILON {
                0.5
            } else {
                if x.is_sign_negative() {
                    0.
                } else {
                    1.
                }
            }
        }),
        // SPECIAL
        predefined_unary_fn(r"\Gamma", "approximate gamma function", None, |x| gamma(x)),
        predefined_unary_fn(
            r"\Phi",
            "CDF of the standard normal distribution",
            None,
            |x| phi(x),
        ),
        // MIN / MAX
        (
            r"\min".to_owned(),
            Val::Lambda(
                r"\min".to_owned(),
                HashSet::new(),
                vec![],
                Arc::new(move |args: Vec<Val>, _, span| {
                    let mut res = f64::INFINITY;
                    for arg in &args {
                        match arg {
                            Val::Num(x) => {
                                res = res.min(*x);
                            }
                            Val::Lambda(_, _, _, _) => {
                                return Err(lambda_arg_err(
                                    "minimum",
                                    span,
                                    &args,
                                    Either::Right(Typ::Num),
                                ))
                            }
                        };
                    }
                    Ok(Val::Num(res))
                }),
            ),
        ),
        (
            r"\max".to_owned(),
            Val::Lambda(
                r"\max".to_owned(),
                HashSet::new(),
                vec![],
                Arc::new(move |args: Vec<Val>, _, span| {
                    let mut res = f64::NEG_INFINITY;
                    for arg in &args {
                        match arg {
                            Val::Num(x) => {
                                res = res.max(*x);
                            }
                            Val::Lambda(_, _, _, _) => {
                                return Err(lambda_arg_err(
                                    "maximum",
                                    span,
                                    &args,
                                    Either::Right(Typ::Num),
                                ))
                            }
                        };
                    }
                    Ok(Val::Num(res))
                }),
            ),
        ),
    ])
});
