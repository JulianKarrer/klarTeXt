use std::{
    collections::HashMap,
    f64::{
        consts::{E, PI},
        EPSILON,
    },
    sync::{Arc, LazyLock},
};

use peroxide::fuga::{gamma, phi};

use crate::{
    error::{lambda_arg_err, Error, SpanInfo},
    utils::Either,
    Env, Expr, PredefinedFunction, Typ, Val,
};

/// This wrapper conveniently creates a `Val::Lambda` for defining built-in unary functions
/// - from a name, an error name to be shown in error messages and a function
/// - e.g. `predefined_unary_fn("sin", "sine", |x|{x.sin()})`
fn predefined_unary_fn(
    name: &'static str,
    readable_name: &'static str,
    error_description: Option<&'static str>,
    func: fn(f64) -> f64,
    derivative: Option<&'static (dyn Fn(Expr, SpanInfo) -> DerivRet + Send + Sync)>,
) -> (String, Val) {
    (
        name.to_owned(),
        Val::Lambda(Either::Left(PredefinedFunction {
            closure: Arc::new(move |xs: Vec<Val>, _, span| match xs.as_slice() {
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
            identifier: name.to_owned(),
            derivative: if let Some(deriv) = derivative {
                Some(Arc::new(|args, s| match &args[..] {
                    [arg] => Ok(deriv(*arg.clone(), s)),
                    _ => Err(Error::FnArgCount(name.to_owned(), 1, args.len(), s)),
                }))
            } else {
                None
            },
            param_count: Some(1),
        })),
    )
}

type DerivRet = (Expr, Vec<&'static str>);

pub static PREDEFINED: LazyLock<Env> = LazyLock::new(|| {
    HashMap::from([
        // CONSTANT NUMBERS
        (r"e".to_owned(), Val::Num(E)),
        (r"\pi".to_owned(), Val::Num(PI)),
        // TRIGONOMETRIC
        // regular
        predefined_unary_fn(r"\sin", "sine", None, |x| x.sin(), {
            fn deriv(arg: Expr, s: SpanInfo) -> DerivRet {
                (
                    Expr::FnApp(r"\cos".to_owned(), vec![Box::new(arg)], s, s),
                    vec![r"\cos"],
                )
            }
            Some(&deriv)
        }),
        predefined_unary_fn(r"\cos", "cosine", None, |x| x.cos(), {
            fn deriv(arg: Expr, s: SpanInfo) -> DerivRet {
                (
                    Expr::Neg(
                        Box::new(Expr::FnApp(r"\sin".to_owned(), vec![Box::new(arg)], s, s)),
                        s,
                    ),
                    vec![r"\sin"],
                )
            }
            Some(&deriv)
        }),
        predefined_unary_fn(
            r"\tan",
            "tangent",
            Some("Tangent at (n+1/2)π"),
            |x| x.tan(),
            {
                fn deriv(arg: Expr, s: SpanInfo) -> DerivRet {
                    // 1/(cos(x)^2)
                    (
                        Expr::Div(
                            Box::new(Expr::Const(Val::Num(1.), s)),
                            Box::new(Expr::Pow(
                                Box::new(Expr::FnApp(
                                    r"\cos".to_owned(),
                                    vec![Box::new(arg)],
                                    s,
                                    s,
                                )),
                                Box::new(Expr::Const(Val::Num(2.), s)),
                                s,
                            )),
                            s,
                        ),
                        vec![r"\cos"],
                    )
                }
                Some(&deriv)
            },
        ),
        // inverse
        predefined_unary_fn(
            r"\arcsin",
            "arcsine",
            Some("Arcsine outside of [-1;1]"),
            |x| x.asin(),
            {
                fn deriv(arg: Expr, s: SpanInfo) -> DerivRet {
                    // 1/sqrt(1-x^2)
                    (
                        Expr::Div(
                            Box::new(Expr::Const(Val::Num(1.), s)),
                            Box::new(Expr::Sqrt(
                                Box::new(Expr::Sub(
                                    Box::new(Expr::Const(Val::Num(1.), s)),
                                    Box::new(Expr::Pow(
                                        Box::new(arg),
                                        Box::new(Expr::Const(Val::Num(2.), s)),
                                        s,
                                    )),
                                    s,
                                )),
                                s,
                            )),
                            s,
                        ),
                        vec![],
                    )
                }
                Some(&deriv)
            },
        ),
        predefined_unary_fn(
            r"\arccos",
            "arccosine",
            Some("Arccosine outside of [-1;1]"),
            |x| x.acos(),
            {
                fn deriv(arg: Expr, s: SpanInfo) -> DerivRet {
                    // -( 1/sqrt(1-x^2) )
                    (
                        Expr::Neg(
                            Box::new(Expr::Div(
                                Box::new(Expr::Const(Val::Num(1.), s)),
                                Box::new(Expr::Sqrt(
                                    Box::new(Expr::Sub(
                                        Box::new(Expr::Const(Val::Num(1.), s)),
                                        Box::new(Expr::Pow(
                                            Box::new(arg),
                                            Box::new(Expr::Const(Val::Num(2.), s)),
                                            s,
                                        )),
                                        s,
                                    )),
                                    s,
                                )),
                                s,
                            )),
                            s,
                        ),
                        vec![],
                    )
                }
                Some(&deriv)
            },
        ),
        predefined_unary_fn(r"\arctan", "arctangent", None, |x| x.atan(), {
            fn deriv(arg: Expr, s: SpanInfo) -> DerivRet {
                // 1/(x^2+1)
                (
                    Expr::Div(
                        Box::new(Expr::Const(Val::Num(1.), s)),
                        Box::new(Expr::Add(
                            Box::new(Expr::Const(Val::Num(1.), s)),
                            Box::new(Expr::Pow(
                                Box::new(arg),
                                Box::new(Expr::Const(Val::Num(2.), s)),
                                s,
                            )),
                            s,
                        )),
                        s,
                    ),
                    vec![],
                )
            }
            Some(&deriv)
        }),
        // hyperbolic
        predefined_unary_fn(r"\sinh", "hyperbolic sine", None, |x| x.cosh(), {
            fn deriv(arg: Expr, s: SpanInfo) -> DerivRet {
                (
                    Expr::FnApp(r"\cosh".to_owned(), vec![Box::new(arg)], s, s),
                    vec![r"\cosh"],
                )
            }
            Some(&deriv)
        }),
        predefined_unary_fn(r"\cosh", "hyperbolic cosine", None, |x| x.cosh(), {
            fn deriv(arg: Expr, s: SpanInfo) -> DerivRet {
                (
                    Expr::FnApp(r"\sinh".to_owned(), vec![Box::new(arg)], s, s),
                    vec![r"\sinh"],
                )
            }
            Some(&deriv)
        }),
        predefined_unary_fn(r"\tanh", "hyperbolic tangent", None, |x| x.tanh(), {
            fn deriv(arg: Expr, s: SpanInfo) -> DerivRet {
                // 1/(cosh(x)^2)
                (
                    Expr::Div(
                        Box::new(Expr::Const(Val::Num(1.), s)),
                        Box::new(Expr::Pow(
                            Box::new(Expr::FnApp(r"\cosh".to_owned(), vec![Box::new(arg)], s, s)),
                            Box::new(Expr::Const(Val::Num(2.), s)),
                            s,
                        )),
                        s,
                    ),
                    vec![r"\cosh"],
                )
            }
            Some(&deriv)
        }),
        // EXPONENTIAL
        predefined_unary_fn(
            r"\ln",
            "natural logarithm",
            Some("Negative Logarithm"),
            |x| x.ln(),
            {
                fn deriv(arg: Expr, s: SpanInfo) -> DerivRet {
                    // 1/x
                    (
                        Expr::Div(Box::new(Expr::Const(Val::Num(1.), s)), Box::new(arg), s),
                        vec![],
                    )
                }
                Some(&deriv)
            },
        ),
        predefined_unary_fn(
            r"\log",
            "base-10 logarithm",
            Some("Negative Logarithm"),
            |x| x.log10(),
            {
                fn deriv(arg: Expr, s: SpanInfo) -> DerivRet {
                    // 1/(x * ln(10))
                    // ln(10) is a constant and could be inlined here
                    (
                        Expr::Div(
                            Box::new(Expr::Const(Val::Num(1.), s)),
                            Box::new(Expr::Mul(
                                Box::new(arg),
                                Box::new(Expr::FnApp(
                                    r"\ln".to_owned(),
                                    vec![Box::new(Expr::Const(Val::Num(10.), s))],
                                    s,
                                    s,
                                )),
                                s,
                            )),
                            s,
                        ),
                        vec![r"\ln"],
                    )
                }
                Some(&deriv)
            },
        ),
        predefined_unary_fn(
            r"\lg",
            "base-10 logarithm",
            Some("Negative Logarithm"),
            |x| x.log10(),
            {
                // exact same as \lg above
                fn deriv(arg: Expr, s: SpanInfo) -> DerivRet {
                    // 1/(x * ln(10))
                    // ln(10) is a constant and could be inlined here
                    (
                        Expr::Div(
                            Box::new(Expr::Const(Val::Num(1.), s)),
                            Box::new(Expr::Mul(
                                Box::new(arg),
                                Box::new(Expr::FnApp(
                                    r"\ln".to_owned(),
                                    vec![Box::new(Expr::Const(Val::Num(10.), s))],
                                    s,
                                    s,
                                )),
                                s,
                            )),
                            s,
                        ),
                        vec![r"\ln"],
                    )
                }
                Some(&deriv)
            },
        ),
        predefined_unary_fn(r"\exp", "exponential function", None, |x| x.exp(), {
            fn deriv(arg: Expr, s: SpanInfo) -> DerivRet {
                // e^x
                (
                    Expr::FnApp(r"\exp".to_owned(), vec![Box::new(arg)], s, s),
                    vec![r"\exp"],
                )
            }
            Some(&deriv)
        }),
        predefined_unary_fn(
            r"\Theta",
            "Heaviside theta function",
            None,
            |x| {
                if x.abs() < f64::EPSILON {
                    0.5
                } else {
                    if x.is_sign_negative() {
                        0.
                    } else {
                        1.
                    }
                }
            },
            None,
        ),
        // SPECIAL
        predefined_unary_fn(
            r"\Gamma",
            "gamma function",
            Some("Gamma Function Undefined (Negative Integer or Zero?)"),
            |x| gamma(x),
            None,
        ),
        predefined_unary_fn(
            r"\Psi",
            "digamma function",
            Some("Digamma Function Undefined"),
            |x| digamma(x),
            None,
        ),
        predefined_unary_fn(
            r"\Phi",
            "CDF of the standard normal distribution",
            None,
            |x| phi(x),
            None,
        ),
        // MIN / MAX
        (
            r"\min".to_owned(),
            Val::Lambda(Either::Left(PredefinedFunction {
                closure: Arc::new(move |xs: Vec<Val>, _, span| {
                    let mut res = f64::INFINITY;
                    for arg in &xs {
                        match arg {
                            Val::Num(x) => {
                                res = res.min(*x);
                            }
                            Val::Lambda(_) => {
                                return Err(lambda_arg_err(
                                    "minimum",
                                    span,
                                    &xs,
                                    Either::Right(Typ::Num),
                                ))
                            }
                        };
                    }
                    Ok(Val::Num(res))
                }),
                identifier: r"\min".to_owned(),
                derivative: None,
                param_count: None,
            })),
        ),
        (
            r"\max".to_owned(),
            Val::Lambda(Either::Left(PredefinedFunction {
                closure: Arc::new(move |xs: Vec<Val>, _, span| {
                    let mut res = f64::NEG_INFINITY;
                    for arg in &xs {
                        match arg {
                            Val::Num(x) => {
                                res = res.max(*x);
                            }
                            Val::Lambda(_) => {
                                return Err(lambda_arg_err(
                                    "maximum",
                                    span,
                                    &xs,
                                    Either::Right(Typ::Num),
                                ))
                            }
                        };
                    }
                    Ok(Val::Num(res))
                }),
                identifier: r"\max".to_owned(),
                derivative: None,
                param_count: None,
            })),
        ),
    ])
});

/// https://docs.rs/statrs/latest/x86_64-pc-windows-msvc/src/statrs/function/gamma.rs.html#373-412
/// Computes the Digamma function which is defined as the derivative of
/// the log of the gamma function. The implementation is based on
/// "Algorithm AS 103", Jose Bernardo, Applied Statistics, Volume 25, Number 3
/// 1976, pages 315 - 317
pub fn digamma(x: f64) -> f64 {
    let c = 12.0;
    let d1 = -0.57721566490153286;
    let d2 = 1.6449340668482264365;
    let s = 1e-6;
    let s3 = 1.0 / 12.0;
    let s4 = 1.0 / 120.0;
    let s5 = 1.0 / 252.0;
    let s6 = 1.0 / 240.0;
    let s7 = 1.0 / 132.0;
    if x == f64::NEG_INFINITY || x.is_nan() {
        return f64::NAN;
    }
    // compare with epsilon instead of ulps_eq! macro
    if x <= 0.0 && (x - x.floor()).abs() < EPSILON {
        return f64::NEG_INFINITY;
    }
    if x < 0.0 {
        return digamma(1.0 - x) + PI / (-PI * x).tan();
    }
    if x <= s {
        return d1 - 1.0 / x + d2 * x;
    }
    let mut result = 0.0;
    let mut z = x;
    while z < c {
        result -= 1.0 / z;
        z += 1.0;
    }
    if z >= c {
        let mut r = 1.0 / z;
        result += z.ln() - 0.5 * r;
        r *= r;
        result -= r * (s3 - r * (s4 - r * (s5 - r * (s6 - r * s7))));
    }
    result
}
