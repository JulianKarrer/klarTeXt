use std::collections::HashSet;

use crate::{
    error::Error, eval_num, lookup_env, resolve_def::free_in_expr, utils::Either, Env, Expr, Val,
    Vars,
};

pub fn ddx(x: &str, expr: Expr, env: &Env, fo: &HashSet<String>) -> Result<Expr, Error> {
    let s = expr.span();

    // differentiation with respect to a constant is undefined
    if let Some(_) = env.get(x) {
        return Err(Error::DifferentiationError("You attempted to differentiate with respect to a value, not a variable.\nDerivates with respect to constants are undefined.\nDifferentiation with respect to function values is currently unsupproted".to_owned(), s));
    }

    // whenever the expression is closed, it can be evaluated to a number under the
    // current environment.
    // in that case, the parial derivative with respect to any variable x must be zero
    if let Ok(_) = eval_num(&expr, env, None) {
        return Ok(Expr::Const(Val::Num(0.), s));
    }

    // this span does not have much meaning outside of error reporting
    match expr {
        Expr::Const(_c, _) => {
            // d/dx[c] = 0
            Ok(Expr::Const(Val::Num(0.), s))
        }
        Expr::Ident(v, _) => {
            if v == x {
                // if the variable is the dx variable
                // d/dx[x] = 1
                Ok(Expr::Const(Val::Num(1.), s))
            } else {
                match lookup_env(&v, env, s)?{
                    // name is a constant
                    // d/dx[v] = 0
                    Val::Num(_) => Ok(Expr::Const(Val::Num(0.), s)),
                    // name is a function
                    Val::Lambda(_) => Err(Error::DifferentiationError("Differentiating function values directly is currently unsupported.\nMaybe you meant to use function application?\nTry differentiating e.g. `f(x)` instead of `f`".to_owned(), s)),
                }
            }
        }
        Expr::Add(u, v, _) => {
            // d/dx[u + v] = d/dx[u] + d/dx[v]
            Ok(Expr::Add(
                Box::new(ddx(x, *u, env, fo)?),
                Box::new(ddx(x, *v, env, fo)?),
                s,
            ))
        }
        Expr::Sub(u, v, _) => {
            // d/dx[u - v] = d/dx[u] - d/dx[v]
            Ok(Expr::Sub(
                Box::new(ddx(x, *u, env, fo)?),
                Box::new(ddx(x, *v, env, fo)?),
                s,
            ))
        }
        Expr::Neg(v, _) => {
            // d/dx[-v] = - d/dx[v]
            Ok(Expr::Neg(Box::new(ddx(x, *v, env, fo)?), s))
        }
        Expr::Mul(u, v, _) | Expr::IMul(u, v, _) => {
            // d/dx[u * v] = u * d/dx[v] + v * d/dx[u]
            Ok(Expr::Add(
                Box::new(Expr::Mul(
                    u.clone(),
                    Box::new(ddx(x, *v.clone(), env, fo)?),
                    s,
                )),
                Box::new(Expr::Mul(v, Box::new(ddx(x, *u, env, fo)?), s)),
                s,
            ))
        }
        Expr::Div(u, v, _) => {
            // d/dx[u / v] = (v * d/dx[u] - u * d/dx[v]) / v^2
            Ok(Expr::Div(
                Box::new(Expr::Sub(
                    Box::new(Expr::Mul(
                        v.clone(),
                        Box::new(ddx(x, *u.clone(), env, fo)?),
                        s,
                    )),
                    Box::new(Expr::Mul(u, Box::new(ddx(x, (*v).clone(), env, fo)?), s)),
                    s,
                )),
                Box::new(Expr::Pow(v, Box::new(Expr::Const(Val::Num(2.), s)), s)),
                s,
            ))
        }
        Expr::Pow(ref u, ref v, _) => {
            if let Ok(c) = eval_num(&v, env, None) {
                // v=c is a constant
                // d/dx[u^c] = c * u^(c - 1) * d/dx[u]
                Ok(Expr::Mul(
                    Box::new(Expr::Mul(
                        Box::new(Expr::Const(Val::Num(c), s)),
                        Box::new(Expr::Pow(
                            Box::new(*(*u).clone()),
                            Box::new(Expr::Const(Val::Num(c - 1.), s)),
                            s,
                        )),
                        s,
                    )),
                    Box::new(ddx(x, *u.clone(), env, fo)?),
                    s,
                ))
            } else {
                // v is not a constant
                // d/dx[u^v] = u^v * [ (v' * ln(u)) + (v * (u'/u)) ]
                let dudx = ddx(x, *(*u).clone(), env, fo)?;
                let dvdx = ddx(x, *(*v).clone(), env, fo)?;
                Ok(Expr::Mul(
                    Box::new(expr.clone()),
                    Box::new(Expr::Add(
                        Box::new(Expr::Mul(
                            Box::new(dvdx),
                            Box::new(Expr::FnApp(r"\ln".to_owned(), vec![u.clone()], s, s)),
                            s,
                        )),
                        Box::new(Expr::Mul(
                            v.clone(),
                            Box::new(Expr::Div(Box::new(dudx), u.clone(), s)),
                            s,
                        )),
                        s,
                    )),
                    s,
                ))
            }
        }
        Expr::Fac(u, _) => {
            // d/dx[Γ(u+1)] = Γ(u+1) * Ψ(u+1) * d/dx[u]
            // derivative of gamma -> product with digamma, then inner derivative as per chain rule
            let u_plus_one = Box::new(Expr::Add(
                u.clone(),
                Box::new(Expr::Const(Val::Num(1.0), s)),
                s,
            ));
            Ok(Expr::Mul(
                Box::new(ddx(x, *u, env, fo)?),
                Box::new(Expr::Mul(
                    Box::new(Expr::FnApp(
                        r"\Gamma".to_owned(),
                        vec![u_plus_one.clone()],
                        s,
                        s,
                    )),
                    Box::new(Expr::FnApp(r"\Psi".to_owned(), vec![u_plus_one], s, s)),
                    s,
                )),
                s,
            ))
        }
        Expr::FnApp(fn_name, args, _, _) => {
            match lookup_env(&fn_name, env, s)? {
                Val::Num(_) => unreachable!(),
                Val::Lambda(func) => {
                    match func {
                        Either::Left(predefined) => {
                            if predefined.param_count == Some(1) {
                                match &args[..] {
                                    [arg] => {
                                        // univariate chain rule
                                        if let Some(deriv) = predefined.derivative {
                                            let (derivative, depends_on) =
                                                deriv(vec![arg.clone()], s)?;
                                            // if the derivative relies on a overwritten predefined function, throw an error
                                            if depends_on.iter().any(|needed| fo.contains(*needed))
                                            {
                                                return Err(Error::DifferentiationError("Automatic differentiation encountered a predefined function (like `\\sin` etc.) that may have been overwritten.\nPlease don't overwrite ANY predefined functions if you want to use this feature.".to_owned(), s));
                                            }
                                            Ok(Expr::Mul(
                                                Box::new(derivative),
                                                // multiply with inner derivative
                                                Box::new(ddx(x, *arg.clone(), env, fo)?),
                                                s,
                                            ))
                                        } else {
                                            Err(Error::DifferentiationError(r"A unary predefined function with no specified derivative was encountered during differentiation.".to_owned(), s))
                                        }
                                    }
                                    // throw error if the argument count does not match
                                    // -> args can safely be used in the univariate case
                                    _ => {
                                        return Err(Error::FnArgCount(
                                            format!("{}", predefined),
                                            1,
                                            args.len(),
                                            s,
                                        ))
                                    }
                                }
                            } else {
                                Err(Error::DifferentiationError(r"Differentiating multivariate predefined functions is currently unsupported".to_owned(), s))
                            }
                        }
                        Either::Right((params, body)) => {
                            // get the expression that would result from capture-free substituting the
                            // argument expressions -> beta reduce the function body
                            // this uses `substitute` recursively to beta-reduce and alpha-rename
                            // until only the resulting expression remains
                            let expr =
                                params
                                    .iter()
                                    .zip(args)
                                    .try_fold(*body, |acc, (param, arg)| {
                                        substitute(
                                            param,
                                            &*arg,
                                            acc,
                                            env,
                                            &HashSet::from_iter(
                                                env.keys().cloned().chain(params.iter().cloned()),
                                            ),
                                        )
                                    })?;
                            // now, the resulting expression can be differentiated like all others
                            ddx(x, expr, env, fo)
                        }
                    }
                }
            }
        }
        Expr::Sqrt(u, _) => {
            // d/dx[sqrt(u)] = (d/dx[u]) / (2 * sqrt(u))
            Ok(Expr::Div(
                Box::new(ddx(x, *u.clone(), env, fo)?),
                Box::new(Expr::Mul(
                    Box::new(Expr::Const(Val::Num(2.), s)),
                    Box::new(Expr::Sqrt(u, s)),
                    s,
                )),
                s,
            ))
        }
        Expr::Root(ref u, ref v, _, _) => {
            // d/dx[v^(1/u)]    = v^(1/u) * [ ( (1/u)' * ln(v) ) + (1/u * v'/v) ]
            //                  = v^(1/u) * [ ( -(u'/u^2) * ln(v) ) + (1/u * v'/v) ]
            //                  = expr    * [ ( -(u'/u^2) * ln(v) ) + (1/u * v'/v) ]
            //                  = expr    * [ (1/u * v' / v) - ( ln(v) * (u'/u^2)  )  ]
            let dudx = ddx(x, *(*u).clone(), env, fo)?;
            let dvdx = ddx(x, *(*v).clone(), env, fo)?;

            let one_over_u = Box::new(Expr::Div(
                Box::new(Expr::Const(Val::Num(1.), s)),
                Box::new(*u.clone()),
                s,
            ));

            Ok(Expr::Mul(
                Box::new(expr.clone()),
                Box::new(Expr::Sub(
                    Box::new(Expr::Mul(
                        one_over_u,
                        Box::new(Expr::Div(Box::new(dvdx), v.clone(), s)),
                        s,
                    )),
                    Box::new(Expr::Mul(
                        Box::new(Expr::FnApp(r"\ln".to_owned(), vec![v.clone()], s, s)),
                        Box::new(Expr::Div(
                            Box::new(dudx),
                            Box::new(Expr::Pow(
                                u.clone(),
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
            ))
        }
        Expr::Sum(body, loop_var, range_inclusive, _) => {
            Ok(range_inclusive
                // apply ddx to each part of the sum, where i is reified, collect the results
                .map(|i| {
                    let mut env_inner = env.clone();
                    env_inner.insert(loop_var.clone(), Val::Num(i as f64));
                    ddx(x, *body.clone(), &env_inner, fo)
                })
                .collect::<Result<Vec<Expr>, Error>>()?
                // then fold the sum into a long nested addition
                .into_iter()
                .fold(Expr::Const(Val::Num(0.), s), |lhs, rhs| {
                    Expr::Add(Box::new(lhs), Box::new(rhs), s)
                }))
        }
        Expr::Prod(body, loop_var, range_inclusive, _) => {
            let res = range_inclusive
                .map(|i| {
                    // substitute in the respective loop variable
                    substitute(
                        &loop_var,
                        &Expr::Const(Val::Num(i as f64), s),
                        *body.clone(),
                        env,
                        &HashSet::from_iter(
                            env.keys()
                                .cloned()
                                .chain([loop_var.clone()].iter().cloned()),
                        ),
                    )
                })
                .collect::<Result<Vec<Expr>, Error>>()?
                .into_iter()
                // fold the resulting terms into one long product
                .fold(Expr::Const(Val::Num(1.0), s), |acc, cur| {
                    Expr::Mul(Box::new(acc), Box::new(cur), s)
                });
            // now, apply ddx to the term like usual
            ddx(x, res, env, fo)
        }
        Expr::Int(lower, upper, t, body, _) => {
            if t == x {
                // if x is shadowed by the integration variable, the integral is a constant
                // -> derivative is zero
                Ok(Expr::Const(Val::Num(0.), s))
            } else {
                // Leibnitz's integral rule:
                // d/dx[int_{a(x)}^{b(x)} f(t,x) dt] =     <- where t != x, i.e. int_var != x
                //      f(x, t=b(x)) * d/dx[b(x)]     <- substitute upper for t in body, apply chain rule
                //   -  f(x, t=a(x)) * d/dx[a(x)]     <- substitute lower for t in body, apply chain rule
                //   +  int_{a(x)}^{b(x)} d/dx[f(t,x)] dx  <- recurse into body
                let forbidden =
                    HashSet::from_iter(env.keys().cloned().chain([t.clone()].iter().cloned()));

                let dbdx = ddx(x, *upper.clone(), env, fo)?;
                let dadx = ddx(x, *lower.clone(), env, fo)?;

                let f_x_bx = substitute(&t, &upper, *body.clone(), env, &forbidden)?;
                let f_x_ax = substitute(&t, &lower, *body.clone(), env, &forbidden)?;

                let ddx_f_t_x = ddx(x, *body, env, fo)?;

                Ok(Expr::Add(
                    Box::new(Expr::Sub(
                        Box::new(Expr::Mul(Box::new(f_x_bx), Box::new(dbdx), s)),
                        Box::new(Expr::Mul(Box::new(f_x_ax), Box::new(dadx), s)),
                        s,
                    )),
                    Box::new(Expr::Int(lower, upper, t, Box::new(ddx_f_t_x), s)),
                    s,
                ))
            }
        }
    }
}

/// Implements capture-free subsitution or alpha-renaming of the identifier `from` to the expression `to`
fn substitute(
    from: &str,
    to: &Expr,
    expr: Expr,
    env: &Env,
    forbidden: &HashSet<String>,
) -> Result<Expr, Error> {
    let s = expr.span();
    match expr {
        // base case
        Expr::Const(_, _) => Ok(expr),
        // interesting case
        Expr::Ident(ref name, _) => {
            if from == name {
                Ok(to.clone())
            } else {
                Ok(expr)
            }
        }
        // avoid capture!
        Expr::FnApp(fn_name, args, _, _) => {
            match lookup_env(&fn_name, env, s)? {
                Val::Num(_) => unreachable!(),
                Val::Lambda(func) => {
                    // recurse into the argument expressions and rebuild a new list of arguments
                    let new_args = args
                        .into_iter()
                        .map(|arg| substitute(from, to, *arg, env, forbidden))
                        .collect::<Result<Vec<Expr>, Error>>()?
                        .into_iter()
                        .map(|arg| Box::new(arg))
                        .collect();
                    match func {
                        Either::Left(_) => {
                            // predefined functions dont contain identifiers except for other predefined functions
                            // -> only subsitute in the arguments
                            Ok(Expr::FnApp(fn_name, new_args, s, s))
                        }
                        Either::Right((params, body)) => {
                            // look at the free parameters in the substituted expression
                            let free = free_in_expr(to);
                            let mut new_body = *body.clone();
                            let mut new_params = Vec::with_capacity(params.len());
                            let mut new_forbidden = forbidden.clone();
                            new_forbidden.extend(free.iter().cloned());
                            for arg in &new_args {
                                new_forbidden.extend(free_in_expr(&*arg).iter().cloned());
                            }

                            // if any of the parameters of the function are free in the substiuted expression, replace them first
                            for param in &params {
                                new_params.push(if free.contains(param) {
                                    // parameter is free in `from`, replace with new one and extend forbidden list
                                    let new_param = new_var(&new_forbidden);
                                    new_forbidden.insert(new_param.to_owned());
                                    // substitute in the body
                                    new_body = substitute(
                                        param,
                                        &Expr::Ident(new_param.to_owned(), s),
                                        new_body,
                                        env,
                                        &new_forbidden,
                                    )?;
                                    new_param
                                } else {
                                    param.to_owned()
                                })
                            }
                            // now, substitution ca proceed in the alpha-renamed body
                            let final_body = substitute(from, to, new_body, env, &new_forbidden)?;
                            // finally, beta-reduce the function application!
                            // should be unproblematic, since circular definitions are disallowed
                            let beta_reduced = new_params.iter().zip(new_args).try_fold(
                                final_body,
                                |acc, (param, arg)| {
                                    substitute(param, &*arg, acc, env, &new_forbidden)
                                },
                            )?;

                            Ok(beta_reduced)
                        }
                    }
                }
            }
        }
        // recursive cases, unary
        Expr::Sqrt(expr, _) => Ok(Expr::Sqrt(
            Box::new(substitute(from, to, *expr, env, forbidden)?),
            s,
        )),
        Expr::Neg(expr, _) => Ok(Expr::Neg(
            Box::new(substitute(from, to, *expr, env, forbidden)?),
            s,
        )),
        Expr::Fac(expr, _) => Ok(Expr::Fac(
            Box::new(substitute(from, to, *expr, env, forbidden)?),
            s,
        )),
        // recursive cases, binary
        Expr::Root(expr, expr1, _, _) => Ok(Expr::Root(
            Box::new(substitute(from, to, *expr, env, forbidden)?),
            Box::new(substitute(from, to, *expr1, env, forbidden)?),
            s,
            s,
        )),
        Expr::Add(expr, expr1, _) => Ok(Expr::Add(
            Box::new(substitute(from, to, *expr, env, forbidden)?),
            Box::new(substitute(from, to, *expr1, env, forbidden)?),
            s,
        )),
        Expr::Sub(expr, expr1, _) => Ok(Expr::Sub(
            Box::new(substitute(from, to, *expr, env, forbidden)?),
            Box::new(substitute(from, to, *expr1, env, forbidden)?),
            s,
        )),
        Expr::Mul(expr, expr1, _) => Ok(Expr::Mul(
            Box::new(substitute(from, to, *expr, env, forbidden)?),
            Box::new(substitute(from, to, *expr1, env, forbidden)?),
            s,
        )),
        Expr::IMul(expr, expr1, _) => Ok(Expr::IMul(
            Box::new(substitute(from, to, *expr, env, forbidden)?),
            Box::new(substitute(from, to, *expr1, env, forbidden)?),
            s,
        )),
        Expr::Div(expr, expr1, _) => Ok(Expr::Div(
            Box::new(substitute(from, to, *expr, env, forbidden)?),
            Box::new(substitute(from, to, *expr1, env, forbidden)?),
            s,
        )),
        Expr::Pow(expr, expr1, _) => Ok(Expr::Pow(
            Box::new(substitute(from, to, *expr, env, forbidden)?),
            Box::new(substitute(from, to, *expr1, env, forbidden)?),
            s,
        )),
        // special cases
        Expr::Sum(expr, loop_var, range_inclusive, _) => {
            if loop_var == from {
                // loop variable shadows the substitution, stop here
                return Ok(Expr::Sum(expr, loop_var, range_inclusive, s));
            }
            // check if the loop variable would be captured
            let free = free_in_expr(to);
            if free.contains(&loop_var) {
                // if so, rename it
                let new_loop_var = new_var(forbidden);
                let mut new_forbidden = forbidden.clone();
                new_forbidden.insert(new_loop_var.clone());

                let new_body = substitute(
                    &loop_var,
                    &Expr::Ident(new_loop_var.clone(), s),
                    *expr,
                    env,
                    &new_forbidden,
                )?;

                Ok(Expr::Sum(
                    Box::new(substitute(from, to, new_body, env, forbidden)?),
                    new_loop_var,
                    range_inclusive,
                    s,
                ))
            } else {
                // otherwise, proceed into the loop body
                Ok(Expr::Sum(
                    Box::new(substitute(from, to, *expr, env, forbidden)?),
                    loop_var,
                    range_inclusive,
                    s,
                ))
            }
        }
        Expr::Prod(expr, loop_var, range_inclusive, _) => {
            // exact same code as Sum above, TODO: generalize to remove cuplicate code
            if loop_var == from {
                return Ok(Expr::Prod(expr, loop_var, range_inclusive, s));
            }
            let free = free_in_expr(to);
            if free.contains(&loop_var) {
                // if so, rename it
                let new_loop_var = new_var(forbidden);
                let mut new_forbidden = forbidden.clone();
                new_forbidden.insert(new_loop_var.clone());

                let new_body = substitute(
                    &loop_var,
                    &Expr::Ident(new_loop_var.clone(), s),
                    *expr,
                    env,
                    &new_forbidden,
                )?;

                Ok(Expr::Prod(
                    Box::new(substitute(from, to, new_body, env, forbidden)?),
                    new_loop_var,
                    range_inclusive,
                    s,
                ))
            } else {
                Ok(Expr::Prod(
                    Box::new(substitute(from, to, *expr, env, forbidden)?),
                    loop_var,
                    range_inclusive,
                    s,
                ))
            }
        }
        Expr::Int(lower, upper, int_var, body, _) => {
            // lower and upper integral bounds are not affected by the binding of the integration variable
            // -> they must be subsituted either way
            let new_lower = Box::new(substitute(from, to, *lower, env, forbidden)?);
            let new_upper = Box::new(substitute(from, to, *upper, env, forbidden)?);
            if int_var == from {
                // similar to reductions, substitution stops if `from` is shadowed by the integration variable
                Ok(Expr::Int(new_lower, new_upper, int_var, body, s))
            } else {
                let free = free_in_expr(to);
                // if from and the integration variable are different, check if int_var is free in the substituted expr
                // -> that would be a capture, and requires alpha renaming
                if free.contains(&int_var) {
                    // choose a fresh integration variable and alpha rename it in the body
                    let mut new_forbidden = forbidden.clone();
                    new_forbidden.extend(free.iter().cloned());
                    let new_int_var = new_var(&new_forbidden);
                    new_forbidden.insert(new_int_var.to_owned());

                    let renamed_body = substitute(
                        &int_var,
                        &Expr::Ident(new_int_var.to_owned(), s),
                        *body.clone(),
                        env,
                        &new_forbidden,
                    )?;

                    // then, perform the substitution in the body with no risk of captures
                    let new_body = substitute(from, to, renamed_body, env, &new_forbidden)?;
                    Ok(Expr::Int(
                        new_lower,
                        new_upper,
                        new_int_var,
                        Box::new(new_body),
                        s,
                    ))
                } else {
                    // if the integration variable is not free in to, just recurse into the body straightaway
                    Ok(Expr::Int(
                        new_lower,
                        new_upper,
                        int_var,
                        Box::new(substitute(from, to, *body, env, forbidden)?),
                        s,
                    ))
                }
            }
        }
    }
}

fn new_var(forbidden: &HashSet<String>) -> String {
    Vars::default()
        .into_iter()
        .find(|name| !forbidden.contains(name))
        .unwrap()
}
