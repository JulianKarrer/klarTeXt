use crate::{error::Error, lookup_env, Env, Expr, Program, Stmt, Typ, Val};

/// Function application and implicit multiplication are ambiguous when
/// parsed as a CFG or context-free grammar, since the actual usage *does*
/// depend on the contex, namely if the right-hand argument is a
/// numeric or a function type.
///
/// Instead of parsing a context sensitive grammar,
/// this second pass is introduced to disambiguate after the global environment
/// was resolved and the types of all variables can be inferred.
///
/// Example of ambiguous usage
/// - f(x+2) as the function f applied to (x+2)
/// - f(x+2) as the constant f multiplied implicitly by (x+2)
pub fn disambiguate(prog: Program, env: &Env) -> Result<Program, Error> {
    let mut res = vec![];
    for stmt in prog {
        res.push(match stmt {
            Stmt::Definition(identifier, expr, span) => {
                Stmt::Definition(identifier, disamb_expr(expr, env)?, span)
            }
            Stmt::Print(expr, counter) => Stmt::Print(disamb_expr(expr, env)?, counter),
        })
    }
    Ok(res)
}

fn disamb_expr(expr: Expr, env: &Env) -> Result<Expr, Error> {
    match expr {
        // base cases
        Expr::Const(ref _val, _) => Ok(expr),
        Expr::Ident(_, _) => Ok(expr),
        // interesting case
        Expr::FnApp(ref func_name, ref args, ref name_span, ref args_span) => {
            let func_val = lookup_env(&func_name, env, *args_span)?;
            match &func_val {
                Val::Num(x) => match &args[..] {
                    [arg] => {
                        return Ok(Expr::IMul(
                            Box::new(Expr::Const(Val::Num(*x), *name_span)),
                            arg.clone(),
                            *args_span,
                        ))
                    }
                    _ => Err(Error::TypeError(
                        Typ::Lam.name(),
                        Typ::Num.name(),
                        *args_span,
                    )),
                },
                Val::Lambda(_, _) => Ok(expr),
            }
        }
        // unary recursive cases
        Expr::Sqrt(expr, span) => Ok(Expr::Sqrt(Box::new(disamb_expr(*expr, env)?), span)),
        Expr::Neg(expr, span) => Ok(Expr::Neg(Box::new(disamb_expr(*expr, env)?), span)),
        Expr::Fac(expr, span) => Ok(Expr::Fac(Box::new(disamb_expr(*expr, env)?), span)),
        Expr::Root(expr, expr1, span1, span2) => Ok(Expr::Root(
            Box::new(disamb_expr(*expr, env)?),
            Box::new(disamb_expr(*expr1, env)?),
            span1,
            span2,
        )),
        // binary recursive cases
        Expr::Add(expr, expr1, span) => Ok(Expr::Add(
            Box::new(disamb_expr(*expr, env)?),
            Box::new(disamb_expr(*expr1, env)?),
            span,
        )),
        Expr::Sub(expr, expr1, span) => Ok(Expr::Sub(
            Box::new(disamb_expr(*expr, env)?),
            Box::new(disamb_expr(*expr1, env)?),
            span,
        )),
        Expr::Mul(expr, expr1, span) => Ok(Expr::Mul(
            Box::new(disamb_expr(*expr, env)?),
            Box::new(disamb_expr(*expr1, env)?),
            span,
        )),
        Expr::IMul(expr, expr1, span) => Ok(Expr::IMul(
            Box::new(disamb_expr(*expr, env)?),
            Box::new(disamb_expr(*expr1, env)?),
            span,
        )),
        Expr::Div(expr, expr1, span) => Ok(Expr::Div(
            Box::new(disamb_expr(*expr, env)?),
            Box::new(disamb_expr(*expr1, env)?),
            span,
        )),
        Expr::Pow(expr, expr1, span) => Ok(Expr::Pow(
            Box::new(disamb_expr(*expr, env)?),
            Box::new(disamb_expr(*expr1, env)?),
            span,
        )),

        Expr::Sum(expr, loop_var, range_inclusive, span) => Ok(Expr::Sum(
            Box::new(disamb_expr(*expr, env)?),
            loop_var,
            range_inclusive,
            span,
        )),
        Expr::Prod(expr, loop_var, range_inclusive, span) => Ok(Expr::Prod(
            Box::new(disamb_expr(*expr, env)?),
            loop_var,
            range_inclusive,
            span,
        )),
        Expr::Int(lower, upper, name, body, span) => Ok(Expr::Int(
            Box::new(disamb_expr(*lower, env)?),
            Box::new(disamb_expr(*upper, env)?),
            name,
            Box::new(disamb_expr(*body, env)?),
            span,
        )),
    }
}
