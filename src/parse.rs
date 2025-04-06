use std::{
    f64::INFINITY,
    sync::{Arc, LazyLock},
};

use pest::{
    iterators::{Pair, Pairs},
    pratt_parser::{Assoc, Op, PrattParser},
};

use crate::{
    error::{pest_err_adapter, span_merge, Error, SpanInfo},
    eval_expr,
    resolve_def::names_in_expr,
    Expr, Program, Stmt, Val,
};

static PRATT_PARSER: LazyLock<PrattParser<Rule>> = LazyLock::new(|| {
    use Assoc::*;
    use Rule::*;

    PrattParser::new()
        .op(Op::infix(add, Left) | Op::infix(sub, Left))
        .op(Op::prefix(neg) | Op::prefix(sum) | Op::prefix(prod))
        .op(Op::infix(implicit, Left))
        .op(Op::infix(mul, Left) | Op::infix(div, Left))
        .op(Op::infix(pow, Right) | Op::postfix(fac))
});

#[derive(pest_derive::Parser)]
#[grammar = "grammar.pest"] // relative to src
struct TexParser;

fn parse_expr(expression: Pairs<Rule>, span_arg: Option<SpanInfo>, src: &str) -> Result<Expr,Error> {
    PRATT_PARSER
        .map_primary(|primary: Pair<'_, Rule>| {
            let span = if let Some(s) = span_arg {
                s
            } else {
                (&primary).into()
            };
            match primary.as_rule() {
                // literals
                Rule::real => Ok(Expr::Val(Val::Num(primary.as_str().parse::<f64>().unwrap()), span)),
                Rule::integer => {
                    Ok(Expr::Val(Val::Num(primary.as_str().parse::<f64>().unwrap()), span))
                },
                Rule::digit => {
                    Ok(Expr::Val(Val::Num(primary.as_str().parse::<f64>().unwrap()), span))
                }
                Rule::infinity => Ok(Expr::Val(Val::Num(INFINITY), span)),
                // identifiers
                Rule::identifier => Ok(Expr::Ident(primary.as_str().to_owned(), span)),
                // {}-bracketed expressions
                Rule::frac => {
                    let mut p = primary.clone().into_inner();
                    let lhs = parse_expr(p.next().unwrap().into_inner(), None, src)?;
                    let rhs = parse_expr(p.next().unwrap().into_inner(), None, src)?;
                    Ok(Expr::Div(Box::new(lhs), Box::new(rhs), span))
                }
                Rule::sqrt => {
                    let mut p = primary.clone().into_inner();
                    let expr = parse_expr(p.next().unwrap().into_inner(), None, src)?;
                    Ok(Expr::Sqrt(Box::new(expr), span))
                }
                Rule::nthroot => {
                    let mut p = primary.clone().into_inner();
                    let degree = parse_expr(p.next().unwrap().into_inner(), None, src)?;
                    let radicant = parse_expr(p.next().unwrap().into_inner(), None, src)?;
                    let deg_span = degree.span();
                    let rad_span = radicant.span();
                    Ok(Expr::Root(Box::new(degree), Box::new(radicant), deg_span, rad_span))
                }
                Rule::fn_app => {
                    let mut p = primary.into_inner();
                    let fn_name = p.next().unwrap();
                    let fn_name_str = fn_name.as_str().to_owned();
                    let fn_name_span = (&fn_name).into();
                    let mut args = vec![];
                    for arg in p {
                        args.push(Box::new(parse_expr(arg.into_inner(), None, src)?));
                    }
                    Ok(Expr::FnApp(fn_name_str, args, fn_name_span, span))
                }
                Rule::bracketed_expr => parse_expr(
                    primary.into_inner().next().unwrap().into_inner(),
                    Some(if span_arg.is_none() {
                        SpanInfo {
                            from: span.from - 1,
                            to: span.to,
                        }
                    } else {
                        span
                    }),
                    src
                ),
                // recursive case
                Rule::expr => parse_expr(
                    primary.into_inner(),
                    Some(if span_arg.is_none() {
                        SpanInfo {
                            from: span.from - 1,
                            to: span.to,
                        }
                    } else {
                        span
                    }),
                    src
                ),
                _ => {println!("{:?}", primary);unreachable!()},
            }
        })
        .map_prefix(|prefix, rhs| {
            let span = (&prefix).into();
            let rhs = rhs?;
            match prefix.as_rule() {
                Rule::neg => Ok(Expr::Neg(Box::new(rhs), span)),
                Rule::sum => {
                    let (low,high,body_lam) = parse_reduction(prefix, rhs, src)?;
                    Ok(Expr::Sum(low..=high, body_lam, span))
                },
                Rule::prod => {
                    let (low,high,body_lam) = parse_reduction(prefix, rhs, src)?;
                    Ok(Expr::Prod(low..=high, body_lam, span))
                },
                _ => unreachable!(),
            }
        })
        .map_infix(|lhs, op, rhs| {
            let lhs = lhs?;
            let rhs = rhs?;
            let span = span_merge(&lhs, &rhs);
            match op.as_rule() {
                Rule::add => Ok(Expr::Add(Box::new(lhs), Box::new(rhs), span)),
                Rule::sub => Ok(Expr::Sub(Box::new(lhs), Box::new(rhs), span)),
                Rule::mul => Ok(Expr::Mul(Box::new(lhs), Box::new(rhs), span)),
                Rule::div => Ok(Expr::Div(Box::new(lhs), Box::new(rhs), span)),
                Rule::pow => Ok(Expr::Pow(Box::new(lhs), Box::new(rhs), span)),
                Rule::implicit => Ok(Expr::IMul(Box::new(lhs), Box::new(rhs), span)),
                _ => unreachable!(),
            }
        })
        .map_postfix(|lhs, postfix| {
            let lhs = lhs?;
            let span = span_merge(&lhs, &postfix);
            match postfix.as_rule() {
                Rule::fac => Ok(Expr::Fac(Box::new(lhs), span)),
                _ => unreachable!(),
            }
        })
        .parse(expression)
}

fn reduction_expect_int(expr:&Expr)->Result<i64, Error>{
    if let Expr::Val(Val::Num(x), _) = expr{
        if (x - x.round()) < f64::EPSILON{
            Ok(x.round() as i64)
        } else {
            Err(Error::SumNonIntegerVar(expr.span()))
        }
    } else {
        Err(Error::SumBodyNotNumeric(expr.span()))
    }
}

fn parse_reduction(pair:Pair<'_, Rule>, rhs:Expr, src: &str)->Result<(i64, i64, Val), Error>{
    let mut sum = pair.into_inner();
    let sum_var = sum.next().unwrap().as_str().to_owned();
    let low_expr = parse_expr(sum.next().unwrap().into_inner(), None, src)?;
    let high_expr = parse_expr(sum.next().unwrap().into_inner(), None, src)?;

    let low = reduction_expect_int(&low_expr)?;
    let high = reduction_expect_int(&high_expr)?;

    let body_str = rhs.span().read_source(src);
    let body = create_function(
        sum.as_str().to_owned(), 
        vec![sum_var], 
        rhs, 
        body_str
    );

   Ok((low, high, body))
}

fn create_function(
    name:String, 
    params:Vec<String>, 
    body_expr:Expr, 
    body_str:String,
)->Val{
    let names = names_in_expr(&body_expr);
    let param_count = params.len();
    Val::Lambda(
        // the function string contains the body of the definition for error handling, printing etc.
        body_str.clone(),
        names,
        params.clone(),
        Arc::new({
            move |xs: Vec<Val>, env, span| {
                if xs.len() != param_count {
                    // throw an error if the argument count is incorrect
                    return Err(Error::FnArgCount(
                        name.clone(),
                        param_count,
                        xs.len(),
                        span,
                    ));
                } else {
                    // otherwise add arguments to the environment
                    let mut env_inner = env.clone(); // TODO: avoid clone
                    for (key, val) in params.iter().zip(xs) {
                        env_inner.insert((*key).to_owned(), val);
                    }
                    // then evaluate the function body expression in the new, inner scope
                    eval_expr(&body_expr, &env_inner)
                }
            }
        }),
    )
}

fn parse_stmt(stmt: Pair<'_, Rule>, output_counter: &mut i64, src: &str) -> Result<Option<Stmt>, Error> {
    match stmt.as_rule() {
        Rule::expr_statement => Ok(None),
        Rule::print_statement => {
            let expr = parse_expr(stmt.into_inner().next().unwrap().into_inner(), None, src)?;
            *output_counter += 1;
            Ok(Some(Stmt::Print(expr, *output_counter)))
        }
        Rule::definition => {
            let span = (&stmt).into();
            let mut def = stmt.into_inner();
            let name = def.next().unwrap().as_str();
            let expr = parse_expr(def.next().unwrap().into_inner(), None, src)?;
            Ok(Some(Stmt::Definition(name.to_owned(), expr, span)))
        }
        Rule::fn_definition => {
            let span = (&stmt).into();
            let mut def = stmt.into_inner();
            let mut signature = def.next().unwrap().into_inner();
            let func_name = signature.next().unwrap().as_str().to_owned();
            let mut params = vec![];
            for param in signature {
                params.push(param.as_str().to_owned());
            }
            let body = def.next().unwrap().into_inner();
            let body_str = body.as_str().to_owned();
            let body_expr = parse_expr(body, None, src)?;
            Ok(Some(Stmt::Definition(
                func_name.clone(),
                Expr::Val(
                    create_function(func_name, params, body_expr, body_str),
                    span,
                ),
                span,
            )))
        }
        _ => unreachable!(),
    }
}

pub fn parse_main(src: &str) -> Result<Program, Error> {
    let mut output_counter = 0;
    match <TexParser as pest::Parser<Rule>>::parse(Rule::main, src) {
        Ok(res) => {
            let mut prog = vec![];
            for stmt in res{
                match stmt.as_rule() {
                    Rule::EOI => {},
                    Rule::statement => {
                        let pairs = stmt.into_inner().next().unwrap();
                        if let Some(parsed) = parse_stmt(pairs, &mut output_counter, src)?{
                            prog.push(parsed);
                        };
                    },
                    _ => {
                        println!("{:?}", stmt);
                        unreachable!()
                    }
                }
            }
            Ok(prog)
        },
        Err(err) => Err(pest_err_adapter(err)),
    }
}
