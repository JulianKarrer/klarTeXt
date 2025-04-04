use std::sync::Arc;

use lazy_static::lazy_static;
use pest::{
    iterators::{Pair, Pairs},
    pratt_parser::{Assoc, Op, PrattParser},
};

use crate::{
    error::{pest_err_adapter, span_merge, Error, SpanInfo}, eval_expr, resolve_def::names_in_expr, Expr, Program, Stmt, Val
};

lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use Assoc::*;
        use Rule::*;

        PrattParser::new()
            .op(Op::infix(add, Left) | Op::infix(sub, Left))
            .op(Op::prefix(neg))
            .op(Op::infix(implicit, Left))
            .op(Op::infix(mul, Left) | Op::infix(div, Left))
            .op(Op::infix(pow, Right) | Op::postfix(fac))
    };
}

#[derive(pest_derive::Parser)]
#[grammar = "grammar.pest"] // relative to src
struct TexParser;

fn parse_expr(expression: Pairs<Rule>, span_arg: Option<SpanInfo>) -> Expr {
    PRATT_PARSER
        .map_primary(|primary: Pair<'_, Rule>| {
            let span = if let Some(s) = span_arg {
                s
            } else {
                (&primary).into()
            };
            match primary.as_rule() {
                // literals
                Rule::real => Expr::Val(Val::Num(primary.as_str().parse::<f64>().unwrap()), span),
                Rule::integer => Expr::Val(Val::Num(primary.as_str().parse::<f64>().unwrap()), span),
                // identifiers
                Rule::identifier => Expr::Ident(primary.as_str().to_owned(), span),
                // {}-bracketed expressions
                Rule::frac => {
                    let mut p = primary.clone().into_inner();
                    let lhs = parse_expr(p.next().unwrap().into_inner(), None);
                    let rhs = parse_expr(p.next().unwrap().into_inner(), None);
                    Expr::Div(Box::new(lhs), Box::new(rhs), span)
                }
                Rule::sqrt => {
                    let mut p = primary.clone().into_inner();
                    let expr = parse_expr(p.next().unwrap().into_inner(), None);
                    Expr::Sqrt(Box::new(expr), span)
                }
                Rule::nthroot => {
                    let mut p = primary.clone().into_inner();
                    let degree = parse_expr(p.next().unwrap().into_inner(), None);
                    let radicant = parse_expr(p.next().unwrap().into_inner(), None);
                    let deg_span = degree.span();
                    let rad_span = radicant.span();
                    Expr::Root(Box::new(degree), Box::new(radicant), deg_span, rad_span)
                }
                Rule::fn_app => {
                    let mut p = primary.into_inner();
                    let fn_name = p.next().unwrap();
                    let fn_name_str = fn_name.as_str().to_owned();
                    let fn_name_span = (&fn_name).into();
                    let mut args = vec![];
                    for arg in p{
                        args.push(Box::new(parse_expr(arg.into_inner(), None)));
                    }
                    Expr::FnApp(fn_name_str, args, fn_name_span, span)
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
                ),
                _ => unreachable!(),
            }
        })
        .map_prefix(|prefix, rhs| {
            let span = (&prefix).into();
            match prefix.as_rule() {
                Rule::neg => Expr::Neg(Box::new(rhs), span),
                _ => unreachable!(),
            }
        })
        .map_infix(|lhs, op, rhs| {
            let span = span_merge(&lhs, &rhs);
            match op.as_rule() {
                Rule::add => Expr::Add(Box::new(lhs), Box::new(rhs), span),
                Rule::sub => Expr::Sub(Box::new(lhs), Box::new(rhs), span),
                Rule::mul => Expr::Mul(Box::new(lhs), Box::new(rhs), span),
                Rule::div => Expr::Div(Box::new(lhs), Box::new(rhs), span),
                Rule::pow => Expr::Pow(Box::new(lhs), Box::new(rhs), span),
                Rule::implicit => Expr::IMul(Box::new(lhs), Box::new(rhs), span),
                _ => unreachable!(),
            }
        })
        .map_postfix(|lhs, postfix| {
            let span = span_merge(&lhs, &postfix);
            match postfix.as_rule() {
                Rule::fac => Expr::Fac(Box::new(lhs), span),
                _ => unreachable!(),
            }
        })
        .parse(expression)
}

fn parse_stmt(stmt: Pair<'_, Rule>, output_counter: &mut i64) -> Option<Stmt> {
    match stmt.as_rule() {
        Rule::expr_statement => None,
        Rule::print_statement => {
            let expr = parse_expr(stmt.into_inner().next().unwrap().into_inner(), None);
            *output_counter += 1;
            Some(Stmt::Print(expr, *output_counter))
        }
        Rule::definition => {
            let mut def = stmt.into_inner();
            let name = def.next().unwrap().as_str();
            let expr = parse_expr(def.next().unwrap().into_inner(), None);
            Some(Stmt::Definition(name.to_owned(), expr))
        }
        Rule::fn_definition => {
            let span = (&stmt).into();
            let mut def = stmt.into_inner();
            let mut signature = def.next().unwrap().into_inner();
            let func_name = signature.next().unwrap().as_str().to_owned();
            let mut params = vec![];
            for param in signature{
                params.push(param.as_str().to_owned());
            }
            let param_count = params.len();
            let body = def.next().unwrap().into_inner();
            let body_str = body.as_str().to_owned();
            let body_expr = parse_expr(body, None);
            let names = names_in_expr(&body_expr);
            Some(Stmt::Definition(func_name.clone(), Expr::Val(Val::Lambda(
                // the function string contains the body of the definition for error handling, printing etc.
                body_str.clone(), 
                names,
                params.clone(),
                param_count as isize, 
                Arc::new({ move |xs: Vec<Val>, env, span| {
                        if xs.len() != param_count {
                            // throw an error if the argument count is incorrect
                            return Err(Error::FnArgCount(func_name.clone(), param_count, xs.len(), span));
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
                })
            ), span)))
        }
        _ => unreachable!(),
    }
}

pub fn parse_main(input: &str) -> Result<Program, Error> {
    let mut output_counter = 0;
    match <TexParser as pest::Parser<Rule>>::parse(Rule::main, input) {
        Ok(res) => Ok(res
            .into_iter()
            .map(|stmt| match stmt.as_rule() {
                Rule::EOI => None,
                Rule::statement => {
                    parse_stmt(stmt.into_inner().next().unwrap(), &mut output_counter)
                }
                _ => {
                    println!("{:?}", stmt);
                    unreachable!()
                }
            })
            .flatten()
            .collect()),
        Err(err) => Err(pest_err_adapter(err)),
    }
}
