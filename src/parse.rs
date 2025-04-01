use lazy_static::lazy_static;
use pest::{
    iterators::{Pair, Pairs},
    pratt_parser::{Assoc, Op, PrattParser},
};

use crate::{
    error::{pest_err_adapter, span_merge, Error, SpanInfo},
    Expr, Program, Stmt,
};

lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use Assoc::*;
        use Rule::*;

        PrattParser::new()
            .op(Op::infix(add, Left) | Op::infix(sub, Left))
            .op(Op::prefix(neg))
            .op(Op::infix(mul_implicit, Left))
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
                Rule::real => Expr::Num(primary.as_str().parse::<f64>().unwrap(), span),
                Rule::integer => Expr::Num(primary.as_str().parse::<f64>().unwrap(), span),
                // identifiers
                Rule::identifier => Expr::Ident(primary.as_str().to_owned(), span),
                // {}-bracketed expressions
                Rule::frac => {
                    let mut p = primary.clone().into_inner();
                    let lhs = parse_expr(p.next().unwrap().into_inner(), None);
                    let rhs = parse_expr(p.next().unwrap().into_inner(), None);
                    Expr::Div(Box::new(lhs), Box::new(rhs), span)
                }
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
                Rule::mul_implicit => Expr::IMul(Box::new(lhs), Box::new(rhs), span),
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
