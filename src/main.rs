use std::f64::consts::{E, PI};

use pest::{iterators::Pairs, pratt_parser::{Assoc, Op, PrattParser}, Parser};
use pest_derive::Parser;
use lazy_static::lazy_static;
use phf::phf_map;

#[derive(Debug)]
enum Expr {
    Num(f64),
    Ident(String),

    Neg(Box<Expr>),
    Fac(Box<Expr>),

    // Cos(Box<Expr>),
    // Sin(Box<Expr>),
    // Tan(Box<Expr>),
    // Exp(Box<Expr>),
    // Ln(Box<Expr>),

    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    IMul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Pow(Box<Expr>, Box<Expr>),
}

static CONSTANTS: phf::Map<&'static str, f64> = phf_map! {
    r"e" => E,
    r"\pi" => PI,
};

lazy_static! {
    static ref PRATT_PARSER: PrattParser<Rule> = {
        use Rule::*;
        use Assoc::*;

        PrattParser::new()
            .op(Op::infix(add, Left) | Op::infix(sub, Left) | Op::prefix(neg))
            .op(Op::infix(mul_implicit, Left))
            .op(Op::infix(mul, Left) | Op::infix(div, Left))
            .op(Op::infix(pow, Right) | Op::postfix(fac))
    };
}

#[derive(Parser)]
#[grammar = "grammar.pest"] // relative to src
struct TexParser;

fn parse_expr(expression: Pairs<Rule>) -> Expr {
    PRATT_PARSER
        .map_primary(|primary| match primary.as_rule() {
            // literals
            Rule::real => Expr::Num(primary.as_str().parse::<f64>().unwrap()),
            Rule::integer => Expr::Num(primary.as_str().parse::<f64>().unwrap()),
            // identifiers
            Rule::identifier => Expr::Ident(primary.as_str().to_owned()),
            // {}-bracketed expressions
            Rule::frac => {
                let mut p = primary.into_inner();
                let lhs = p.next().unwrap().into_inner();
                let rhs = p.next().unwrap().into_inner();
                Expr::Div(
                    Box::new(parse_expr(lhs)), 
                    Box::new(parse_expr(rhs))
                )
            },
            // recursive case
            Rule::expr => parse_expr(primary.into_inner()),
            _ => unreachable!(),
        })
        .map_prefix(|prefix, rhs| match prefix.as_rule() {
            Rule::neg => Expr::Neg(Box::new(rhs)),
            _ => unreachable!(),
        })
        .map_infix(|lhs, op, rhs| match op.as_rule() {
            Rule::add => Expr::Add(Box::new(lhs), Box::new(rhs)),
            Rule::sub => Expr::Sub(Box::new(lhs), Box::new(rhs)),
            Rule::mul => Expr::Mul(Box::new(lhs), Box::new(rhs)),
            Rule::div => Expr::Div(Box::new(lhs), Box::new(rhs)),
            Rule::pow => Expr::Pow(Box::new(lhs), Box::new(rhs)),
            Rule::mul_implicit => Expr::IMul(Box::new(lhs), Box::new(rhs)),
            _ => unreachable!(),
        })
        .map_postfix(|lhs,postfix|{
            match postfix.as_rule(){
                Rule::fac => Expr::Fac(Box::new(lhs)),
                _ => unreachable!(),
            }
        })
        .parse(expression)
}

fn eval_expr(expr: &Expr) -> f64{
    fn factorial(n: f64) -> f64 {
        if n < 0.0 {
            panic!("Factorial is not defined for negative numbers.");
        }
        // Ensure n is effectively an integer.
        let n_int = n.round() as u64;
        if (n - n_int as f64).abs() > std::f64::EPSILON {
            panic!("Factorial is only defined for integer values.");
        }
        // Compute factorial iteratively.
        (1..=n_int).map(|x| x as f64).product()
    }
    match expr{
        Expr::Num(x) => *x,
        Expr::Neg(x) => -eval_expr(x),
        Expr::Fac(x) => factorial(eval_expr(x)),
        Expr::Add(lhs, rhs) => eval_expr(lhs) + eval_expr(rhs),
        Expr::Sub(lhs, rhs) => eval_expr(lhs) - eval_expr(rhs),
        Expr::IMul(lhs, rhs) => eval_expr(lhs) * eval_expr(rhs),
        Expr::Mul(lhs, rhs) => eval_expr(lhs) * eval_expr(rhs),
        Expr::Div(lhs, rhs) => eval_expr(lhs) / eval_expr(rhs),
        Expr::Pow(lhs, rhs) => eval_expr(lhs).powf(eval_expr(rhs)),
        Expr::Ident(name) => if let Some(cnst) = CONSTANTS.get(name){
                        *cnst
            } else {
                // TODO: Error handling
                panic!("Undefined identifier {} in expression", name)
            },
    }
}

pub fn main(){
    match TexParser::parse(Rule::main, include_str!("../test/test1.tex")){
        Ok(res) => {
            for stmt in res{
                match stmt.as_rule(){
                    Rule::EOI => {},
                    Rule::math_evn => {
                        let expr = parse_expr(stmt.into_inner());
                        let val = eval_expr(&expr);
                        println!("{:?}\n\tresult: {}", expr, val);
                    },
                    _ => unreachable!()
                };
            }
        },
        Err(err) => println!("{:?}", err),
    }
}