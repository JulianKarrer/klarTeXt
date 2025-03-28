use std::{collections::{HashMap, HashSet}, f64::consts::{E, PI}};
use pest::{iterators::{Pair, Pairs}, pratt_parser::{Assoc, Op, PrattParser}, Parser};
use pest_derive::Parser;
use lazy_static::lazy_static;
use topo_sort::{SortResults, TopoSort};

type Program = Vec<Statement>;
type Program1 = (Program, HashMap<String, f64>);

#[derive(Debug)]
enum Statement {
    Definition(String, Expr),
    Print(Expr, i64),
}

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

    static ref CONSTANTS:HashMap<String, f64> = HashMap::from([
        (r"e".to_owned(), E),
        (r"\pi".to_owned(), PI),
    ]);
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

fn parse_stmt(stmt: Pair<'_, Rule>, output_counter:&mut i64)->Option<Statement>{
    match stmt.as_rule(){
        Rule::expr_statement => {None},
        Rule::print_statement => {
            let expr = parse_expr(
                stmt.into_inner().next().unwrap().into_inner()
            );
            *output_counter += 1;
            Some(Statement::Print(expr, *output_counter))
        },
        Rule::definition => {
            let mut def = stmt.into_inner();
            let name = def.next().unwrap().as_str();
            let expr = parse_expr(def.next().unwrap().into_inner());
            Some(Statement::Definition(name.to_owned(), expr))
        },
        _ => unreachable!(),
    }
}

fn parse_main(input: &str)->Program{
    let mut output_counter = 0;
    match TexParser::parse(Rule::main, input){
        Ok(res) => {
                res.into_iter().map(|stmt|{
                    match stmt.as_rule(){
                        Rule::EOI => {None},
                        Rule::statement => {
                            parse_stmt(stmt.into_inner().next().unwrap(), &mut output_counter)
                        },
                        _ => unreachable!()
                    }
                }).flatten().collect()
        },
        Err(err) => panic!("{:?}", err), // TODO error handling
    }
}

// SEMANTICS - DEFINITIONAL INTERPRETER
fn eval_expr(expr: &Expr, env:&HashMap<String, f64>) -> f64{
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
        Expr::Neg(x) => -eval_expr(x, env),
        Expr::Fac(x) => factorial(eval_expr(x, env)),
        Expr::Add(lhs, rhs) => eval_expr(lhs, env) + eval_expr(rhs, env),
        Expr::Sub(lhs, rhs) => eval_expr(lhs, env) - eval_expr(rhs, env),
        Expr::IMul(lhs, rhs) => eval_expr(lhs, env) * eval_expr(rhs, env),
        Expr::Mul(lhs, rhs) => eval_expr(lhs, env) * eval_expr(rhs, env),
        Expr::Div(lhs, rhs) => eval_expr(lhs, env) / eval_expr(rhs, env),
        Expr::Pow(lhs, rhs) => eval_expr(lhs, env).powf(eval_expr(rhs, env)),
        Expr::Ident(name) => if let Some(cnst) = CONSTANTS.get(name){
                // look for predefined constants
                *cnst
            } else {
                if let Some(cnst) = env.get(name){
                    // then look for user-defined constants
                    *cnst
                } else {
                    // TODO: Error handling
                    panic!("Undefined identifier {} in expression", name)
                }
            },
    }
}


fn get_names(expr: &Expr)->HashSet<String>{
    match expr{
        // base cases
        Expr::Num(_) => {HashSet::new()}, 
        Expr::Ident(name) => HashSet::from([name.to_owned()]),
        // unary recursive cases
        Expr::Neg(expr) | Expr::Fac(expr) 
            => get_names(expr),
        // binary recursive cases
        Expr::Add(expr1, expr2) | 
        Expr::Sub(expr1, expr2) |
        Expr::Mul(expr1, expr2) |
        Expr::IMul(expr1, expr2) |
        Expr::Div(expr1, expr2) |
        Expr::Pow(expr1, expr2) 
            => &get_names(expr1) | &get_names(&expr2),
    }
}

fn resolve_definitions(prog:Program)->Program1{
    let mut dependencies = TopoSort::with_capacity(prog.len());
    let mut definitions = HashMap::new();
    let mut prints = vec![];
    let mut env = HashMap::new();
    
    // find the set of names that each definition depends on
    for stmt in prog{
        match stmt{
            Statement::Definition(name, expr) => {
                        dependencies.insert_from_set(name.to_owned(), get_names(&expr));
                        definitions.insert(name, expr);
                    },
            Statement::Print(expr, c) => prints.push(Statement::Print(expr, c)),
        }
    }

    // topologically sort the dependencies or detect a cycle
    match dependencies.into_vec_nodes() {
        SortResults::Partial(_) => panic!("Cyclic definitions!"),
        SortResults::Full(nodes) => {
            for name in nodes{
                let expr = definitions.get(&name).unwrap();
                // evaluate the expression:
                // this must be possible, since definitions are now topologically ordered
                let res = eval_expr(expr, &env);
                // add the resolved definition to the environment
                env.insert(name.to_owned(), res);
            }
        },
    }

    // return the resolved definitions along with other statements
    (prints, env)
}

fn debug_run(prog:Program, env: HashMap<String, f64>, _counter:i64){
    println!("DEFINITIONS: -----------");
    for (k,v) in &env{
        println!("{} = {}", k, v)
    }
    println!("PRINTS: ----------------");
    for stmt in prog{
        match stmt {
            Statement::Print(expr, c) => println!("{} >>> {}", c, eval_expr(&expr, &env)),
            _ => {}
        }
    }
}

pub fn main(){
    let p0 = parse_main(include_str!("../test/test1.tex"));
    let (p1, env) = resolve_definitions(p0);
    debug_run(p1, env, 0);
}