use ariadne::{ColorGenerator, Config, Label, Report, ReportKind, Source};
use itertools::Itertools;
use lazy_static::lazy_static;
use pest::{
    iterators::{Pair, Pairs},
    pratt_parser::{Assoc, Op, PrattParser},
    Parser,
};
use pest_derive::Parser;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    f64::consts::{E, PI},
    ops::Range,
    process::exit,
};

type Program = Vec<Stmt>;
type Program1 = (Program, HashMap<String, f64>);

#[derive(Debug)]
enum Stmt {
    Definition(String, Expr),
    Print(Expr, i64),
}

#[derive(Debug)]
enum Expr {
    Num(f64, SpanInfo),
    Ident(String, SpanInfo),

    Neg(Box<Expr>, SpanInfo),
    Fac(Box<Expr>, SpanInfo),

    Add(Box<Expr>, Box<Expr>, SpanInfo),
    Sub(Box<Expr>, Box<Expr>, SpanInfo),
    Mul(Box<Expr>, Box<Expr>, SpanInfo),
    IMul(Box<Expr>, Box<Expr>, SpanInfo),
    Div(Box<Expr>, Box<Expr>, SpanInfo),
    Pow(Box<Expr>, Box<Expr>, SpanInfo),
}

// ERROR HANDLING
#[derive(Debug, Copy, Clone)]
struct SpanInfo {
    from: usize,
    to: usize,
}
impl From<&Pair<'_, Rule>> for SpanInfo {
    fn from(val: &Pair<'_, Rule>) -> Self {
        Self {
            from: val.as_span().start_pos().pos(),
            to: val.as_span().end_pos().pos(),
        }
    }
}
impl From<&Expr> for SpanInfo {
    fn from(val: &Expr) -> Self {
        val.span()
    }
}
fn span_merge<T: Into<SpanInfo>, U: Into<SpanInfo>>(lhs: T, rhs: U) -> SpanInfo {
    SpanInfo {
        from: lhs.into().from,
        to: rhs.into().to,
    }
}
impl From<&SpanInfo> for Range<usize> {
    fn from(value: &SpanInfo) -> Self {
        value.from..value.to
    }
}

#[derive(Debug)]
enum Error {
    // Parsing Errors
    ParseError(SpanInfo, String),
    // Syntax Errors
    //     Definitions
    DefMissing(SpanInfo, String),
    DefMultiply(SpanInfo, String),
    DefCircular(Vec<(String, SpanInfo, String)>),
    //     Implicit Multiplication
    ImpMulRhsNum(SpanInfo, SpanInfo),
    ImpMulNumNum(SpanInfo, SpanInfo),
    // Math Errors
    FactorialNeg(SpanInfo),
    FactorialFloat(SpanInfo),
    DivByZero(SpanInfo),
}

impl Error {
    fn span(&self) -> std::ops::Range<usize> {
        match self {
            Error::ParseError(span_info, _) => span_info.into(),
            Error::DefMissing(span_info, _) => span_info.into(),
            Error::DefMultiply(span_info, _) => span_info.into(),
            Error::DefCircular(cycle) => {
                cycle.iter().map(|(_, span, _)| span.from).min().unwrap()
                    ..cycle.iter().map(|(_, span, _)| span.to).max().unwrap()
            }
            Error::FactorialNeg(span_info) => span_info.into(),
            Error::FactorialFloat(span_info) => span_info.into(),
            Error::DivByZero(span_info) => span_info.into(),
            Error::ImpMulRhsNum(lhs, rhs) => lhs.from..rhs.to,
            Error::ImpMulNumNum(lhs, rhs) => lhs.from..rhs.to,
        }
    }
}
impl Expr {
    fn span(&self) -> SpanInfo {
        match self {
            Expr::Num(_, span_info) => *span_info,
            Expr::Ident(_, span_info) => *span_info,
            Expr::Neg(_, span_info) => *span_info,
            Expr::Fac(_, span_info) => *span_info,
            Expr::Add(_, _, span_info) => *span_info,
            Expr::Sub(_, _, span_info) => *span_info,
            Expr::Mul(_, _, span_info) => *span_info,
            Expr::IMul(_, _, span_info) => *span_info,
            Expr::Div(_, _, span_info) => *span_info,
            Expr::Pow(_, _, span_info) => *span_info,
        }
    }
}

fn err_report<S>(
    labels: Vec<(Range<usize>, S)>,
    message: &str,
    note: &str,
    filename: &str,
    src: &str,
    span: Range<usize>,
) where
    S: ToString,
{
    let mut colors = ColorGenerator::new();
    let config = Config::new().with_index_type(ariadne::IndexType::Byte);
    let mut report = Report::build(ReportKind::Error, (filename, span))
        .with_message(message)
        .with_config(config);
    let mut order = 0;
    for (lspan, label) in labels {
        report = report.with_label(
            Label::new((filename, lspan))
                .with_message(label)
                .with_order(order)
                .with_color(colors.next()),
        );
        order += 1;
    }
    report
        .with_note(note)
        .finish()
        .print((filename, Source::from(src)))
        .unwrap();
}

fn handle_errs<T>(res: Result<T, Error>, src: &str, filename: &str) -> T {
    match res {
        Ok(val) => val,
        Err(err) => {
            match &err {
                Error::ParseError(_,note) => err_report(
                    vec![(
                        (&err).span(),
                        "the unexpected input is here",
                    )],
                    "Syntax Error",
                    &format!("There is a syntax error in your program, which caused parsing to fail.\n{}", note),
                    filename,
                    src,
                    err.span(),
                ),
                Error::DefMissing(_, name) => err_report(
                    vec![(
                        (&err).span(),
                        &format!("The identifier {} is undefined.", name),
                    )],
                    "Undefined identifier",
                    "It does not matter in which order you define identifiers using '=', but this one is never defined.\nMaybe you meant to use a predefined identifier like e or π?",
                    filename,
                    src,
                    err.span(),
                ),
                Error::DefMultiply(_, name) => err_report(
                    vec![(
                        (&err).span(),
                        &format!("The identifier {} was defined at least twice", name),
                    )],
                    "Multiply defined identifier",
                    "Definitions using '=' are static, immutable, single assignments of a constant expression to a name.\nYou cannot bind an expression to the same name twice.",
                    filename,
                    src,
                    err.span(),
                ),
                Error::DefCircular(cycle) => {
                    err_report(
                    cycle.iter().map(|(name, span, depends_on)|(
                        span.into(), format!("{} depends on {}", name, depends_on)
                    )).collect(),
                    "Cyclic Definitions",
                    "Cyclic Definition detected.\nCompile-time recursion using the static definition '=' is not currently supported.\nDefinitions with '=' bind an expression immutably to a single name forever.\nMaybe you meant to use a mutable assignment?",
                    filename,
                    src,
                    err.span(),
                )},
                Error::FactorialNeg(_) => err_report(
                                vec![(
                                    err.span().start..err.span().end-1,
                                    "This expression evaluates to a negative number.",
                                )],
                                "Negative Argument to Factorial",
                                "The Factorial function '!' is only defined for non-negative integers.",
                                filename,
                                src,
                                err.span(),
                            ),
                Error::FactorialFloat(_) => err_report(
                                vec![(
                                    err.span().start..err.span().end-1,
                                    "This expression evaluates to a non-integer.",
                                )],
                                "Non-Integer Argument to Factorial",
                                "The Factorial function '!' is only defined for non-negative integers.\nPerhaps you want to use a more general Gamma function Γ?",
                                filename,
                                src,
                                err.span(),
                            ),
                Error::DivByZero(_) => err_report(
                                vec![(
                                    err.span(),
                                    "This division results in an undefined value",
                                )],
                                "Division by Zero",
                                "You can sometimes avoid divisions by zero by rearranging terms.\nMultiplication implements short-circuiting, so 'zero times x' is always zero, even if x is undefined.\nIn that case, evaluation is left-to-right and the order of terms matters!",
                                filename,
                                src,
                                err.span(),
                            ),
                Error::ImpMulRhsNum(lhs, rhs) => err_report(
                    vec![(
                        lhs.into(),
                        "this expression gets multiplied",
                    ),(
                        rhs.into(),
                        "with a numerical literal on the right-hand side",
                    )],
                    "Implicit multiplication with a number on the right side",
                    "Implicit multiplication is meant to be used for terms like:\n - 3x + 2y\n - 2(x+3)\nBut here, there is a number on the right-hand side of the multiplication.\nThis is an error, since it is usually unintended.",
                    filename,
                    src,
                    err.span(),
                ),
                Error::ImpMulNumNum(lhs, rhs) => err_report(
                    vec![(
                        lhs.into(),
                        "this is a number",
                    ),(
                        rhs.into(),
                        "this is also a number",
                    )],
                    "Implicit multiplication of two numbers",
                    "Implicit multiplication is meant to be used for terms like:\n - 3x + 2y\n - 2(x+3)\nBut here it was used to multiply two numbers.\nThis is an error, since it is usually unintended.",
                    filename,
                    src,
                    err.span(),
                ),
            }
            exit(1)
        }
    }
}

fn rule_description(rule: Rule) -> &'static str {
    match rule {
        Rule::EOI => "end of the file",
        Rule::WHITESPACE => "whitespace",
        Rule::COMMENT => "a comment",
        Rule::IGNORE => "whitespace or a comment",
        Rule::outside => "text outside of the 'program' environment",
        Rule::main => "a latex document with a program environment",
        Rule::program => "a program environment",
        Rule::statement => "a statement",
        Rule::expr_statement => "a standalone expression (which  is ignored)",
        Rule::print_statement => "a print statement",
        Rule::definition => "a definition",
        Rule::math_evn => "a math environment",
        Rule::expr => "an expression",
        Rule::primary => "the atom of an expression",
        Rule::number_literal => "a numerical literal",
        Rule::real => "a real number",
        Rule::integer => "an integer",
        Rule::enclosed => "something enclosed in {} brackets",
        Rule::frac => "a fraction \\frac{}{}",
        Rule::keyword => "a keyword like '\\left', '\\cdot' etc.",
        Rule::identifier => "an identifier like 'x' or 'y_{t=0}'",
        Rule::simple_identifier => "a simple, single letter identifier",
        Rule::latex_symbol => "a single latex symbol, like '\\pi' or '\\eta'",
        Rule::subscript => "a subscript '_{ ... }'",
        Rule::nested_block => "a nested subscript",
        Rule::infix => "an infix operation (+,-,*,/,...)",
        Rule::add => "addition (+)",
        Rule::sub => "subtraction (-)",
        Rule::mul => "multiplication (*)",
        Rule::mul_implicit => "implicit multiplication (3x, 5(y+2), ...)",
        Rule::div => "a division (using e.g. \\frac{}{})",
        Rule::pow => "exponentiation (e^x etc.)",
        Rule::prefix => "a prefix operator (like '-' in '-5')",
        Rule::neg => "a negation (prefix -)",
        Rule::postfix => "a postfix operator (like !)",
        Rule::fac => "a factorial (!)",
    }
}

fn parse_error(err: pest::error::Error<Rule>) -> Error {
    Error::ParseError(
        match err.location {
            pest::error::InputLocation::Pos(f) => SpanInfo { from: f, to: f },
            pest::error::InputLocation::Span((f, t)) => SpanInfo { from: f, to: t },
        },
        match err.variant {
            pest::error::ErrorVariant::ParsingError {
                positives,
                negatives,
            } => {
                // tell the user what was expected next
                let mut res = match positives[..] {
                    [] => String::new(),
                    [r] => format!("The parser expected to see {}.", rule_description(r)),
                    _ => format!(
                        "The parser expected to see one of the following: \n\t- {}",
                        positives.iter().map(|r| rule_description(*r)).join("\n\t- ")
                    ),
                };
                if positives.len() > 0 {
                    res.push('\n');
                }
                res.push_str(&match negatives[..] {
                    [] => String::new(),
                    [r] => format!("The parser expected NOT to see {}.", rule_description(r)),
                    _ => format!(
                        "The parser expected to see NONE of the following {}.",
                        positives.iter().map(|r| rule_description(*r)).join(", ")
                    ),
                });
                res
            }
            pest::error::ErrorVariant::CustomError { message } => message,
        },
    )
}

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
    static ref PREDEFINED_CONSTANTS: HashMap<String, f64> =
        HashMap::from([(r"e".to_owned(), E), (r"\pi".to_owned(), PI),]);
}

#[derive(Parser)]
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

fn parse_main(input: &str) -> Result<Program, Error> {
    let mut output_counter = 0;
    match TexParser::parse(Rule::main, input) {
        Ok(res) => Ok(res
            .into_iter()
            .map(|stmt| match stmt.as_rule() {
                Rule::EOI => None,
                Rule::statement => {
                    parse_stmt(stmt.into_inner().next().unwrap(), &mut output_counter)
                }
                _ => {println!("{:?}", stmt); unreachable!()},
            })
            .flatten()
            .collect()),
        Err(err) => Err(parse_error(err)),
    }
}

// SEMANTICS - DEFINITIONAL INTERPRETER

fn custom_mul(lhs: &Expr, rhs: &Expr, env: &HashMap<String, f64>) -> Result<f64, Error> {
    let lhs = eval_expr(lhs, env);
    let rhs = eval_expr(rhs, env);
    // if any of the two arguments is close enough to zero, return it
    if let Ok(vl) = lhs {
        if vl.abs() < std::f64::EPSILON {
            return Ok(vl);
        }
    }
    if let Ok(vr) = rhs {
        if vr.abs() < std::f64::EPSILON {
            return Ok(vr);
        }
    }
    // otherwise, perform the multiplication
    Ok(lhs? * rhs?)
}

fn eval_expr(expr: &Expr, env: &HashMap<String, f64>) -> Result<f64, Error> {
    let span = expr.span();
    match expr {
        Expr::Num(x, _) => Ok(*x),
        Expr::Neg(x, _) => Ok(-eval_expr(x, env)?),
        Expr::Fac(x, span) => {
            let val = eval_expr(x, env)?;
            let val_int = val.round() as u64;
            if val < 0. {
                Err(Error::FactorialNeg(*span))
            } else if (val - val_int as f64).abs() > std::f64::EPSILON {
                Err(Error::FactorialFloat(*span))
            } else {
                Ok((1..=val_int).map(|x| x as f64).product())
            }
        }
        Expr::Add(lhs, rhs, _) => Ok(eval_expr(lhs, env)? + eval_expr(rhs, env)?),
        Expr::Sub(lhs, rhs, _) => Ok(eval_expr(lhs, env)? - eval_expr(rhs, env)?),
        Expr::IMul(lhs, rhs, _) => {
            // check if two numbers are implicitly multiplied
            match **rhs {
                Expr::Num(_, _) => match **lhs {
                    Expr::Num(_, _) => return Err(Error::ImpMulNumNum(lhs.span(), rhs.span())),
                    _ => return Err(Error::ImpMulRhsNum(lhs.span(), rhs.span())),
                },
                _ => {}
            };
            // otherwise perform the multiplication
            Ok(custom_mul(lhs, rhs, env)?)
        }
        Expr::Mul(lhs, rhs, _) => Ok(custom_mul(lhs, rhs, env)?),
        Expr::Div(lhs, rhs, _) => {
            let res = eval_expr(lhs, env)? / eval_expr(rhs, env)?;
            if res.is_finite() {
                Ok(res)
            } else {
                Err(Error::DivByZero(span))
            }
        }
        Expr::Pow(lhs, rhs, _) => Ok(eval_expr(lhs, env)?.powf(eval_expr(rhs, env)?)),
        Expr::Ident(name, _) => {
            if let Some(cnst) = env.get(name) {
                // look for user-defined constants
                Ok(*cnst)
            } else {
                if let Some(cnst) = PREDEFINED_CONSTANTS.get(name) {
                    // look for predefined constants
                    Ok(*cnst)
                } else {
                    Err(Error::DefMissing(span, name.clone()))
                }
            }
        }
    }
}

fn names_in_expr(expr: &Expr) -> HashSet<String> {
    match expr {
        // base cases
        Expr::Num(_, _) => HashSet::new(),
        Expr::Ident(name, _) => HashSet::from([name.to_owned()]),
        // unary recursive cases
        Expr::Neg(expr, _) | Expr::Fac(expr, _) => names_in_expr(expr),
        // binary recursive cases
        Expr::Add(expr1, expr2, _)
        | Expr::Sub(expr1, expr2, _)
        | Expr::Mul(expr1, expr2, _)
        | Expr::IMul(expr1, expr2, _)
        | Expr::Div(expr1, expr2, _)
        | Expr::Pow(expr1, expr2, _) => &names_in_expr(expr1) | &names_in_expr(&expr2),
    }
}

fn topological_sort(
    graph: &HashMap<String, HashSet<String>>,
    definitions: &HashMap<String, Expr>,
) -> Result<VecDeque<String>, Error> {
    // https://en.wikipedia.org/wiki/Topological_sorting#Depth-first_search
    let n = graph.len();
    let mut l: VecDeque<String> = VecDeque::with_capacity(n);
    let mut temporary: Vec<String> = Vec::with_capacity(n);
    let mut permanent: HashSet<String> = HashSet::with_capacity(n);
    let mut unmarked: HashSet<String> = HashSet::from_iter(graph.keys().cloned());
    while !unmarked.is_empty() {
        topological_visit(
            &unmarked.iter().next().unwrap().clone(),
            &mut permanent,
            &mut temporary,
            &mut unmarked,
            &mut l,
            &definitions,
            &graph,
        )?;
    }
    Ok(l)
}
fn topological_visit(
    node: &String,
    permanent: &mut HashSet<String>,
    temporary: &mut Vec<String>,
    unmarked: &mut HashSet<String>,
    l: &mut VecDeque<String>,
    definitions: &HashMap<String, Expr>,
    graph: &HashMap<String, HashSet<String>>,
) -> Result<(), Error> {
    if permanent.contains(node) {
        return Ok(());
    }
    if let Some(pos) = temporary.iter().position(|n| n == node) {
        let cycle = temporary[pos..].to_vec();
        return Err(Error::DefCircular(
            cycle
                .iter()
                .cycle()
                .zip(cycle.iter().cycle().skip(1))
                .map(|(node, depends_on)| {
                    (
                        node.to_owned(),
                        definitions.get(node).unwrap().span(),
                        depends_on.to_owned(),
                    )
                })
                .take(cycle.len())
                .collect(),
        ));
    }

    temporary.push(node.to_string());
    // if graph.get returns None, node is an undefined identifier
    if let Some(nbrs) = graph.get(node){
        for m in nbrs {
            topological_visit(m, permanent, temporary, unmarked, l, definitions, graph)?;
        }
    } 
    
    temporary.pop();

    permanent.insert(node.to_string());
    unmarked.remove(node);
    l.push_back(node.to_string());
    Ok(())
}

fn resolve_const_definitions(prog: Program) -> Result<Program1, Error> {
    let mut graph = HashMap::with_capacity(prog.len());
    let mut definitions: HashMap<String, Expr> = HashMap::new();
    let mut prints = vec![];
    let mut env = HashMap::new();

    // add predefined definitions to the dependency graph
    for cnst in (*PREDEFINED_CONSTANTS).keys() {
        graph.insert(cnst.to_owned(), HashSet::new());
    }
    // find the set of names that each definition depends on
    for stmt in prog {
        match stmt {
            Stmt::Definition(name, expr) => {
                graph.insert(name.to_owned(), names_in_expr(&expr));
                let span = expr.span();
                if let Some(_) = definitions.insert(name.to_owned(), expr) {
                    return Err(Error::DefMultiply(span, name.to_owned()));
                };
            }
            Stmt::Print(expr, c) => prints.push(Stmt::Print(expr, c)),
        }
    }

    // topologically sort the dependencies or detect a cycle
    let nodes = topological_sort(&graph, &definitions)?;

    // resolve dependencies in topological order
    for name in nodes
        .iter()
        // filter out predefined constants
        .filter(|n| !PREDEFINED_CONSTANTS.contains_key(*n))
    {
        if let Some(expr) = definitions.get(name){
            // evaluate the expression:
            // this must be possible, since definitions are now topologically ordered
            let res = eval_expr(expr, &env)?;
            // add the resolved definition to the environment
            env.insert(name.to_owned(), res);
        }
    }

    // return the resolved definitions along with other statements
    Ok((prints, env))
}

fn debug_run(prog: Program, env: HashMap<String, f64>, _counter: i64) {
    println!("DEFINITIONS: -----------");
    for (k, v) in &env {
        println!("{} = {}", k, v)
    }
    println!("PRINTS: ----------------");
    for stmt in prog {
        match stmt {
            Stmt::Print(expr, c) => println!("{} >>> {:#?}", c, eval_expr(&expr, &env)),
            _ => {}
        }
    }
}

pub fn main() {
    let name = "../test/test1.tex";
    let src = include_str!("../test/test1.tex");
    let p0 = handle_errs(parse_main(src), src, name);
    let (p1, env) = handle_errs(resolve_const_definitions(p0), src, name);
    debug_run(p1, env, 0);
}
