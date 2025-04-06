use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    error::{Error, Warning, WARNINGS}, eval_expr, Env, Expr, Program, Stmt, Val, PREDEFINED
};

pub fn names_in_expr(expr: &Expr) -> HashSet<String> {
    match expr {
        Expr::Val(val, _) => match val {
                        Val::Num(_) => HashSet::new(),
                        Val::Lambda(_, depends_on, _, _) => depends_on.clone(),
            },
        Expr::Sum(_, val, _) | Expr::Prod(_, val, _)=> {
            match val {
                Val::Num(_) => unreachable!(),
                Val::Lambda(_, depends_on, _, _) => depends_on.clone(),
            }
        },
        Expr::Ident(name, _) => HashSet::from([name.to_owned()]),
        Expr::Neg(expr, _)
            | Expr::Fac(expr, _)
            | Expr::Sqrt(expr, _)
            | Expr::Root(_, expr, _, _) => names_in_expr(expr),
        Expr::Add(expr1, expr2, _)
            | Expr::Sub(expr1, expr2, _)
            | Expr::Mul(expr1, expr2, _)
            | Expr::IMul(expr1, expr2, _)
            | Expr::Div(expr1, expr2, _)
            | Expr::Pow(expr1, expr2, _) => &names_in_expr(expr1) | &names_in_expr(&expr2),
        Expr::FnApp(name, exprs, _, _) => {
                // collect names in argument expressions
                let args_names = exprs
                    .iter()
                    .map(|expr| names_in_expr(&expr))
                    .reduce(|acc: HashSet<String>, e: HashSet<String>| &acc | &e)
                    .unwrap();
                // combine with names in function expression
                &HashSet::from([name.to_owned()]) | &args_names
            }
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
    if let Some(nbrs) = graph.get(node) {
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

pub fn resolve_const_definitions(prog: Program) -> Result<(Program, Env), Error> {
    let mut graph = HashMap::with_capacity(prog.len());
    let mut definitions: HashMap<String, Expr> = HashMap::new();
    let mut prints = vec![];
    let mut env = HashMap::new();

    // add predefined definitions to the dependency graph
    for cnst in (*PREDEFINED).keys() {
        graph.insert(cnst.to_owned(), HashSet::new());
    }
    // find the set of names that each definition depends on
    for stmt in prog {
        match stmt {
            Stmt::Definition(name, expr, span) => {
                if let Some(_) = graph.insert(name.to_owned(), names_in_expr(&expr)) {
                    WARNINGS
                        .lock()
                        .unwrap()
                        .push(Warning::PredefinedOverwritten(name.to_owned(), span));
                };
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
        .filter(|n| !PREDEFINED.contains_key(*n))
    {
        if let Some(expr) = definitions.get(name) {
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
