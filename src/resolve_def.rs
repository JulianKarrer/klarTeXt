use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    error::{Error, Warning, WARNINGS},
    eval_expr,
    utils::Either,
    Env, Expr, Program, Stmt, Val, PREDEFINED,
};

pub fn free_in_expr(expr: &Expr) -> HashSet<String> {
    match expr {
        Expr::Const(val, _) => match val {
            Val::Num(_) => HashSet::new(),
            Val::Lambda(func) => {
                match func {
                    Either::Left(_) => {
                        // predefined function don't depend on anything but their arguments
                        HashSet::new()
                    }
                    Either::Right((params, body)) => {
                        let mut inner = free_in_expr(&body);
                        // remove names bound by parameters from the free variables
                        for param in params {
                            inner.remove(param);
                        }
                        inner
                    }
                }
            }
        },
        Expr::Sum(body, loop_var, _, _) | Expr::Prod(body, loop_var, _, _) => {
            let mut inner = free_in_expr(&body);
            inner.remove(loop_var);
            inner
        }
        Expr::Ident(name, _) => HashSet::from([name.to_owned()]),
        Expr::Neg(expr, _) | Expr::Fac(expr, _) | Expr::Sqrt(expr, _) => free_in_expr(expr),
        Expr::Add(expr1, expr2, _)
        | Expr::Sub(expr1, expr2, _)
        | Expr::Mul(expr1, expr2, _)
        | Expr::IMul(expr1, expr2, _)
        | Expr::Div(expr1, expr2, _)
        | Expr::Pow(expr1, expr2, _)
        | Expr::Root(expr1, expr2, _, _) => &free_in_expr(expr1) | &free_in_expr(&expr2),
        Expr::FnApp(_, exprs, _, _) => {
            // collect names in argument expressions
            exprs.iter().map(|expr| free_in_expr(&expr)).fold(
                HashSet::new(),
                |acc: HashSet<String>, e: HashSet<String>| &acc | &e,
            )
        }
        Expr::Int(expr, expr1, dx, expr2, _) => {
            let mut inner: HashSet<String> = HashSet::new();
            inner.extend(free_in_expr(expr));
            inner.extend(free_in_expr(expr1));
            inner.extend(free_in_expr(expr2));
            inner.remove(dx);
            inner
        }
        Expr::Ddx(_, expr, _) => free_in_expr(expr),
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

pub fn resolve_const_definitions(prog: Program) -> Result<(Program, Env, HashSet<String>), Error> {
    let mut graph = HashMap::with_capacity(prog.len());
    let mut definitions: HashMap<String, Expr> = HashMap::new();
    let mut stmts = vec![];
    let mut env = HashMap::new();
    let mut fn_overwritten = HashSet::new();

    // add predefined definitions to the dependency graph
    for cnst in (*PREDEFINED).keys() {
        graph.insert(cnst.to_owned(), HashSet::new());
    }
    // find the set of names that each definition depends on
    for stmt in prog {
        match stmt {
            Stmt::Definition(name, expr, span) => {
                if let Some(_) = graph.insert(name.to_owned(), free_in_expr(&expr)) {
                    // if anything predefined was overwritten, give a warning
                    WARNINGS
                        .lock()
                        .unwrap()
                        .push(Warning::PredefinedOverwritten(name.to_owned(), span));
                    // if a predefined function was overwritten, it cannot be used in autodiff
                    if let Some(overwritten) = PREDEFINED.get(&name) {
                        match overwritten {
                            Val::Num(_) => {}
                            Val::Lambda(_) => {
                                fn_overwritten.insert(name.clone());
                            }
                        }
                    }
                };
                let span = expr.span();
                if let Some(_) = definitions.insert(name.to_owned(), expr) {
                    return Err(Error::DefMultiply(span, name.to_owned()));
                };
            }
            _ => stmts.push(stmt),
        }
    }

    // topologically sort the dependencies or detect a cycle
    let nodes = topological_sort(&graph, &definitions)?;

    // resolve dependencies in topological order
    for name in nodes {
        if let Some(expr) = definitions.get(&name) {
            // evaluate the expression:
            // this must be possible, since definitions are now topologically ordered
            let res = eval_expr(expr, &env, &fn_overwritten)?;
            // add the resolved definition to the environment
            env.insert(name.to_owned(), res);
        }
    }

    // return the resolved definitions along with other statements
    Ok((stmts, env, fn_overwritten))
}
