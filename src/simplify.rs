use std::collections::HashSet;

use itertools::Itertools;

use crate::{
    ast::{sval_to_val, SExpr, SVal}, utils::Either, Env, Expr
};

/// The rules to simplify expressions with.
/// Order matters!
const RULES: [fn(SExpr, &Env, &HashSet<String>) -> SExpr; 9] = [
    absorbing_element,
    idempotence,
    remove_degenerate_assoc,
    constant_fold,
    combine,
    bounds_make_it_trivial,
    annihilating_ops,
    shift_neg_out_of_mul,
    trivial,
];

/// Simplify an expression.
/// TODO RULES:
/// - single element sums or products are their body, with the loop variable subsituted for its single value
pub fn simplify(expr: &Expr, env: &Env, fo: &HashSet<String>) -> SExpr {
    let mut current: SExpr = expr.clone().into();
    let mut prev_hash: u64 = 0;
    loop {
        println!("SIMPLIFYING {:?}", current);
        current = apply(current, env, &RULES, fo);
        let new_hash = current.calculate_hash();
        if prev_hash == new_hash {
            break;
        };
        prev_hash = new_hash;
    }
    return current;
}

/// Traverse the [`SExpr`] AST, applying all `rules` once, bottom-up in a recursive descent.
fn apply<F: Fn(SExpr, &Env, &HashSet<String>) -> SExpr>(
    sexpr: SExpr,
    env: &Env,
    rules: &[F],
    fo: &HashSet<String>,
) -> SExpr {
    // first, recurse through the ast, applying all rules to all children
    let updated = match sexpr {
        // atomic, cannot be simplified
        SExpr::Const(_) => sexpr,
        SExpr::Ident(_) => sexpr,
        // unary recursive
        SExpr::Neg(box sexpr) => SExpr::Neg(Box::new(apply(sexpr, env, rules, fo))),
        SExpr::Fac(box sexpr) => SExpr::Fac(Box::new(apply(sexpr, env, rules, fo))),
        // binary recursive
        SExpr::Div(box sexpr, box sexpr1) => SExpr::Div(
            Box::new(apply(sexpr, env, rules, fo)),
            Box::new(apply(sexpr1, env, rules, fo)),
        ),
        SExpr::Pow(box sexpr, box sexpr1) => SExpr::Pow(
            Box::new(apply(sexpr, env, rules, fo)),
            Box::new(apply(sexpr1, env, rules, fo)),
        ),
        SExpr::Root(box sexpr, box sexpr1) => SExpr::Root(
            Box::new(apply(sexpr, env, rules, fo)),
            Box::new(apply(sexpr1, env, rules, fo)),
        ),
        // associative relations
        SExpr::Add(sexprs) => SExpr::Add(
            sexprs
                .into_iter()
                .map(|sexpr| apply(sexpr, env, rules, fo))
                .collect(),
        ),
        SExpr::Mul(sexprs) => SExpr::Mul(
            sexprs
                .into_iter()
                .map(|sexpr| apply(sexpr, env, rules, fo))
                .collect(),
        ),
        // reductions
        SExpr::Sum(box sexpr, loop_var, lower, upper) => SExpr::Sum(
            Box::new(apply(sexpr, env, rules, fo)),
            loop_var,
            lower,
            upper,
        ),
        SExpr::Prod(box sexpr, loop_var, lower, upper) => SExpr::Prod(
            Box::new(apply(sexpr, env, rules, fo)),
            loop_var,
            lower,
            upper,
        ),
        // others
        SExpr::FnApp(name, sexprs) => SExpr::FnApp(
            name,
            sexprs
                .into_iter()
                .map(|sexpr| apply(sexpr, env, rules, fo))
                .collect(),
        ),
        SExpr::Int(box lower, box upper, int_var, box body) => SExpr::Int(
            Box::new(apply(lower, env, rules, fo)),
            Box::new(apply(upper, env, rules, fo)),
            int_var,
            Box::new(apply(body, env, rules, fo)),
        ),
    };
    // then, apply the rules to the current node
    rules.iter().fold(updated, |acc, rule| rule(acc, env, fo))
}

/// Takes a slice of reduction rules over pairs of terms and applies them to each pair of expressions in `exprs` if possible.
/// This essentially lifts a reduction over a single pair of expressions to a reduction over all applicable pairs of values.
///
/// - `exprs` is mutably borrowed and changed in-place.
/// - the arguments to the reduction rule are supplied in all possible orders (a,b and b,a for every a,b in the vec)
/// 
/// If a reduction function returns:
/// - `None`, nothing changes
/// - `Some(None)` the pair of expressions annihilates and is reduced to nothing
/// - `Some(Some(expr))` the pair of expressions is reduced to the single returned expression
/// 
/// This function is O(N^2) and could be made O(N) if [`HashSet`]s were used instead of vectors of expressions,
/// but for small vectors this should be faster (?)
fn pair_reduce(reductions: &[fn(&SExpr, &SExpr) -> Option<Option<SExpr>>], sexprs: &mut Vec<SExpr>) {
    let apply_reduction = |reduced,i,j,sexprs:&mut Vec<SExpr>|{
        sexprs.remove(j);
        sexprs.remove(i);
        if let Some(insert) = reduced {
            sexprs.push(insert);
            sexprs.sort()
        }
    };
    for reduction in reductions {
        for i in 0..sexprs.len() {
            for j in (i + 1)..sexprs.len() {
                if let Some(reduced) = reduction(&sexprs[i], &sexprs[j]) {
                    apply_reduction(reduced,i,j, sexprs);
                    return
                }
                if let Some(reduced) = reduction(&sexprs[j], &sexprs[i]) {
                    apply_reduction(reduced,i,j, sexprs);
                    return
                }
            }
        }
    }
}

/// Remove operations when they have no effect, i.e. when the neutral element is applied.
/// For each operation in the AST, this function asks *on which argument(s) does this operation have no effect?*
///
/// - x + 0 = x
/// - x * 1 = x
/// - x / 1 = x
/// - 1st root of x = x
/// - x ^ 1 = x
fn idempotence(sexpr: SExpr, _: &Env, _: &HashSet<String>) -> SExpr {
    fn associative(
        mut sexprs: Vec<SExpr>,
        constructor: fn(Vec<SExpr>) -> SExpr,
        neutral_element: i64,
    ) -> SExpr {
        sexprs.retain(|expr| match expr {
            SExpr::Const(SVal::Int(x)) => *x != neutral_element,
            _ => true,
        });
        constructor(sexprs)
    }
    match sexpr {
        SExpr::Add(sexprs) => associative(sexprs, SExpr::Add, 0),
        SExpr::Mul(sexprs) => associative(sexprs, SExpr::Mul, 1),
        SExpr::Div(numerator, box SExpr::Const(SVal::Int(1))) => *numerator,
        SExpr::Root(box SExpr::Const(SVal::Int(1)), radicant) => *radicant,
        SExpr::Pow(base, box SExpr::Const(SVal::Int(1))) => *base,
        _ => sexpr,
    }
}

/// Simplify expressions where the bounds of the sum, product or integral make it trivial
/// - empty sum is zero
/// - empty product is one
/// - integrals with equal lower and upper bound is zero
fn bounds_make_it_trivial(sexpr: SExpr, _: &Env, _: &HashSet<String>) -> SExpr {
    match sexpr {
        // empty sum is zero
        SExpr::Add(summands) if summands.is_empty() => SExpr::Const(SVal::Int(0)),
        SExpr::Sum(_, _, lower, upper) if lower > upper => SExpr::Const(SVal::Int(0)),
        // empty product is one
        SExpr::Mul(factors) if factors.is_empty() => SExpr::Const(SVal::Int(1)),
        SExpr::Prod(_, _, lower, upper) if lower > upper => SExpr::Const(SVal::Int(1)),
        // integrals with equal lower and upper bound is zero
        SExpr::Int(box ref lower, box ref upper, _, _) if lower == upper => {
            SExpr::Const(SVal::Int(0))
        }
        _ => sexpr,
    }
}

/// Remove operations that are trivial due to one of the arguments.
/// - x ^ 0 = 1
/// - x / x = 1
/// - \int_a^b x^p \, dx = (1/(p+1))*b^(p+1) - (1/(p+1))*a^(p+1)
fn trivial(sexpr: SExpr, _: &Env, _: &HashSet<String>) -> SExpr {
    match sexpr {
        SExpr::Pow(_, box SExpr::Const(SVal::Int(0))) => SExpr::Const(SVal::Int(1)),
        SExpr::Div(box a, box b) if a==b => SExpr::Const(SVal::Int(1)),
        SExpr::Div(box SExpr::Const(zero), _) if zero.snap()==SVal::Int(0) => SExpr::Const(SVal::Int(0)),
        _ => sexpr,
    }
}

/// Checks for absorbing elements
/// - zero in a multiplication
fn absorbing_element(sexpr: SExpr, _: &Env, _: &HashSet<String>) -> SExpr {
    match sexpr {
        SExpr::Mul(ref sexprs)
            if sexprs.iter().any(|expr| match expr {
                SExpr::Const(SVal::Int(0)) => true,
                _ => false,
            }) =>
        {
            SExpr::Const(SVal::Int(0))
        }
        _ => sexpr,
    }
}


/// Remove subsequent applications of operators that annihilate one another
///
/// Unary minus with itself
/// - -(-x) = x
/// Roots and Powers
/// - \sqrt[y]{x^y} = x
/// - sqrt[y]{x}^y = x
/// Addition and Negation
/// - x + (-x) = 0
/// - (-x) + x = 0
/// Multiplication
/// - x * a/x = a
fn annihilating_ops(sexpr: SExpr, _: &Env, _: &HashSet<String>) -> SExpr {
    match sexpr {
        SExpr::Neg(box SExpr::Neg(box x)) => x,
        SExpr::Root(box deg1, box SExpr::Pow(box x, box deg2)) if deg1 == deg2 => x,
        SExpr::Pow(box SExpr::Root(box y1, box x), box y2) if y1 == y2 => x,
        SExpr::Add(mut exprs) => {
            pair_reduce(
                &[|a, b| match (a, b) {
                    (&ref a, &SExpr::Neg(box ref b)) if *a == *b => Some(None),
                    _ => None,
                }],
                &mut exprs,
            );
            SExpr::Add(exprs)
        }
        SExpr::Mul(mut exprs) => {
            pair_reduce(
                &[|a, b| match (a, b) {
                    (&ref a, &SExpr::Div(box ref num, box ref den)) if *a == *den => Some(Some(num.clone())),
                    _ => None,
                }],
                &mut exprs,
            );
            SExpr::Mul(exprs)
        }
        _ => sexpr,
    }
}


/// Negations in products can be reduced since only their parity matters
/// - -5x * 2y * -6i = 5x * 2y * 6i
fn shift_neg_out_of_mul(sexpr: SExpr, _: &Env, _: &HashSet<String>) -> SExpr {
    match sexpr {
        SExpr::Mul(mut sexprs)
            if sexprs.iter().any(|expr| match expr {
                SExpr::Neg(_) => true,
                _ => false,
            }) =>
        {
            // fold over factors to check if the result is positive or negative
            let positive = sexprs.iter().fold(true, |positive, expr| {
                if let SExpr::Neg(_) = expr {
                    !positive
                } else {
                    positive
                }
            });
            // mutate all inner expressions to remove SExpr::Neg wrappers
            sexprs.iter_mut().for_each(|expr| {
                if let SExpr::Neg(inner) = expr {
                    *expr = *inner.clone()
                }
            });
            // negate the entire product if applicable
            if positive {
                SExpr::Mul(sexprs)
            } else {
                SExpr::Neg(Box::new(SExpr::Mul(sexprs)))
            }
        }
        _ => sexpr,
    }
}

/// Remove degenerate cases of [`SExpr::Add`] and [`SExpr::Mul`] which contain:
/// - zero elements -> this becomes the neutral element
/// - one element -> this becomes the element, with no associative relation
fn remove_degenerate_assoc(sexpr: SExpr, _: &Env, _: &HashSet<String>) -> SExpr{
    match sexpr{
        SExpr::Add(sexprs) if sexprs.len() < 2 => match &sexprs[..] {
            [] => SExpr::Const(SVal::Int(0)),
            [elem] => elem.clone(),
            _ => unreachable!(),
        },
        SExpr::Mul(sexprs) if sexprs.len() < 2 => match &sexprs[..] {
            [] => SExpr::Const(SVal::Int(1)),
            [elem] => elem.clone(),
            _ => unreachable!(),
        },
        _ => sexpr
    }
}

/// Combine like terms.  
/// Addition and Factors:
/// - x + x = 2x
/// - x + 3x = 4x
/// - 5x + 2x = 7x
/// 
/// Multiplication and Powers:
/// - x * x = x^2
/// - x * x^a = x^(a+1)
/// - x^a * x^b = x^(a+b)
fn combine(sexpr: SExpr, _: &Env, _: &HashSet<String>) -> SExpr {
    match sexpr{
        SExpr::Add(mut exprs) => {
            pair_reduce(
                &[|a, b| match (a, b) {
                    // case for x + x = 2x
                    (lhs, rhs) if *lhs == *rhs => {
                        if let SExpr::Mul(ll) = lhs{
                            // if the summands are already products, prepend a factor of 
                            // two to one of them
                            let mut res = vec![SExpr::Const(SVal::Int(2))];
                            res.extend_from_slice(ll);
                            Some(Some(SExpr::Mul(res)))
                        } else {
                            Some(Some(SExpr::Mul(vec![SExpr::Const(SVal::Int(2)), lhs.clone()])))
                        }
                    },
                    // x + 3x = 4x
                      (lhs,  &SExpr::Mul(ref rhs)) if 
                        rhs.len() == 2 &&
                        let Some(SExpr::Const(fact)) = rhs.first() && 
                        let Some(elem) = rhs.last() && 
                        let Some(factor) = &SVal::Int(1) + fact &&
                        *lhs == *elem 
                    => {
                        Some(Some(SExpr::Mul(vec![SExpr::Const(factor), lhs.clone()])))
                    },
                    // case for  5xy + 2xy = 7xy
                    (&SExpr::Mul(ref lhs), &SExpr::Mul(ref rhs)) if 
                    // if both products have a constant factor
                    let Some(SExpr::Const(vl)) = lhs.first() && 
                    let Some(SExpr::Const(vr)) = rhs.first() && 
                    let Some(factor) = vl + vr &&
                    // and all remaining terms are equal
                    lhs.len() == rhs.len() && // necessary check since zip ignores args when one iterator has run out
                    lhs.iter().skip(1).zip(rhs.iter().skip(1)).all(|(l,r)|*l==*r)
                    => {
                        let mut res = vec![SExpr::Const(factor)];
                        res.extend_from_slice(&lhs[1..]);
                        Some(Some(SExpr::Mul(res)))
                    },
                  
                    // xy + 3xy = 4xy
                    (&SExpr::Mul(ref lhs),  &SExpr::Mul(ref rhs)) if 
                        rhs.len() >= 2 &&
                        // if left product has a constant factor
                        let Some(SExpr::Const(fact)) = rhs.first() && 
                        let rest = &rhs[1..] && 
                        let Some(factor) = &SVal::Int(1) + fact &&
                        // and all remaining terms are equal
                        lhs.len() == rest.len() &&
                        lhs.iter().zip(rest.iter()).all(|(l,r)| *l == *r)
                    => {
                        let mut res = vec![SExpr::Const(factor)];
                        res.extend_from_slice(&rhs[1..]);
                        Some(Some(SExpr::Mul(res)))
                    },
                    _ => None,
                }],
                &mut exprs,
            );
            SExpr::Add(exprs)
        },
        SExpr::Mul(mut exprs) => {
            pair_reduce(
                &[|a, b| match (a, b) {
                    // case for x * x^a = x^(1 + a)
                    (lhs, &SExpr::Pow(ref base, ref exp)) if *lhs == **base => {
                        Some(Some(SExpr::Pow(Box::new(*base.clone()), Box::new(SExpr::Add( vec![SExpr::Const(SVal::Int(1)), *exp.clone()])))))
                    },
                    // case for x^a * x^b = x^(a+b)
                    (&SExpr::Pow(ref lbase, ref lexp), 
                     &SExpr::Pow(ref rbase, ref rexp)) if **lbase == **rbase => {
                        Some(Some(SExpr::Pow(Box::new(*lbase.clone()), Box::new(SExpr::Add( vec![*lexp.clone(), *rexp.clone()])))))
                    },
                    // case for x * x = x^2
                    (lhs, rhs) if *lhs == *rhs => {
                        Some(Some(SExpr::Pow(Box::new(lhs.clone()), Box::new(SExpr::Const(SVal::Int(2))))))
                    },
                    _ => None,
                }],
                &mut exprs,
            );
            SExpr::Mul(exprs)
        },
        _ => sexpr
    }
}

/// Fold constants
fn constant_fold(sexpr: SExpr, env: &Env, fo: &HashSet<String>) -> SExpr {
    match sexpr {
        SExpr::Const(_) => sexpr,
        SExpr::Ident(_) => sexpr,
        // TODO: apply function if all arguments are constants
        SExpr::FnApp(name, sexprs) => SExpr::FnApp(
            name,
            sexprs
                .into_iter()
                .map(|arg| constant_fold(arg, env, fo))
                .collect(),
        ),
        SExpr::Neg(box SExpr::Const(ref val)) if let Some(res) = -val => SExpr::Const(res),
        // SExpr::Add(ref sexprs) if sexprs.len() >= 2 => match &sexprs[0..2] {
        //     [SExpr::Const(ref l), SExpr::Const(ref r)] if let Some(res) = l + r => {
        //         let mut res = vec![SExpr::Const(res)];
        //         res.extend_from_slice(&sexprs[2..]);
        //         // res.sort();
        //         SExpr::Add(res)
        //     }
        //     _ => sexpr,
        // },
        SExpr::Add(mut sexprs) => {
            pair_reduce(&[|a,b|match (a,b){
                (SExpr::Const(ref l), SExpr::Const(ref r)) if let Some(res) = l + r => {
                    Some(Some(SExpr::Const(res)))
                },
                _ => None
            }], &mut sexprs);
            SExpr::Add(sexprs) 
        }
        SExpr::Mul(ref sexprs) if sexprs.len() >= 2 => match &sexprs[0..2] {
            [SExpr::Const(ref l), SExpr::Const(ref r)] if let Some(res) = l * r => {
                let mut res = vec![SExpr::Const(res)];
                res.extend_from_slice(&sexprs[2..]);
                // res.sort();
                SExpr::Mul(res)
            }
            _ => sexpr,
        },
        SExpr::Div(box SExpr::Const(lhs), box SExpr::Const(rhs)) if let Some(res) = &lhs / &rhs => {
            SExpr::Const(res)
        }
        SExpr::Pow(box SExpr::Const(lhs), box SExpr::Const(rhs))
            if let Some(res) = lhs.pow(&rhs) =>
        {
            SExpr::Const(res)
        }
        SExpr::Root(box SExpr::Const(ref deg), box SExpr::Const(ref rad))
            if let Some(exp) = deg.invert() =>
        {
            match rad.pow(&exp) {
                Some(res) => SExpr::Const(res),
                None => sexpr,
            }
        }
        SExpr::Fac(box SExpr::Const(val)) if let Some(res) = val.fact() => SExpr::Const(res),
        SExpr::Sum(box SExpr::Const(ref val), _, lower, upper)
            if upper >= lower
                && let Some(res) = val * &SVal::Int(upper - lower + 1) =>
        {
            SExpr::Const(res)
        }
        SExpr::Prod(box SExpr::Const(ref val), _, lower, upper)
            if upper >= lower
                && let Some(res) = val.pow(&SVal::Int(upper - lower + 1)) =>
        {
            SExpr::Const(res)
        }
        SExpr::Int(
            box SExpr::Const(ref lower),
            box SExpr::Const(ref upper),
            _int_var,
            box SExpr::Const(ref body),
        ) if let Some(low) = (body * lower)
            && let Some(up) = (body * upper)
            && let Some(res) = (&up - &low) =>
        {
            SExpr::Const(res)
        }
        _ => sexpr
    }
}


/// Try to evaluate a subset of integrals with analytic solutions
fn try_eval_integral(sexpr: SExpr, env: &Env, fo: &HashSet<String>) -> SExpr {
    let bound : HashSet<&String> = HashSet::from_iter(env.keys());
    match &sexpr{
        SExpr::Int(
            box lower,
            box ref upper, 
            ref int_var,
            box ref body
        ) 
        // integrals are disqualified from matching here if
        // - any subexpression (body, lower bound, upper bound)
        //   contain an identifier not bound to a constant in the environment
        // - except for occurances of the integration variable in the body
        if 
        !sexpr_has_free(lower, &bound) &&
        !sexpr_has_free(upper, &bound) && 
        !sexpr_has_free(body, &(&bound | &HashSet::from([int_var]))) && 
        let SExpr::Const(low) = constant_fold(lower.clone(), env, fo) && 
        low.is_numeric() &&
        let SExpr::Const(up) = constant_fold(upper.clone(), env, fo) &&
        up.is_numeric()
        => {
            // at this point, we have matched on an integral with no free variables in the body
            // and numeric constants at the bounds

            // compute the antiderivative
            if let Some(anti) = antiderivative(body.clone(), env, fo){
                // use constant folding to try to find F(upper)
                let mut env_upper = env.clone();
                env_upper.insert(int_var.clone(), sval_to_val(up, env).unwrap());
                if let SExpr::Const(f_up) = constant_fold(anti.clone(), &env_upper, fo){
                    // use constant folding to try to find F(lower)
                    let mut env_lower = env.clone();
                    env_lower.insert(int_var.clone(), sval_to_val(low, env).unwrap());
                    if let SExpr::Const(f_low) = constant_fold(anti.clone(), &env_lower, fo){
                        // return F(upper) - F(lower)
                        return SExpr::Add(vec![
                            SExpr::Const(f_up),
                            SExpr::Neg(Box::new(SExpr::Const(f_low)))
                        ])
                    }
                }
            } 
        },
        _ => {}
    }
    sexpr
}

fn antiderivative(sexpr: SExpr, env: &Env, fo: &HashSet<String>) -> Option<SExpr> {
    todo!()
}


fn sexpr_has_free(expr: &SExpr, bound: &HashSet<&String>) -> bool {
    match expr {
        SExpr::Ident(name) => !bound.contains(name),
        SExpr::Const(val) => match val {
            SVal::Int(_) => false,
            SVal::Real(_) => false,
            SVal::Lambda(func) => {
                match func {
                    Either::Left(_) => {
                        // predefined function don't depend on anything but their arguments
                        false
                    }
                    Either::Right((params, body)) => {
                        sexpr_has_free(body, &(bound | &params.iter().collect()))
                    }
                }
            }
        },
        SExpr::Sum(body, loop_var, _, _) | 
        SExpr::Prod(body, loop_var, _, _) => {
            sexpr_has_free(body, &(bound | &HashSet::from([loop_var])))
        }
        SExpr::Neg(expr) | SExpr::Fac(expr) 
         => sexpr_has_free(expr, bound),
        SExpr::Add(exprs) | SExpr::Mul(exprs) |  SExpr::FnApp(_, exprs)
        => exprs.iter().any(|ex| sexpr_has_free(ex, bound)),
        SExpr::Div(expr1, expr2)
        | SExpr::Pow(expr1, expr2)
        | SExpr::Root(expr1, expr2) => 
        sexpr_has_free(expr1, bound) || sexpr_has_free(expr2, bound),
        SExpr::Int(lower, upper, int_var, body) => {
            sexpr_has_free(lower, bound) ||
            sexpr_has_free(upper, bound) ||
            sexpr_has_free(body, &(bound | &HashSet::from([int_var])))
        }
    }
}