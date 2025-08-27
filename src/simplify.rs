use std::collections::HashSet;

use crate::{
    ast::{cnst, sexpr_to_expr, sval_to_val, PredefinedFunction, SExpr, SVal, Val}, differentiate::substitute, error::{Error, SpanInfo}, lookup_env, predefined::{unary_antiderivative}, utils::Either, Env, Expr
};

/// The rules to simplify expressions with.
/// Order matters! 
/// Rules that can be expected to remove larger chunks of 
/// the expression tree and which are more likely to be applicable
/// should tend to be higher up this list.
const RULES: [fn(SExpr, &Env, &HashSet<String>) -> SExpr; 10] = [
    absorbing_element,
    neutral_element,
    fix_assoc,
    constant_fold,
    combine,
    bounds_make_it_trivial,
    annihilating_ops,
    shift_neg_out_of_mul,
    trivial,
    analytic_integrals,
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
fn pair_reduce(
    reductions: &[fn(&SExpr, &SExpr) -> Option<Option<SExpr>>],
    sexprs: &mut Vec<SExpr>,
) {
    let apply_reduction = |reduced, i, j, sexprs: &mut Vec<SExpr>| {
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
                    apply_reduction(reduced, i, j, sexprs);
                    return;
                }
                if let Some(reduced) = reduction(&sexprs[j], &sexprs[i]) {
                    apply_reduction(reduced, i, j, sexprs);
                    return;
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
fn neutral_element(sexpr: SExpr, _: &Env, _: &HashSet<String>) -> SExpr {
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
/// - 0 / x = 0
fn trivial(sexpr: SExpr, _: &Env, _: &HashSet<String>) -> SExpr {
    match sexpr {
        SExpr::Pow(_, box SExpr::Const(SVal::Int(0))) => SExpr::Const(SVal::Int(1)),
        SExpr::Div(box a, box b) if a == b => SExpr::Const(SVal::Int(1)),
        SExpr::Div(box SExpr::Const(zero), _) if zero.snap() == SVal::Int(0) => {
            SExpr::Const(SVal::Int(0))
        }
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
                    (&ref a, &SExpr::Div(box ref num, box ref den)) if *a == *den => {
                        Some(Some(num.clone()))
                    }
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
/// - nested structure, e.g. a sum inside a sum, which should be flattened
fn fix_assoc(sexpr: SExpr, _: &Env, _: &HashSet<String>) -> SExpr {
    match sexpr {

        // REMOVE DEGENERATE CASES
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
        
        // FLATTEN NESTED SUMS AND PRODUCTS 
        SExpr::Mul(sexprs) 
        // if any immediate subexpression of a product is a product, lift it to the outer level
        if sexprs.iter().any(|se| if let SExpr::Mul(_) = se {true} else {false}) => {
            let mut res = vec![];
            for se in sexprs{
                if let SExpr::Mul(elems) = se{
                    res.extend(elems);
                } else {
                    res.push(se);
                }
            }
            SExpr::Mul(res)
        },
        SExpr::Add(sexprs) 
        // if any immediate subexpression of a sum is a sum, lift it to the outer level
        if sexprs.iter().any(|se| if let SExpr::Add(_) = se {true} else {false}) => {
            let mut res = vec![];
            for se in sexprs{
                if let SExpr::Add(elems) = se{
                    res.extend(elems);
                } else {
                    res.push(se);
                }
            }
            SExpr::Add(res)
        }

        // ENFORCE ORDER
        SExpr::Add(mut sexprs) if !sexprs.is_sorted() => {
            sexprs.sort_unstable();
            SExpr::Add(sexprs)
        },
        SExpr::Mul(mut sexprs) if !sexprs.is_sorted() => {
            sexprs.sort_unstable();
            SExpr::Mul(sexprs)
        },

        _ => sexpr,
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
    match sexpr {
        SExpr::Add(mut exprs) => {
            pair_reduce(
                &[|a, b| match (a, b) {
                    // case for x + x = 2x
                    (lhs, rhs) if *lhs == *rhs => {
                        if let SExpr::Mul(ll) = lhs{
                            // if the summands are already products, prepend a factor of 
                            // two to one of them
                            let mut res = vec![cnst(2)];
                            res.extend_from_slice(ll);
                            Some(Some(SExpr::Mul(res)))
                        } else {
                            Some(Some(SExpr::Mul(vec![cnst(2), lhs.clone()])))
                        }
                    },
                    // x + 3x = 4x
                    // -x + 3x = 2x
                      (lhs,  &SExpr::Mul(ref rhs)) if 
                        rhs.len() == 2 &&
                        let Some(SExpr::Const(fact)) = rhs.first() && 
                        let Some(elem) = rhs.last() 
                    => {
                        // x + 3x case
                        if let Some(new_factor) = &SVal::Int(1) + fact && *lhs == *elem {
                            Some(Some(SExpr::Mul(vec![SExpr::Const(new_factor), elem.clone()])))
                        } else 
                        // -x + 3x = 2x case
                        if let Some(new_factor) = fact - &SVal::Int(1) 
                            && let SExpr::Neg(box inner) = lhs
                            && *inner == *elem {
                                Some(Some(SExpr::Mul(vec![SExpr::Const(new_factor), elem.clone()])))
                        } else {
                            None
                        }
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
                    // case for  5xy - 2xy = 3xy
                    (&SExpr::Mul(ref lhs), &SExpr::Mul(ref rhs)) if 
                    // if both products have a constant factor
                    let Some(SExpr::Neg(box SExpr::Const(vl))) = lhs.first() && 
                    let Some(SExpr::Const(vr)) = rhs.first() && 
                    let Some(factor) = vr - vl &&
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
        }
        SExpr::Mul(mut exprs) => {
            pair_reduce(
                &[|a, b| match (a, b) {
                    // case for x * x^a = x^(1 + a)
                    (lhs, &SExpr::Pow(ref base, ref exp)) if *lhs == **base => {
                        Some(Some(SExpr::Pow(
                            Box::new(*base.clone()),
                            Box::new(SExpr::Add(vec![SExpr::Const(SVal::Int(1)), *exp.clone()])),
                        )))
                    }
                    // case for x^a * x^b = x^(a+b)
                    (&SExpr::Pow(ref lbase, ref lexp), &SExpr::Pow(ref rbase, ref rexp))
                        if **lbase == **rbase =>
                    {
                        Some(Some(SExpr::Pow(
                            Box::new(*lbase.clone()),
                            Box::new(SExpr::Add(vec![*lexp.clone(), *rexp.clone()])),
                        )))
                    }
                    // case for x * x = x^2
                    (lhs, rhs) if *lhs == *rhs => Some(Some(SExpr::Pow(
                        Box::new(lhs.clone()),
                        Box::new(SExpr::Const(SVal::Int(2))),
                    ))),
                    _ => None,
                }],
                &mut exprs,
            );
            SExpr::Mul(exprs)
        }
        _ => sexpr,
    }
}

/// Fold constants
fn constant_fold(sexpr: SExpr, env: &Env, fo: &HashSet<String>) -> SExpr {
    match sexpr {
        SExpr::Const(_) => sexpr,
        SExpr::Ident(name) => {
            SExpr::Ident(name)
        }
        SExpr::FnApp(fn_name, sexprs) => {
            // recurse to all arguments
            let args: Vec<SExpr> = sexprs
                .into_iter()
                .map(|arg| constant_fold(arg, env, fo))
                .collect();

            // otherwise, return the function with potentially partially folded arguments
            SExpr::FnApp(fn_name, args)
        }
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
            pair_reduce(
                &[|a, b| match (a, b) {
                    (SExpr::Const(ref l), SExpr::Const(ref r)) if let Some(res) = l + r => {
                        Some(Some(SExpr::Const(res)))
                    }
                    _ => None,
                }],
                &mut sexprs,
            );
            SExpr::Add(sexprs)
        }
        // SExpr::Mul(ref sexprs) if sexprs.len() >= 2 => match &sexprs[0..2] {
        //     [SExpr::Const(ref l), SExpr::Const(ref r)] if let Some(res) = l * r => {
        //         let mut res = vec![SExpr::Const(res)];
        //         res.extend_from_slice(&sexprs[2..]);
        //         // res.sort();
        //         SExpr::Mul(res)
        //     }
        //     _ => sexpr,
        // },
        SExpr::Mul(mut sexprs) => {
            pair_reduce(
                &[|a, b| match (a, b) {
                    (SExpr::Const(ref l), SExpr::Const(ref r)) if let Some(res) = l * r => {
                        Some(Some(SExpr::Const(res)))
                    }
                    _ => None,
                }],
                &mut sexprs,
            );
            SExpr::Mul(sexprs)
        }
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
        _ => sexpr,
    }
}

/// Try to evaluate a subset of integrals with analytic solutions
fn analytic_integrals(sexpr: SExpr, env: &Env, fo: &HashSet<String>) -> SExpr {
    // let bound: HashSet<&String> = HashSet::from_iter(env.keys().chain(PREDEFINED.keys()));
    match &sexpr{
        SExpr::Int(
            box lower,
            box ref upper, 
            ref int_var,
            box ref body
        ) 
        => {
            // compute the antiderivative
            if let Some(anti) = antiderivative(body.clone(), env, fo, int_var){
                let mut f_upper = anti.clone();
                sexpr_substitute_ident(&mut f_upper, int_var, &constant_fold(upper.clone(), env, fo));
                let mut f_lower  = anti;
                sexpr_substitute_ident(&mut f_lower, int_var, &constant_fold(lower.clone(), env, fo));
                return SExpr::Add(vec![
                    f_upper,
                    SExpr::Neg(Box::new(f_lower))
                ])
            } 
        },
        _ => {}
    }
    sexpr
}

fn antiderivative(
    sexpr: SExpr,
    env: &Env,
    fo: &HashSet<String>,
    int_var: &String,
) -> Option<SExpr> {
    // ∫ a dx = ax
    // catch cases where the integration variable is definitely not contained 
    // in the expression here, so a useful antiderivative is reported even
    // if the derivation of the antiderivative would fail for some other reason 
    // in a subterm due to conservative estimations
    if !sexpr_contains_ident(&sexpr, int_var){
        return Some(SExpr::Ident(int_var.to_owned()) * sexpr)
    }

    match sexpr {
        // ∫ c dx = cx
        SExpr::Const(sval) if sval.is_numeric() => Some(SExpr::Mul(vec![
            SExpr::Const(sval),
            SExpr::Ident(int_var.to_string()),
        ])),
        // if n is just a function that is not applied, there is nothing to be done
        SExpr::Const(_) => None,
        // ∫ a dx = ax if a!=x else x^2/2
        SExpr::Ident(name) => {
            if name == *int_var{
                // if the name is the integration variable we have 
                // ∫ x dx = x^2/2
                Some(SExpr::Ident(int_var.to_string()).pow(cnst(2)) / cnst(2))
            } else {
                // otherwise the name is a constant with respect to x and 
                // ∫ a dx = ax
                Some(SExpr::Ident(name) * SExpr::Ident(int_var.to_string()))
            }
        }
        // recursive case:
        // move the negation out of the integral
        // ∫ - f(x) dx =  - ∫ f(x) dx
        SExpr::Neg(box sexpr) => {
            if let Some(inner) = antiderivative(sexpr, env, fo, int_var) {
                Some(SExpr::Neg(Box::new(inner)))
            } else {
                None
            }
        }
        // recursive case:
        // distribute this function over sums
        // ∫ f(x) + g(x) dx = ∫ f(x) dx + ∫ g(x) dx
        SExpr::Add(sexprs) => {
            let res = sexprs
                .into_iter()
                .map(|sexpr| antiderivative(sexpr, env, fo, int_var))
                .collect();
            if let Some(res) = res {
                Some(SExpr::Add(res))
            } else {
                None
            }
            // Some(SExpr::Add(res))
        },
        //      ∫ f(x) dx depends on f
        // also ∫ f(y) dx = x f(y)
        SExpr::FnApp(fn_name, sexprs) => {
            if sexprs.len() == 1 && (!fo.contains(&fn_name)) {
                // if a unary function is directly applied to x
                if let SExpr::Ident(arg) = &sexprs[0]
                    && *arg == *int_var
                {
                    // look up the the antiderivative if the function is a prebuilt function
                    // the antiderivative of which is known
                    return unary_antiderivative(&fn_name, sexprs);
                }
            }
            if !sexprs.iter().any(|n| sexpr_contains_ident(&n, int_var)){
                // if the arguments do not contain the integration variable, 
                // the function application is a constant wrt. the integration variable
                // so the `∫ f(y) dx = x f(y)` case applies:
                // keep the funciton application unchanged but multiply with x
                Some(SExpr::FnApp(fn_name, sexprs) * SExpr::Ident(int_var.to_string()))
            } else {
                // otherwise integration fails
                None
            }
        }
        // ∫ n/x dx = n ln(x)
        // where n does not contain x as an identifier
        SExpr::Div(box n, box ref x @ SExpr::Ident(ref x_name))
            if !sexpr_contains_ident(&n, int_var) && *x_name == *int_var => 
            Some(n * x.pow(cnst(2)).sqrt().unary(r"\ln")),
        // ∫ f(x)/n dx = (∫ f(x) dx )/n
        // where n does not contain x as an identifier
        SExpr::Div(box f_x, box n)
            if !sexpr_contains_ident(&n, int_var) &&
            let Some(f_x_anti) = antiderivative(f_x.clone(), env, fo, int_var) => 
            Some(cnst(1)/n * f_x_anti),
        // ∫ x^n dx = x^(n+1)/(n+1) for n != 1 
        SExpr::Pow(box ref x @ SExpr::Ident(ref x_name), box n) 
            if !sexpr_contains_ident(&n, int_var) && *x_name == *int_var => 
            {
                if let Ok(val) = sexpr_eval(&n, env, fo){
                    if val.is_near(-1){
                        // exception: to the power of minus one: same as 1/x
                        Some(n * x.pow(cnst(2)).sqrt().unary(r"\ln"))
                    } else {
                        // all other powers: x^(n+1)/(n+1)
                        Some(x.pow(n.clone() + cnst(1)) / (n + cnst(1)))
                    }
                } else {
                    // could not evaluate n: 
                    // since we don't statically know if n is -1 or not we do not reduce the term
                    None
                }
            },
        // ∫ x^(1/n) dx = n/(n+1) x^((n+1)/n)
        SExpr::Root(box n, box ref x @ SExpr::Ident(ref x_name)) 
            if !sexpr_contains_ident(&n, int_var) && *x_name == *int_var => 
            {
                if let Ok(val) = sexpr_eval(&n, env, fo){
                    if val.is_near(-1){
                        // exception: to the power of minus one: same as 1/x
                        Some(n * x.pow(cnst(2)).sqrt().unary(r"\ln"))
                    } else {
                        // all other roots: n/(n+1) x^((n+1)/n)
                        Some( n.clone()/(n.clone() + cnst(1)) * x.pow((n.clone() + cnst(1)) / n))
                    }
                } else {
                    // could not evaluate n: 
                    // since we don't statically know if n is -1 or not we do not reduce the term
                    None
                }
            },
        // antiderivatives of the Gamma function are not implemented
        SExpr::Fac(_) => None,
        
        // There is no general rule for products and integration by parts is tricky, 
        // but constants can be factored out:
        // ∫ g(y) f(x) dx = g(y)  ∫ f(x) dx
        SExpr::Mul(sexprs) => {
            // look for constants in the product and pull them out of the integral
            let mut consts = vec![];
            let mut depends = vec![];
            for sexpr in &sexprs{
                if !sexpr_contains_ident(sexpr, int_var){
                    consts.push(sexpr.clone())
                } else {
                    if let Some(res) = antiderivative(sexpr.clone(), env, fo, int_var){
                        depends.push(res);
                    } else {
                        return None
                    }
                }
            };
            // if at most one factor depending on the integration variable remains, 
            // the antiderivativce of which was found, assemble the entire 
            // product and return it
            if depends.len() <= 1 {
                consts.extend(depends);
                Some(SExpr::Mul(consts))
            } else {
                // otherwise there is a product of terms depending on the integration
                // variable and integration by parts or a similar technique would
                // have to be applied
                None
            }
        },
        SExpr::Sum(box body, loop_var, lower, upper) => {
            if loop_var != *int_var {
                if let Some(inner) = antiderivative(body.clone(), env, fo, int_var) {
                    // if the integration variable is not shadowed by the loop variable,
                    // distribute across the sum
                    Some(SExpr::Sum(Box::new(inner), loop_var, lower, upper))
                } else {
                    None
                }
            } else {
                // otherwise the summation is constant wrt. the integration variable
                // and can be treated as a constant, so ∫ c dx = cx applies
                Some(SExpr::Ident(int_var.to_owned()) * SExpr::Sum(Box::new(body), loop_var, lower, upper))
            }
        },
        SExpr::Prod(box body, loop_var, lower, upper) => {
            // if the integration variable is shadowed by the loop variable, treat the term as a constant.
            if loop_var == *int_var{
                Some(SExpr::Ident(int_var.to_owned()) * SExpr::Prod(Box::new(body), loop_var, lower, upper))
            } else {
                // otherwise, this term is taken care of by the rule concerning terms that do not 
                // contain the integration variable, or it cannot be simplified since products 
                // are tricky to symbolically integrate
                None
            }
        },
        // SExpr::Int(sexpr, sexpr1, _, sexpr2) => todo!(),
        _ => None,
    }
}

/// Implement capture-free substitution of an identifier with an [`SExpr`].
/// This just recurses to positions with identifiers, except inside of loops or integrations
/// with shadowing binders (where the binder matches `from`).
fn sexpr_substitute_ident(sexpr: &mut SExpr, from: &String, to: &SExpr) {
    match sexpr {
        SExpr::Const(_) => {}
        SExpr::Ident(name) => {
            if *name == *from {
                *sexpr = to.clone();
            }
        }
        SExpr::FnApp(_, sexprs) => {
            sexprs
                .into_iter()
                .for_each(|se| sexpr_substitute_ident(se, from, to));
        }
        SExpr::Neg(sexpr) => sexpr_substitute_ident(sexpr, from, to),
        SExpr::Add(sexprs) => sexprs
            .into_iter()
            .for_each(|se| sexpr_substitute_ident(se, from, to)),
        SExpr::Mul(sexprs) => sexprs
            .into_iter()
            .for_each(|se| sexpr_substitute_ident(se, from, to)),
        SExpr::Div(sexpr, sexpr1) => {
            sexpr_substitute_ident(sexpr, from, to);
            sexpr_substitute_ident(sexpr1, from, to);
        }
        SExpr::Pow(sexpr, sexpr1) => {
            sexpr_substitute_ident(sexpr, from, to);
            sexpr_substitute_ident(sexpr1, from, to);
        }
        SExpr::Root(sexpr, sexpr1) => {
            sexpr_substitute_ident(sexpr, from, to);
            sexpr_substitute_ident(sexpr1, from, to);
        }
        SExpr::Fac(sexpr) => sexpr_substitute_ident(sexpr, from, to),
        // if the identifier is shadowed by a loop variable, don't replace it
        SExpr::Sum(sexpr, loop_var, _, _) => {
            if *loop_var != *from {
                sexpr_substitute_ident(sexpr, from, to)
            }
        },
        SExpr::Prod(sexpr, loop_var, _, _) => {
            // if the identifier is shadowed by a loop variable, don't replace it
            if *loop_var != *from {
                sexpr_substitute_ident(sexpr, from, to)
            }
        },
        SExpr::Int(sexpr, sexpr1, int_var, sexpr2) => {
            // if the identifier is shadowed by an integration variable, don't replace it
            if *int_var != *from{
                sexpr_substitute_ident(sexpr, from, to);
                sexpr_substitute_ident(sexpr1, from, to);
                sexpr_substitute_ident(sexpr2, from, to);
            }
        }
    }
}

/// Check if the [`SExpr`] contains the given identifier, ignoring occurences due to a shadowing binder
fn sexpr_contains_ident(sexpr: &SExpr, contains: &String) -> bool {
    match sexpr {
        // base cases
        SExpr::Const(_) => false,
        SExpr::Ident(x) => *x == *contains,
        // recurse over single argument
        SExpr::Neg(box sexpr) => sexpr_contains_ident(sexpr, contains),
        SExpr::Fac(sexpr) => sexpr_contains_ident(sexpr, contains),
        SExpr::Sum(sexpr, loop_var, _, _) => {
            if *loop_var != *contains{
                sexpr_contains_ident(sexpr, contains)
            } else {
                false
            }
        },
        SExpr::Prod(sexpr, loop_var, _, _) => {
            if *loop_var != *contains{
                sexpr_contains_ident(sexpr, contains)
            } else {
                false
            }
        },
        // recurse over two arguments
        SExpr::Div(sexpr, sexpr1) => {
            sexpr_contains_ident(sexpr, contains) || sexpr_contains_ident(sexpr1, contains)
        }
        SExpr::Pow(sexpr, sexpr1) => {
            sexpr_contains_ident(sexpr, contains) || sexpr_contains_ident(sexpr1, contains)
        }
        SExpr::Root(sexpr, sexpr1) => {
            sexpr_contains_ident(sexpr, contains) || sexpr_contains_ident(sexpr1, contains)
        }
        // recurse over three arguments
        SExpr::Int(lower, upper, int_var, body) => {
            if *int_var != *contains{
                sexpr_contains_ident(lower, contains)
                || sexpr_contains_ident(upper, contains)
                || sexpr_contains_ident(body, contains)
            } else {
                false
            }
        }
        // recurse over vector of arguments
        SExpr::FnApp(_, sexprs) => sexprs.iter().any(|se| sexpr_contains_ident(se, contains)),
        SExpr::Add(sexprs) => sexprs.iter().any(|se| sexpr_contains_ident(se, contains)),
        SExpr::Mul(sexprs) => sexprs.iter().any(|se| sexpr_contains_ident(se, contains)),
    }
}

/// Evaluate an [`SExpr`] if possible. Evaluation of integrals is currently unsupported here.
fn sexpr_eval(sexpr: &SExpr, env: &Env, fo: &HashSet<String>,) -> Result<SVal, ()> {
    match sexpr {
        SExpr::Const(sval) => Ok(sval.to_owned()),
        SExpr::Ident(name) => {
            if let Ok(val) = lookup_env(&name, env, SpanInfo::default()){
                let sval:SVal = val.into();
                match sval{
                    SVal::Int(i) => Ok(SVal::Int(i)),
                    SVal::Real(real) => Ok(SVal::Real(real)),
                    // function names are not included in this
                    SVal::Lambda(_) => Err(()) ,
                }
            } else {
                // undefined identifier: not a closed term
                Err(()) 
            }
        },
        SExpr::FnApp(fn_name, sexprs) => {
            // recurse to all arguments
            let args: Vec<SVal> = sexprs
                .into_iter()
                .map(|arg| sexpr_eval(arg, env, fo))
                .collect::<Result<Vec<SVal>, ()>>()?;

            // if all arguments are numeric
            if args.iter().all(|arg|arg.is_numeric()){
                // and if the function name is defined
                let func = lookup_env(&fn_name, env, SpanInfo::default()).map_err(|_| ())?;
                match func.into(){
                    SVal::Lambda(func) => {
                        match func{
                            Either::Left(predef) => {
                                // and corresponds to a predefined function
                                if !fo.contains(&predef.identifier){
                                    // and all s-values can be converted to values
                                    let vals:Vec<Val> =  args.into_iter().map(|sval|sval_to_val(sval, env)).collect::<Result<Vec<Val>, Error>>().map_err(|_| ())?;
                                    // and the parameter count matches the argument count or if the parameter count is arbitrary
                                    let count_matches = predef.param_count.iter().all(|count| *count == vals.len());
                                    if count_matches {
                                        let pred : PredefinedFunction = predef.into();
                                        // then evaluate the closure
                                        if let Ok(res) = (pred.closure)(
                                            vals,
                                            env,
                                            SpanInfo::default()
                                        ){
                                            // and return the resulting value
                                            return Ok(res.into())
                                        }
                                    }
                                }
                            },
                            Either::Right((params, box body)) => {
                                // if the function application pertains to a custom function, reify it
                                // convert arguments and body from SExpr and SVal to Expr 
                                let args:Vec<Expr> =  args.into_iter().map(|sval|sval_to_val(sval, env), ).collect::<Result<Vec<Val>, Error>>().map_err(|_| ())?.into_iter().map(|val|Expr::Const(val, SpanInfo::default())).collect();
                                let body: Expr = sexpr_to_expr(body, env, SpanInfo::default());
                                // get the expression that would result from capture-free substituting the
                                // argument expressions -> beta reduce the function body
                                // this uses `substitute` recursively to beta-reduce and alpha-rename
                                // until only the resulting expression remains
                                let substituted =
                                    params
                                        .iter()
                                        .zip(args)
                                        .try_fold(body, |acc, (param, arg)| {
                                            substitute(
                                                param,
                                                &arg,
                                                acc,
                                                env,
                                                &HashSet::from_iter(
                                                    env.keys().cloned().chain(params.iter().cloned()),
                                                ),
                                            )
                                        }).map_err(|_| ())?;
                                // now convert back to an sexpr and continue evaluating
                                return sexpr_eval(&substituted.into(), env, fo);
                            },
                        }
                    },
                    // if a number was used in place of a function, there is an error and evaluation is not possible
                    SVal::Int(_) => return Err(()),
                    SVal::Real(_) => return Err(()),
                }
            }
            // in all other cases, could not evaluate
            Err(())
        }
        SExpr::Neg(sexpr) => {
            // attempt to negate the evaluation of the subexpression
            let res = &sexpr_eval(sexpr, env, fo)?;
            if let Some(negated) = -res {
                return Ok(negated)
            } else{
                Err(())
            }
        },
        SExpr::Add(sexprs) => {
            let svals = sexprs.into_iter().map(|sexpr| sexpr_eval(sexpr, env, fo)).collect::<Result<Vec<SVal>, ()>>()?;
            let mut res = SVal::Int(0);
            for val in svals{
                res = (&res + &val).ok_or(())?;
            }
            Ok(res)
        },
        SExpr::Mul(sexprs) => {
            let svals = sexprs.into_iter().map(|sexpr| sexpr_eval(sexpr, env, fo)).collect::<Result<Vec<SVal>, ()>>()?;
            let mut res = SVal::Int(1);
            for val in svals{
                res = (&res * &val).ok_or(())?;
            }
            Ok(res)
        },
        SExpr::Div(sexpr, sexpr1) => {
            let a = sexpr_eval(sexpr, env, fo)?;
            let b = sexpr_eval(sexpr1, env, fo)?;
            Ok((&a / &b).ok_or(())?)
        },
        SExpr::Pow(sexpr, sexpr1) => {
            let a = sexpr_eval(sexpr, env, fo)?;
            let b = sexpr_eval(sexpr1, env, fo)?;
            Ok(((&a).pow(&b)).ok_or(())?)
        },
        SExpr::Root(sexpr, sexpr1) => {
            let a = sexpr_eval(sexpr, env, fo)?;
            let one_over_a = (&a).invert().ok_or(())?;
            let b = sexpr_eval(sexpr1, env, fo)?;
            Ok(((&b).pow(&one_over_a)).ok_or(())?)
        },
        SExpr::Fac(sexpr) => {
            Ok(sexpr_eval(sexpr, env, fo)?.fact().ok_or(())?)
        },
        SExpr::Sum(body, loop_var, from, to) => 
        {
            let mut res = SVal::Int(0);
            for i in *from..=*to{
                let mut reified = body.clone();
                sexpr_substitute_ident(&mut reified, loop_var, &SExpr::Const(SVal::Int(i)));
                if let Ok(summand) = sexpr_eval(&reified, env, fo){
                    res = (&res + &summand).ok_or(())?
                }
            }
            Ok(res)
        },
        SExpr::Prod(body, loop_var, from, to) => {
            let mut res = SVal::Int(1);
            for i in *from..=*to{
                let mut reified = body.clone();
                sexpr_substitute_ident(&mut reified, loop_var, &SExpr::Const(SVal::Int(i)));
                if let Ok(summand) = sexpr_eval(&reified, env, fo){
                    res = (&res * &summand).ok_or(())?
                }
            }
            Ok(res)
        },
        SExpr::Int(_, _, _, _) => {
            // TODO add integration here?
            Err(())
        }
    }
}