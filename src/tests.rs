use crate::{
    ast::{sexpr_to_expr, SExpr},
    simplify::sexpr_eval,
    *,
};

fn _run_integral_test<T: ToString>(
    test_name: &str,
    lower: SExpr,
    upper: SExpr,
    body: SExpr,
    int_var: T,
    expected: f64,
) {
    const F64_TOLERANCE: f64 = 1e-8;
    let env: Env = HashMap::new();
    let fo: HashSet<String> = HashSet::new();

    // build expression
    let sexpr = SExpr::Int(
        Box::new(lower),
        Box::new(upper),
        int_var.to_string(),
        Box::new(body),
    );

    // simplify
    let expr = sexpr_to_expr(sexpr, &env, SpanInfo::default());
    let simplified = simplify(&expr, &env, &fo);

    // evaluate result
    let sval = match sexpr_eval(&simplified, &env, &fo) {
        Ok(v) => v,
        Err(_) => panic!(
            "{}: sexpr_eval could not evaluate expression {:?}",
            test_name, simplified
        ),
    };

    let got = sval.to_f64().unwrap_or_else(|| {
        panic!(
            "{}: sexpr_eval did not return a numeric SVal but {:?}",
            test_name, sval
        )
    });

    let approx = |a: f64, b: f64| (a - b).abs() < F64_TOLERANCE;

    if !approx(got, expected) {
        panic!(
            "{}: result mismatch\n  expr: {:?}\n  expected: {:.12e}\n  got:      {:.12e}",
            test_name, simplified, expected, got
        );
    }
}

/// Macro for creating tests of the [`antiderivative`] function that each expand to a `#[test]`
macro_rules! integral_test {
    ($name:ident, $lower:expr, $upper:expr, $body:expr, $intvar:expr, $expected:expr) => {
        #[test]
        fn $name() {
            use crate::ast::cnst;
            _run_integral_test(stringify!($name), $lower, $upper, $body, $intvar, $expected);
        }
    };
}

integral_test!(
    integral_constant_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    cnst(5.0f64),
    "x",
    5.000000000000000e+00f64
);
integral_test!(
    integral_constant_neg1_2,
    cnst(-1.0f64),
    cnst(2.0f64),
    cnst(3.0f64),
    "x",
    9.000000000000000e+00f64
);
integral_test!(
    integral_negative_linear_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    -SExpr::Ident("x".to_string()),
    "x",
    -5.000000000000000e-01f64
);
integral_test!(
    integral_negative_quadratic_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    -SExpr::Ident("x".to_string()).pow(cnst(2.0f64)),
    "x",
    -3.333333333333333e-01f64
);
integral_test!(
    integral_sum_x_plus_1_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()) + cnst(1.0f64),
    "x",
    1.500000000000000e+00f64
);
integral_test!(
    integral_sum_x_x2_0_2,
    cnst(0.0f64),
    cnst(2.0f64),
    SExpr::Ident("x".to_string()) + SExpr::Ident("x".to_string()).pow(cnst(2.0f64)),
    "x",
    4.666666666666667e+00f64
);
integral_test!(
    integral_sigma_sum_i_times_x_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Sum(
        Box::new(SExpr::Ident("i".to_string()) * SExpr::Ident("x".to_string())),
        "i".to_string(),
        1,
        3
    ),
    "x",
    3.000000000000000e+00f64
);
integral_test!(
    integral_sigma_sum_independent_0_2,
    cnst(0.0f64),
    cnst(2.0f64),
    SExpr::Sum(
        Box::new(SExpr::Ident("x".to_string()).pow(cnst(2.0f64))),
        "i".to_string(),
        0,
        2
    ),
    "x",
    8.000000000000000e+00f64
);
integral_test!(
    integral_shadow_sum_same_var_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Sum(
        Box::new(SExpr::Ident("x".to_string())),
        "x".to_string(),
        1,
        3
    ),
    "x",
    6.000000000000000e+00f64
);

integral_test!(
    integral_prod_shadowing_same_var_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Prod(
        Box::new(SExpr::Ident("x".to_string())),
        "x".to_string(),
        1,
        3
    ),
    "x",
    6.000000000000000e+00f64
);

integral_test!(
    integral_frac_x_over_2_0_2,
    cnst(0.0f64),
    cnst(2.0f64),
    SExpr::Ident("x".to_string()) / cnst(2.0f64),
    "x",
    1.000000000000000e+00f64
);

integral_test!(
    integral_n_over_x_1_e,
    cnst(1.0f64),
    cnst(std::f64::consts::E),
    cnst(2.0f64) / SExpr::Ident("x".to_string()),
    "x",
    2.000000000000000e+00f64
);
integral_test!(
    integral_n_over_x_1_2_three_n,
    cnst(1.0f64),
    cnst(2.0f64),
    cnst(3.0f64) / SExpr::Ident("x".to_string()),
    "x",
    2.079441541679836e+00f64
);

integral_test!(
    integral_x_pow_3_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).pow(cnst(3.0f64)),
    "x",
    2.500000000000000e-01f64
);
integral_test!(
    integral_x_pow_3_1_3,
    cnst(1.0f64),
    cnst(3.0f64),
    SExpr::Ident("x".to_string()).pow(cnst(3.0f64)),
    "x",
    2.000000000000000e+01f64
);

integral_test!(
    integral_sqrt_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).sqrt(),
    "x",
    6.666666666666666e-01f64
);
integral_test!(
    integral_cuberoot_0_8,
    cnst(0.0f64),
    cnst(8.0f64),
    SExpr::Root(
        Box::new(cnst(3.0f64)),
        Box::new(SExpr::Ident("x".to_string()))
    ),
    "x",
    1.200000000000000e+01f64
);

integral_test!(
    integral_sin_0_pi,
    cnst(0.0f64),
    cnst(std::f64::consts::PI),
    SExpr::Ident("x".to_string()).unary(r"\sin"),
    "x",
    2.000000000000000e+00f64
);
integral_test!(
    integral_cos_0_pi,
    cnst(0.0f64),
    cnst(std::f64::consts::PI),
    SExpr::Ident("x".to_string()).unary(r"\cos"),
    "x",
    0.000000000000000e+00f64
);
integral_test!(
    integral_tan_0_pi4,
    cnst(0.0f64),
    cnst(std::f64::consts::PI / 4.0f64),
    SExpr::Ident("x".to_string()).unary(r"\tan"),
    "x",
    3.465735902799726e-01f64
);

integral_test!(
    integral_arcsin_0_half,
    cnst(0.0f64),
    cnst(0.5f64),
    SExpr::Ident("x".to_string()).unary(r"\arcsin"),
    "x",
    1.278247915835880e-01f64
);
integral_test!(
    integral_arccos_0_half,
    cnst(0.0f64),
    cnst(0.5f64),
    SExpr::Ident("x".to_string()).unary(r"\arccos"),
    "x",
    6.575733718138602e-01f64
);
integral_test!(
    integral_arctan_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).unary(r"\arctan"),
    "x",
    4.388245731174757e-01f64
);

integral_test!(
    integral_sinh_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).unary(r"\sinh"),
    "x",
    5.430806348152437e-01f64
);
integral_test!(
    integral_cosh_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).unary(r"\cosh"),
    "x",
    1.175201193643801e+00f64
);
integral_test!(
    integral_tanh_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).unary(r"\tanh"),
    "x",
    4.337808305170380e-01f64
);

integral_test!(
    integral_ln_1_e,
    cnst(1.0f64),
    cnst(std::f64::consts::E),
    SExpr::Ident("x".to_string()).unary(r"\ln"),
    "x",
    1.000000000000000e+00f64
);
integral_test!(
    integral_lg_1_10,
    cnst(1.0f64),
    cnst(10.0f64),
    SExpr::Ident("x".to_string()).unary(r"\lg"),
    "x",
    6.09134966287073355113983972975055425935042694776700090496991595150721815712
);

integral_test!(
    integral_exp_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).unary(r"\exp"),
    "x",
    1.718281828459045e+00f64
);
integral_test!(
    integral_exp_1_2,
    cnst(1.0f64),
    cnst(2.0f64),
    SExpr::Ident("x".to_string()).unary(r"\exp"),
    "x",
    4.670774270471585e+00f64
);

integral_test!(
    integral_theta_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).unary(r"\Theta"),
    "x",
    1.000000000000000e+00f64
);

integral_test!(
    integral_phi_neg1_1,
    cnst(-1.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).unary(r"\Phi"),
    "x",
    1.0
);

integral_test!(
    integral_sin_plus_cos_0_pi,
    cnst(0.0f64),
    cnst(std::f64::consts::PI),
    SExpr::Ident("x".to_string()).unary(r"\sin") + SExpr::Ident("x".to_string()).unary(r"\cos"),
    "x",
    2.000000000000000e+00f64
);

integral_test!(
    integral_5_x2_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    cnst(5.0f64) * SExpr::Ident("x".to_string()).pow(cnst(2.0f64)),
    "x",
    1.666666666666667e+00f64
);

integral_test!(
    integral_x2_1_4,
    cnst(1.0f64),
    cnst(4.0f64),
    SExpr::Ident("x".to_string()).pow(cnst(2.0f64)),
    "x",
    2.100000000000000e+01f64
);

integral_test!(
    integral_x_neg_half_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).pow(cnst(-0.5f64)),
    "x",
    2.000000000000000e+00f64
);

integral_test!(
    integral_sigma_sum_1_to_5_x2_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Sum(
        Box::new(SExpr::Ident("x".to_string()).pow(cnst(2.0f64))),
        "i".to_string(),
        1,
        5
    ),
    "x",
    1.666666666666667e+00f64
);

integral_test!(
    integral_ln_1_3,
    cnst(1.0f64),
    cnst(3.0f64),
    SExpr::Ident("x".to_string()).unary(r"\ln"),
    "x",
    1.295836866004329e+00f64
);

integral_test!(
    integral_lg_10_100,
    cnst(10.0f64),
    cnst(100.0f64),
    SExpr::Ident("x".to_string()).unary(r"\lg"),
    "x",
    150.913496628707335511398397297505542593504269477670009049699159515072181571
);

integral_test!(
    integral_arcsin_minus_half_half,
    cnst(-0.5f64),
    cnst(0.5f64),
    SExpr::Ident("x".to_string()).unary(r"\arcsin"),
    "x",
    0.
);

integral_test!(
    integral_arctan_minus1_1,
    cnst(-1.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).unary(r"\arctan"),
    "x",
    0.000000000000000e+00f64
);

integral_test!(
    integral_phi_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).unary(r"\Phi"),
    "x",
    0.68437319018625362044311667863321670883072630629910475880
);

integral_test!(
    integral_x2_0_2pi,
    cnst(0.0f64),
    cnst(2.0f64 * std::f64::consts::PI),
    SExpr::Ident("x".to_string()).pow(cnst(2.0f64)),
    "x",
    82.6834044807995204679368401789370538726007695090269538510521016101503864465
);

integral_test!(
    integral_sin_0_pi2,
    cnst(0.0f64),
    cnst(std::f64::consts::PI / 2.0f64),
    SExpr::Ident("x".to_string()).unary(r"\sin"),
    "x",
    1.000000000000000e+00f64
);

integral_test!(
    integral_tan_0_pi6,
    cnst(0.0f64),
    cnst(std::f64::consts::PI / 6.0f64),
    SExpr::Ident("x".to_string()).unary(r"\tan"),
    "x",
    0.14384103622589046371960950299691371575175485544888052825333284267464647536
);

integral_test!(
    integral_exp_0_2,
    cnst(0.0f64),
    cnst(2.0f64),
    SExpr::Ident("x".to_string()).unary(r"\exp"),
    "x",
    6.389056098930650e+00f64
);

integral_test!(
    integral_sigma_sum_1_to_4_constant_times_x2_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Sum(
        Box::new(SExpr::Ident("x".to_string()).pow(cnst(2.0f64))),
        "i".to_string(),
        1,
        4
    ),
    "x",
    1.333333333333333e+00f64
);

integral_test!(
    integral_ln_1_2,
    cnst(1.0f64),
    cnst(2.0f64),
    SExpr::Ident("x".to_string()).unary(r"\ln"),
    "x",
    0.38629436111989061883446424291635313615100026872051050824136001898678724393
);

integral_test!(
    integral_x_pow_minus2_1_2,
    cnst(1.0f64),
    cnst(2.0f64),
    SExpr::Ident("x".to_string()).pow(cnst(-2.0f64)),
    "x",
    5.000000000000000e-01f64
);

integral_test!(
    integral_root_fourth_0_16,
    cnst(0.0f64),
    cnst(16.0f64),
    SExpr::Root(
        Box::new(cnst(4.0f64)),
        Box::new(SExpr::Ident("x".to_string()))
    ),
    "x",
    2.560000000000000e+01f64
);

// ----------------- 50 additional tests added below -----------------

integral_test!(
    integral_constant_2_5,
    cnst(2.0f64),
    cnst(5.0f64),
    cnst(7.000000000000000000e+00f64),
    "x",
    2.100000000000000000e+01f64
);
integral_test!(
    integral_negative_constant,
    cnst(-1.0f64),
    cnst(1.0f64),
    cnst(-3.000000000000000000e+00f64),
    "x",
    -6.000000000000000000e+00f64
);
integral_test!(
    integral_linear_2_4,
    cnst(2.0f64),
    cnst(4.0f64),
    cnst(3.0f64) * SExpr::Ident("x".to_string()),
    "x",
    1.800000000000000000e+01f64
);
integral_test!(
    integral_quadratic_neg1_1,
    cnst(-1.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).pow(cnst(2.0f64)),
    "x",
    6.666666666666666000e-01f64
);
integral_test!(
    integral_sum_i2_x_0_1,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Sum(
        Box::new(SExpr::Ident("i".to_string()).pow(cnst(2.0f64)) * SExpr::Ident("x".to_string())),
        "i".to_string(),
        1,
        3
    ),
    "x",
    7.000000000000000000e+00f64
);
integral_test!(
    integral_sum_x3_0_2,
    cnst(0.0f64),
    cnst(2.0f64),
    SExpr::Sum(
        Box::new(SExpr::Ident("x".to_string()).pow(cnst(3.0f64))),
        "i".to_string(),
        0,
        2
    ),
    "x",
    1.200000000000000000e+01f64
);

integral_test!(
    integral_4_over_x_1_3,
    cnst(1.0f64),
    cnst(3.0f64),
    cnst(4.0f64) / SExpr::Ident("x".to_string()),
    "x",
    4.394449154672439000e+00f64
);
integral_test!(
    integral_x_minus_half_0_1_additional,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).pow(cnst(-0.5f64)),
    "x",
    2.000000000000000000e+00f64
);
integral_test!(
    integral_root5_0_32,
    cnst(0.0f64),
    cnst(32.0f64),
    SExpr::Root(
        Box::new(cnst(5.0f64)),
        Box::new(SExpr::Ident("x".to_string()))
    ),
    "x",
    5.333333333333333111e+01f64
);
integral_test!(
    integral_sin_cos_0_pi2,
    cnst(0.0f64),
    cnst(std::f64::consts::PI / 2.0f64),
    SExpr::Ident("x".to_string()).unary(r"\sin") + SExpr::Ident("x".to_string()).unary(r"\cos"),
    "x",
    2.000000000000000000e+00f64
);
integral_test!(
    integral_2sin_0_pi,
    cnst(0.0f64),
    cnst(std::f64::consts::PI),
    cnst(2.0f64) * SExpr::Ident("x".to_string()).unary(r"\sin"),
    "x",
    4.000000000000000000e+00f64
);
integral_test!(
    integral_3cos_0_pi2,
    cnst(0.0f64),
    cnst(std::f64::consts::PI / 2.0f64),
    cnst(3.0f64) * SExpr::Ident("x".to_string()).unary(r"\cos"),
    "x",
    3.000000000000000000e+00f64
);
integral_test!(
    integral_tan_0_pi8_additional,
    cnst(0.0f64),
    cnst(std::f64::consts::PI / 8.0f64),
    SExpr::Ident("x".to_string()).unary(r"\tan"),
    "x",
    7.917359191018748000e-02f64
);
integral_test!(
    integral_arcsin_0_1_additional,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).unary(r"\arcsin"),
    "x",
    5.707963267948966000e-01f64
);
integral_test!(
    integral_arccos_0_1_additional,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).unary(r"\arccos"),
    "x",
    1.000000000000000000e+00f64
);
integral_test!(
    integral_arctan_0_2_additional,
    cnst(0.0f64),
    cnst(2.0f64),
    SExpr::Ident("x".to_string()).unary(r"\arctan"),
    "x",
    1.40957847937113081873375125374398026037729461366860643239675446913033118410
);
integral_test!(
    integral_sinh_neg1_1_additional,
    cnst(-1.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).unary(r"\sinh"),
    "x",
    0.000000000000000000e+00f64
);
integral_test!(
    integral_cosh_0_2_additional,
    cnst(0.0f64),
    cnst(2.0f64),
    SExpr::Ident("x".to_string()).unary(r"\cosh"),
    "x",
    3.626860407847019000e+00f64
);
integral_test!(
    integral_tanh_neg1_1_additional,
    cnst(-1.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).unary(r"\tanh"),
    "x",
    0.000000000000000000e+00f64
);
integral_test!(
    integral_ln_2_4_additional,
    cnst(2.0f64),
    cnst(4.0f64),
    SExpr::Ident("x".to_string()).unary(r"\ln"),
    "x",
    2.15888308335967185650339272874905940845300080616153152472408005696036173181
);
integral_test!(
    integral_lg_2_20_additional,
    cnst(2.0f64),
    cnst(20.0f64),
    SExpr::Ident("x".to_string()).unary(r"\lg"),
    "x",
    17.6012392476931286161269795645419830005282717618519555535275262033023837211
);
integral_test!(
    integral_exp_neg1_1_additional,
    cnst(-1.0f64),
    cnst(1.0f64),
    SExpr::Ident("x".to_string()).unary(r"\exp"),
    "x",
    2.350402387287602720e+00f64
);
integral_test!(
    integral_theta_1_2_additional,
    cnst(-1.0f64),
    cnst(2.0f64),
    SExpr::Ident("x".to_string()).unary(r"\Theta"),
    "x",
    2.000000000000000000e+00f64
);
integral_test!(
    integral_phi_2_2_additional,
    cnst(-2.0f64),
    cnst(2.0f64),
    SExpr::Ident("x".to_string()).unary(r"\Phi"),
    "x",
    2.0
);
integral_test!(
    integral_x_minus2_1_3_additional,
    cnst(1.0f64),
    cnst(3.0f64),
    SExpr::Ident("x".to_string()).pow(cnst(-2.0f64)),
    "x",
    6.666666666666666667e-01f64
);
integral_test!(
    integral_x_sqrt_0_2_additional,
    cnst(0.0f64),
    cnst(2.0f64),
    SExpr::Ident("x".to_string()).sqrt(),
    "x",
    1.88561808316412673173558496561293077142622916716926409756890631732097663794
);
integral_test!(
    integral_root3_1_8_additional,
    cnst(1.0f64),
    cnst(8.0f64),
    SExpr::Root(
        Box::new(cnst(3.0f64)),
        Box::new(SExpr::Ident("x".to_string()))
    ),
    "x",
    11.25
);
integral_test!(
    integral_sum_i_times_x2_additional,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Sum(
        Box::new(SExpr::Ident("i".to_string()) * SExpr::Ident("x".to_string()).pow(cnst(2.0f64))),
        "i".to_string(),
        1,
        4
    ),
    "x",
    3.333333333333333259e+00f64
);
integral_test!(
    integral_prod_const_0_1_additional,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Prod(Box::new(cnst(3.0f64)), "i".to_string(), 1, 3),
    "x",
    2.700000000000000000e+01f64
);

integral_test!(
    integral_neg_3x2_0_2_additional,
    cnst(0.0f64),
    cnst(2.0f64),
    cnst(-3.0f64) * SExpr::Ident("x".to_string()).pow(cnst(2.0f64)),
    "x",
    -8.000000000000000000e+00f64
);
integral_test!(
    integral_frac_const_mul_x_additional,
    cnst(0.0f64),
    cnst(1.0f64),
    (cnst(2.0f64) / cnst(5.0f64)) * SExpr::Ident("x".to_string()),
    "x",
    2.000000000000000000e-01f64
);
integral_test!(
    integral_x_minus3_2_4_additional,
    cnst(2.0f64),
    cnst(4.0f64),
    SExpr::Ident("x".to_string()).pow(cnst(-3.0f64)),
    "x",
    9.375000000000000000e-02f64
);
integral_test!(
    integral_2exp_1_3_additional,
    cnst(1.0f64),
    cnst(3.0f64),
    cnst(2.0f64) * SExpr::Ident("x".to_string()).unary(r"\exp"),
    "x",
    3.473451018945724000e+01f64
);
integral_test!(
    integral_2arctan_0_1_additional,
    cnst(0.0f64),
    cnst(1.0f64),
    cnst(2.0f64) * SExpr::Ident("x".to_string()).unary(r"\arctan"),
    "x",
    8.776491462349513000e-01f64
);
integral_test!(
    integral_sum_i_plus_x_additional,
    cnst(0.0f64),
    cnst(1.0f64),
    SExpr::Sum(
        Box::new(SExpr::Ident("i".to_string()) + SExpr::Ident("x".to_string())),
        "i".to_string(),
        1,
        3
    ),
    "x",
    7.500000000000000000e+00f64
);
integral_test!(
    integral_2ln_1_4_additional,
    cnst(1.0f64),
    cnst(4.0f64),
    cnst(2.0f64) * SExpr::Ident("x".to_string()).unary(r"\ln"),
    "x",
    5.090354888959125000e+00f64
);
integral_test!(
    integral_tan_0_pi12,
    cnst(0.0f64),
    cnst(std::f64::consts::PI / 12.0f64),
    SExpr::Ident("x".to_string()).unary(r"\tan"),
    "x",
    3.466823209753693014e-02f64
);
