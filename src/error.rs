use std::sync::Mutex;
use std::{io::Write, ops::Range, process::exit, sync::LazyLock};

use crate::utils::Either;
use crate::{io::create_sibling_file, parse::Rule, Expr, Typ, Val};
use ariadne::{ColorGenerator, Config, Label, Report, ReportKind, Source};
use itertools::Itertools;
use pest::iterators::Pair;

#[derive(Debug)]
pub enum Error {
    // PARSING ERRORS -----------------
    ParseError(SpanInfo, String),
    // SYNTAX ERRORS ------------------
    //     DEFINITIONS ----------------
    /// where, name
    DefMissing(SpanInfo, String),
    /// where, name
    DefMultiply(SpanInfo, String),
    /// Vec<name, where, depends on>
    DefCircular(Vec<(String, SpanInfo, String)>),
    //     Implicit Multiplication ----
    /// where left, where right
    ImpMulRhsNum(SpanInfo, SpanInfo),
    /// where left, where right
    ImpMulNumNum(SpanInfo, SpanInfo),
    // MATH ERRORS --------------------
    FactorialNeg(SpanInfo),
    FactorialFloat(SpanInfo),
    DivByZero(SpanInfo),
    ZerothRoot(SpanInfo),
    ComplexNumber(SpanInfo),
    // generic
    /// error type, in operation/function, where
    MathError(String, String, SpanInfo),
    // TYPE ERRORS --------------------
    /// expected, saw, where
    TypeError(String, String, SpanInfo),
    /// expected, saw, function name, where are the arguments
    FnArgs(String, String, String, SpanInfo),
    /// Fn name, expected number, saw number, where
    FnArgCount(String, usize, usize, SpanInfo),
    // REDUCTIONS ---------------------
    /// where
    ReductionNonIntegerVar(SpanInfo),
    /// where
    ReductionBodyNotNumeric(SpanInfo),
    // INTEGRALS ----------------------
    IntegralNot1D(SpanInfo),
    IntegralInternalErr(String, SpanInfo),
}

#[derive(Debug)]
pub enum Warning {
    PredefinedOverwritten(String, SpanInfo),
    // Overflow(String, SpanInfo),
}

pub static WARNINGS: LazyLock<Mutex<Vec<Warning>>> = LazyLock::new(|| Default::default());

#[derive(Debug, Copy, Clone, Default)]
pub struct SpanInfo {
    pub from: usize,
    pub to: usize,
}
impl SpanInfo {
    pub fn read_source(&self, src: &str) -> String {
        src[self.from..self.to].to_owned()
    }
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
pub fn span_merge<T: Into<SpanInfo>, U: Into<SpanInfo>>(lhs: T, rhs: U) -> SpanInfo {
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

impl Expr {
    pub fn span(&self) -> SpanInfo {
        match self {
            Expr::Const(_, span_info) => *span_info,
            Expr::Ident(_, span_info) => *span_info,
            Expr::Neg(_, span_info) => *span_info,
            Expr::Fac(_, span_info) => *span_info,
            Expr::Add(_, _, span_info) => *span_info,
            Expr::Sub(_, _, span_info) => *span_info,
            Expr::Mul(_, _, span_info) => *span_info,
            Expr::IMul(_, _, span_info) => *span_info,
            Expr::Div(_, _, span_info) => *span_info,
            Expr::Pow(_, _, span_info) => *span_info,
            Expr::Sqrt(_, span_info) => *span_info,
            Expr::Root(_, _, _, span_info) => *span_info,
            Expr::FnApp(_, _, _, span_info) => *span_info,
            Expr::Sum(_, _, span_info) => *span_info,
            Expr::Prod(_, _, span_info) => *span_info,
            Expr::Int(_, _, _, _, span_info) => *span_info,
        }
    }
}

fn ariadne_write<W: Write, A: ErrReportable>(
    err: &A,
    filename: &str,
    src: &str,
    txt_file_mode: bool,
    warning: bool,
    out: &mut W,
) {
    let mut colors = ColorGenerator::new();
    let config = Config::new()
        .with_index_type(ariadne::IndexType::Byte)
        .with_color(!txt_file_mode)
        .with_compact(false)
        .with_cross_gap(!txt_file_mode);
    let mut report_builder = Report::build(
        if warning {
            ReportKind::Warning
        } else {
            ReportKind::Error
        },
        (filename, err.span()),
    )
    .with_message(err.messages())
    .with_config(config);
    let mut order = 0;
    for (lspan, label) in err.labels() {
        report_builder = report_builder.with_label(
            Label::new((filename, lspan))
                .with_message(label)
                .with_order(order)
                .with_color(colors.next()),
        );
        order += 1;
    }
    let report: Report<'_, (&str, Range<usize>)> = report_builder.with_note(err.note()).finish();
    let mut buffer: Vec<u8> = Vec::new();
    report
        .write((filename, Source::from(src)), &mut buffer)
        .unwrap();
    // then replace regular spaces with no-break spaces (U+00A0, ' ')
    // this preserves arrows and spacing without latex and ide's interference
    let updated = String::from_utf8(buffer).unwrap().replace(" ", " ");
    write!(out, "{}", updated).unwrap();
}

pub fn handle_errs<T>(
    res: Result<T, Error>,
    src: &str,
    filename: &str,
    err_wrn_file_name: &Option<(String, String)>,
) -> T {
    let txt_file_mode = err_wrn_file_name.is_some();

    // get the output streams of where errors and warnings are written to
    let (mut err_out, mut warn_out): (Box<dyn Write>, Box<dyn Write>) =
        if let Some((err_file, wrn_file)) = err_wrn_file_name {
            // if a file is given, write to it
            (
                Box::new(create_sibling_file(filename, err_file, false)),
                Box::new(create_sibling_file(filename, wrn_file, true)),
            )
        } else {
            // otherwise, use stderr
            (Box::new(std::io::stderr()), Box::new(std::io::stderr()))
        };

    // handle warnings
    {
        let mut warnings = WARNINGS.lock().unwrap();
        for warning in warnings.iter() {
            ariadne_write(warning, filename, src, txt_file_mode, true, &mut warn_out);
        }
        warnings.clear();
        drop(warnings);
    };
    assert!(WARNINGS.lock().unwrap().is_empty());

    // handle errors
    match res {
        Ok(val) => val,
        Err(err) => {
            ariadne_write(&err, filename, src, txt_file_mode, false, &mut err_out);
            exit(1)
        }
    }
}

trait ErrReportable {
    fn span(&self) -> std::ops::Range<usize>;
    fn labels(&self) -> Vec<(Range<usize>, String)>;
    fn messages(&self) -> String;
    fn note(&self) -> String;
}

impl ErrReportable for Error {
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
            Error::ComplexNumber(span_info) => span_info.into(),
            Error::ZerothRoot(span_info) => span_info.into(),
            Error::TypeError(_, _, span_info) => span_info.into(),
            Error::FnArgs(_, _, _, span_info) => span_info.into(),
            Error::MathError(_, _, span_info) => span_info.into(),
            Error::FnArgCount(_, _, _, span_info) => span_info.into(),
            Error::ReductionBodyNotNumeric(span_info) => span_info.into(),
            Error::ReductionNonIntegerVar(span_info) => span_info.into(),
            Error::IntegralNot1D(span_info) => span_info.into(),
            Error::IntegralInternalErr(_, span_info) => span_info.into(),
        }
    }

    fn labels(&self) -> Vec<(Range<usize>, String)> {
        match self {
            Error::ParseError(_, _) => {
                vec![(self.span(), "the unexpected input is here".to_owned())]
            }
            Error::DefMissing(_, name) => vec![(
                self.span(),
                format!("The identifier {} is undefined.", name),
            )],
            Error::DefMultiply(_, name) => vec![(
                self.span(),
                format!("The identifier {} was defined at least twice", name),
            )],
            Error::DefCircular(cycle) => cycle
                .iter()
                .map(|(name, span, depends_on)| {
                    (span.into(), format!("{} depends on {}", name, depends_on))
                })
                .collect(),
            Error::ImpMulRhsNum(lhs, rhs) => vec![
                (lhs.into(), "this expression gets multiplied".to_owned()),
                (
                    rhs.into(),
                    "with a numerical literal on the right-hand side".to_owned(),
                ),
            ],
            Error::ImpMulNumNum(lhs, rhs) => vec![
                (lhs.into(), "this is a number".to_owned()),
                (rhs.into(), "this is also a number".to_owned()),
            ],
            Error::FactorialNeg(_) => vec![(
                self.span().start..self.span().end - 1,
                "This expression evaluates to a negative number.".to_owned(),
            )],
            Error::FactorialFloat(_) => vec![(
                self.span().start..self.span().end - 1,
                "This expression evaluates to a non-integer.".to_owned(),
            )],
            Error::DivByZero(_) => vec![(
                self.span(),
                "This division results in an undefined value".to_owned(),
            )],
            Error::ComplexNumber(_) => {
                vec![(self.span(), "This evaluates to a complex number".to_owned())]
            }
            Error::ZerothRoot(_) => vec![(self.span(), "This evaluates to zero".to_owned())],
            Error::TypeError(expected, _, _) => {
                vec![(self.span(), format!("expected {} here", expected))]
            }
            Error::FnArgs(_, _, _, _) => vec![(self.span(), "Wrong argument type here".to_owned())],
            Error::MathError(_, _, _) => vec![(self.span(), "Error occured here".to_owned())],
            Error::FnArgCount(_, _, _, _) => vec![(
                self.span(),
                "This function call has a wrong argument count".to_owned(),
            )],
            Error::ReductionBodyNotNumeric(_) => {
                vec![(self.span(), "this sum is not defined".to_owned())]
            }
            Error::ReductionNonIntegerVar(_) => {
                vec![(self.span(), "this is not an integer".to_owned())]
            }
            Error::IntegralNot1D(_) => vec![(self.span(), "this integral is not 1D".to_owned())],
            Error::IntegralInternalErr(_, _) => vec![(
                self.span(),
                "this integrand did not evaluate to a number".to_owned(),
            )],
        }
    }

    fn messages(&self) -> String {
        match self {
            Error::ParseError(_, _) => "Syntax Error".to_owned(),
            Error::DefMissing(_, _) => "Missing Definition".to_owned(),
            Error::DefMultiply(_, _) => "Multiply Defined Identifier".to_owned(),
            Error::DefCircular(_) => "Circular Definition".to_owned(),
            Error::ImpMulRhsNum(_, _) => {
                "Implicit multiplication with number on the right side".to_owned()
            }
            Error::ImpMulNumNum(_, _) => "Implicit multiplication of two numbers".to_owned(),
            Error::FactorialNeg(_) => "Negative argument to a factorial".to_owned(),
            Error::FactorialFloat(_) => "Non-integer argument to a factorial".to_owned(),
            Error::DivByZero(_) => "Division by Zero".to_owned(),
            Error::ComplexNumber(_) => "Complex Number encountered".to_owned(),
            Error::ZerothRoot(_) => "Zero-th Root".to_owned(),
            Error::TypeError(_, _, _) => "Type Error".to_owned(),
            Error::FnArgs(_, _, _, _) => "Argument Type Error".to_owned(),
            Error::MathError(err_type, _, _) => err_type.to_owned(),
            Error::FnArgCount(_, _, _, _) => "Wrong Argument Count".to_owned(),
            Error::ReductionBodyNotNumeric(_) => {
                "Reduction where Addition is not defined".to_owned()
            }
            Error::ReductionNonIntegerVar(_) => "Reduction over non-integers".to_owned(),
            Error::IntegralNot1D(_) => "Multidimensional Integral".to_owned(),
            Error::IntegralInternalErr(_, _) => "Internal Error in Integral".to_owned(),
        }
    }

    fn note(&self) -> String {
        match self{
            Error::ParseError(_, note) => format!("There is a syntax error in your program, which caused parsing to fail.\n{}", note),
            Error::DefMissing(_, _) => "It does not matter in which order you define identifiers using '='.\nMaybe you meant to use a predefined identifier like e or π?".to_owned(),
            Error::DefMultiply(_, _) => "Definitions using '=' are static, immutable, single assignments of a constant expression to a name.\nYou cannot bind an expression to the same name twice.".to_owned(),
            Error::DefCircular(_) => "Cyclic Definition detected.\nCompile-time recursion using the static definition '=' is not currently supported.\nDefinitions with '=' bind an expression immutably to a single name forever.\nMaybe you meant to use a mutable assignment?".to_owned(),
            Error::ImpMulRhsNum(_, _) => "Implicit multiplication is meant to be used for terms like:\n - 3x + 2y\n - 2(x+3)\nBut here, there is a number on the right-hand side of the multiplication.\nThis is an error, since it is usually unintended.".to_owned(),
            Error::ImpMulNumNum(_, _) => "Implicit multiplication is meant to be used for terms like:\n - 3x + 2y\n - 2(x+3)\nBut here it was used to multiply two numbers.\nThis is an error, since it is usually unintended.".to_owned(),
            Error::FactorialNeg(_) => "The Factorial function '!' is only defined for non-negative integers.".to_owned(),
            Error::FactorialFloat(_) => "The Factorial function '!' is only defined for non-negative integers.\nPerhaps you want to use a more general Gamma function Γ?".to_owned(),
            Error::DivByZero(_) => "You can sometimes avoid divisions by zero by rearranging terms.\nMultiplication implements short-circuiting, so 'zero times x' is always zero, even if x is undefined.\nIn that case, evaluation is left-to-right and the order of terms matters!".to_owned(),
            Error::ComplexNumber(_) => "Complex numbers are currently not supported.\nPlease avoid taking roots of negative arguments.".into(),
            Error::ZerothRoot(_) => "The zero-th root is undefined.\n`\\sqrt[0]{1}` could be argued to be any number, which is also unheplful\nCongratulations on this rare error message!".into(),
            Error::TypeError(expected, saw, _) => format!("There was a type error.\nExpected:\n\t{}\nActually supplied:\n\t{}", expected, saw),
            Error::FnArgs(expected, saw, name, _) =>  format!("The arguments to the {} function are wrong in their number or type.\nExpected:\n\t{}\nActually supplied:\n\t{}", name, expected, saw),
            Error::MathError(err_description, fn_name, _) => format!("There was a math error in a {}:\n\t- {}", fn_name, err_description),
            Error::FnArgCount(name, expected, saw, _) => format!("The function {} was called with {} arguments, but expected {}.", name, saw, expected),
            Error::ReductionBodyNotNumeric(_) => ("If a sum was used, addition is not defined on the body.\nIf a product was used, multiplication is not defined on the body.\nPlease check if the expression you sum over has a function type, which is currently unsupported.\nMaybe you used a function name 'f' instead of a function application 'f(x)'?").to_owned(),
            Error::ReductionNonIntegerVar(_) => "You attempted to sum from or to limits that do not evaluate to an integer.\nMaybe you meant to integrate instead of sum?".to_owned(),
            Error::IntegralNot1D(_) => "Currently, only definite integrals over one integration variable are supported.\nTo calculate multidimensional integrals, please nest one integral in the other to achieve the same effect.\n\nGGauss-Kronrod G7K15 quadrature is used to integrate numerically.\nhttps://arxiv.org/pdf/1003.4629".to_owned(),
            Error::IntegralInternalErr(intvar, _) => format!("The integrand did not evaluate to a number.\n Please check for errors inside.\nThe integration variable, which overwrites variables of the same name defined somewhere else, was {}.\n\nGauss-Kronrod G7K15 quadrature is used to integrate numerically.\nhttps://arxiv.org/pdf/1003.4629", intvar),
        }
    }
}

impl ErrReportable for Warning {
    fn span(&self) -> std::ops::Range<usize> {
        match self {
            Warning::PredefinedOverwritten(_, span_info) => span_info.into(),
        }
    }

    fn labels(&self) -> Vec<(Range<usize>, String)> {
        match self {
            Warning::PredefinedOverwritten(name, _) => vec![(
                self.span(),
                format!("The identifier {} is overwritten.", name),
            )],
        }
    }

    fn messages(&self) -> String {
        match self {
            Warning::PredefinedOverwritten(_, _) => format!("Predefined Identifier Overwritten"),
        }
    }

    fn note(&self) -> String {
        match self {
            Warning::PredefinedOverwritten(_, _) => String::new(),
        }
    }
}

fn rule_description(rule: Rule) -> &'static str {
    match rule {
        Rule::EOI => "end of the file",
        Rule::WHITESPACE => "whitespace",
        Rule::COMMENT => "a comment",
        Rule::IGNORE => "whitespace or a comment",
        Rule::IGNORE_NO_LF => r"whitespace or a comment with no line break (\\)",
        Rule::no_lf_statement => r"a statement with no line break (\\)",
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
        Rule::frac => r"a fraction \frac{}{}",
        Rule::keyword => r"a keyword like '\left', '\cdot' etc.",
        Rule::identifier => r"an identifier like 'x', `\pi` or 'y_{t=0}'",
        Rule::wrapped_ident => r"an identifier like 'x', `\pi` or 'y_{t=0}'",
        Rule::simple_identifier => "a simple, single letter identifier",
        Rule::latex_symbol => r"a single latex symbol, like '\pi' or '\eta'",
        Rule::subscript => "a subscript '_{ ... }'",
        Rule::nested_block => "a nested subscript",
        Rule::infix => "an infix operation (+,-,*,/,...)",
        Rule::add => "addition (+)",
        Rule::sub => "subtraction (-)",
        Rule::mul => "multiplication (*)",
        Rule::implicit => "implicit multiplication (3x, 5(y+2), ...)",
        Rule::div => r"a division (using e.g. \frac{}{})",
        Rule::pow => "exponentiation (e^x etc.)",
        Rule::prefix => "a prefix operator (like '-' in '-5')",
        Rule::neg => "a negation (prefix -)",
        Rule::postfix => "a postfix operator (like !)",
        Rule::fac => "a factorial (!)",
        Rule::sqrt => r"a square root (\sqrt{})",
        Rule::nthroot => r"some root (\sqrt[3]{}, \sqrt[\pi]{}, ...)",
        Rule::bracketed_expr => r"a bracketed expression like (...), \left( ... \right) or {...}",
        Rule::fn_app => {
            r"a function call (or an implicit multiplication like x(5+2), depending on what x is)"
        }
        Rule::fn_definition => r"a function definition",
        Rule::fn_signautre => r"a function signature",
        Rule::infinity => r"infinity (\infty)",
        Rule::sum => r"a sum (\sum_{i=0}^{15} i)",
        Rule::digit => r"a single digit",
        Rule::wrapped_digit => r"a single digit",
        Rule::prod => r"a product (\sum_{i=1}^{8} i^2)",
        Rule::reduction => r"a reduction, like a sum or product",
        Rule::newl_seperated_statemtnts => r"statements seperated by newlines (\\)",
        Rule::integral => r"a definite, 1D integral (\int_{...}^{...} ... \,dx)",
    }
}

pub fn pest_err_adapter(err: pest::error::Error<Rule>) -> Error {
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
                        positives
                            .iter()
                            .map(|r| rule_description(*r))
                            .join("\n\t- ")
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

/// Creates an Error message to use when wrong arguments where supplied to a lambda
/// `expected` is either:
/// - a list of argument types OR
/// - a single argument type, any number of arguments of which are accepted.
/// the second is useful for reduce-like overloaded functions, such as min, max
pub fn lambda_arg_err<S: ToString>(
    name: S,
    span: SpanInfo,
    xs: &[Val],
    expected: Either<Vec<Typ>, Typ>,
) -> Error {
    let expected = match expected {
        Either::Left(args) => args.iter().map(|arg| arg.name()).join(", "),
        Either::Right(arg) => format!("any number of arguments which each are a {}", arg.name()),
    };
    let saw = xs.iter().map(|arg| Typ::from(arg.into()).name()).join(",");
    Error::FnArgs(expected, saw, name.to_string(), span)
}
