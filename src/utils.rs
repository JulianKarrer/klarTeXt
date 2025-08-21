#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Either<L, R> {
    Left(L),
    Right(R),
}
/// If f64 distance to the next integer is below the EPSILON precision limit, round the number to an integer
pub fn snap_to_int(val: f64) -> f64 {
    if (val.round() - val).abs() < f64::EPSILON {
        // additionally, avoid -0.0
        if val.abs() < f64::EPSILON {
            0.
        } else {
            val.round()
        }
    } else {
        val
    }
}

#[derive(Clone, Copy, Debug, Default)]
/// create infinite x_i variable names
pub struct Vars {
    counter: usize,
}
impl Iterator for Vars {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        self.counter += 1;
        Some(format!(r"x_{{ {} }}", self.counter))
    }
}
