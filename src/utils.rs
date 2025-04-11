#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Either<L, R> {
    Left(L),
    Right(R),
}
