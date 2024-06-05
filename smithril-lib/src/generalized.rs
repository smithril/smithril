use core::fmt;

pub trait GeneralSort {}

pub trait GeneralTerm {}

#[derive(Debug, PartialEq, Eq)]
pub enum SolverResult {
    Sat,
    Unsat,
    Unknown,
}

impl fmt::Display for SolverResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let printable = match *self {
            SolverResult::Sat => "sat",
            SolverResult::Unsat => "unsat",
            SolverResult::Unknown => "unknown",
        };
        write!(f, "{}", printable)
    }
}

pub trait GeneralConverter<'a, S, T>
where
    S: GeneralSort,
    S: 'a,
    T: GeneralTerm,
    T: 'a,
{
    fn assert(&self, term: &T);
    fn check_sat(&self) -> SolverResult;
    fn mk_and(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bv_sort(&'a self, size: u64) -> S;
    fn mk_bool_sort(&'a self) -> S;
    fn mk_bv_value_uint64(&'a self, sort: &S, val: u64) -> T;
    fn mk_bvadd(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvand(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvashr(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvlshr(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvmul(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvnand(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvneg(&'a self, term: &T) -> T;
    fn mk_bvnor(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvnot(&'a self, term: &T) -> T;
    fn mk_bvnxor(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvor(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvsdiv(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvsge(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvsgt(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvshl(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvsle(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvslt(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvsmod(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvsub(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvudiv(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvuge(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvugt(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvule(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvult(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvumod(&'a self, term1: &T, term2: &T) -> T;
    fn mk_bvxor(&'a self, term1: &T, term2: &T) -> T;
    fn mk_eq(&'a self, term1: &T, term2: &T) -> T;
    fn mk_implies(&'a self, term1: &T, term2: &T) -> T;
    fn mk_neq(&'a self, term1: &T, term2: &T) -> T;
    fn mk_not(&'a self, term: &T) -> T;
    fn mk_or(&'a self, term1: &T, term2: &T) -> T;
    fn mk_smt_bool(&'a self, val: bool) -> T;
    fn mk_smt_symbol(&'a self, name: &str, sort: &S) -> T;
    fn mk_xor(&'a self, term1: &T, term2: &T) -> T;
}
