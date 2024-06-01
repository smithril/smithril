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

pub trait GeneralConvertor<S: GeneralSort, T: GeneralTerm> {
    fn mk_smt_symbol(&self, name: &str, sort: &S) -> T;
    fn assert(&self, term: &T);
    fn mk_eq(&self, term1: &T, term2: &T) -> T;
    fn check_sat(&self) -> SolverResult;
    fn mk_bv_sort(&self, size: u64) -> S;
    fn mk_bv_value_uint64(&self, sort: &S, val: u64) -> T;
    fn mk_smt_bool(&self, val: bool) -> T;
}
