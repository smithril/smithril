use core::fmt;
use serde::{Deserialize, Serialize};
use serde::{Deserialize, Serialize};

pub trait GeneralSort {}

pub trait GeneralTerm {}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum GenConstant {
    Numeral(u64),
    Boolean(bool),
    Symbol(String),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum UnoOperationKind {
    Not,
    BvNeg,
    BvNot,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum DuoOperationKind {
    Eq,
    And,
    Implies,
    Neq,
    Or,
    Xor,
    Select,
    BvAdd,
    BvAnd,
    BvAshr,
    BvLshr,
    BvMul,
    BvNand,
    BvNor,
    BvNxor,
    BvOr,
    BvSdiv,
    BvSge,
    BvSgt,
    BvShl,
    BvSle,
    BvSlt,
    BvSmod,
    BvSub,
    BvUdiv,
    BvUge,
    BvUgt,
    BvUle,
    BvUlt,
    BvUmod,
    BvXor,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum TrioOperationKind {
    Store,
}
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum GenOperation {
    Uno(UnoOperationKind, Term),
    Duo(DuoOperationKind, Term, Term),
    Trio(TrioOperationKind, Term, Term, Term),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum UnsortedTerm {
    Constant(GenConstant),
    Operation(Box<GenOperation>),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum Sort {
    BvSort(u64),
    BoolSort(),
    ArraySort(Box<Sort>, Box<Sort>),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub struct Term {
    pub term: UnsortedTerm,
    pub sort: Sort,
}

#[derive(PartialEq, Eq, Serialize, Deserialize, Debug, Clone)]
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

pub trait GeneralUnsatCoreConverter<S, T>
where
    S: GeneralSort,
    T: GeneralTerm,
{
    fn unsat_core(&self) -> Vec<T>;
}
pub trait GeneralConverter<S, T>
where
    S: GeneralSort,
    T: GeneralTerm,
{
    fn assert(&self, term: &T);
    fn check_sat(&self) -> SolverResult;
    fn eval(&self, term1: &T) -> Option<T>;
    fn mk_bv_sort(&self, size: u64) -> S;
    fn mk_bool_sort(&self) -> S;
    fn mk_and(&self, term1: &T, term2: &T) -> T;
    fn mk_bv_value_uint64(&self, sort: &S, val: u64) -> T;
    fn mk_bvadd(&self, term1: &T, term2: &T) -> T;
    fn mk_bvand(&self, term1: &T, term2: &T) -> T;
    fn mk_bvashr(&self, term1: &T, term2: &T) -> T;
    fn mk_bvlshr(&self, term1: &T, term2: &T) -> T;
    fn mk_bvmul(&self, term1: &T, term2: &T) -> T;
    fn mk_bvnand(&self, term1: &T, term2: &T) -> T;
    fn mk_bvneg(&self, term: &T) -> T;
    fn mk_bvnor(&self, term1: &T, term2: &T) -> T;
    fn mk_bvnot(&self, term: &T) -> T;
    fn mk_bvnxor(&self, term1: &T, term2: &T) -> T;
    fn mk_bvor(&self, term1: &T, term2: &T) -> T;
    fn mk_bvsdiv(&self, term1: &T, term2: &T) -> T;
    fn mk_bvsge(&self, term1: &T, term2: &T) -> T;
    fn mk_bvsgt(&self, term1: &T, term2: &T) -> T;
    fn mk_bvshl(&self, term1: &T, term2: &T) -> T;
    fn mk_bvsle(&self, term1: &T, term2: &T) -> T;
    fn mk_bvslt(&self, term1: &T, term2: &T) -> T;
    fn mk_bvsmod(&self, term1: &T, term2: &T) -> T;
    fn mk_bvsub(&self, term1: &T, term2: &T) -> T;
    fn mk_bvudiv(&self, term1: &T, term2: &T) -> T;
    fn mk_bvuge(&self, term1: &T, term2: &T) -> T;
    fn mk_bvugt(&self, term1: &T, term2: &T) -> T;
    fn mk_bvule(&self, term1: &T, term2: &T) -> T;
    fn mk_bvult(&self, term1: &T, term2: &T) -> T;
    fn mk_bvumod(&self, term1: &T, term2: &T) -> T;
    fn mk_bvxor(&self, term1: &T, term2: &T) -> T;
    fn mk_eq(&self, term1: &T, term2: &T) -> T;
    fn mk_implies(&self, term1: &T, term2: &T) -> T;
    fn mk_neq(&self, term1: &T, term2: &T) -> T;
    fn mk_not(&self, term: &T) -> T;
    fn mk_or(&self, term1: &T, term2: &T) -> T;
    fn mk_smt_bool(&self, val: bool) -> T;
    fn mk_smt_symbol(&self, name: &str, sort: &S) -> T;
    fn mk_xor(&self, term1: &T, term2: &T) -> T;
    fn mk_array_sort(&self, index: &S, element: &S) -> S;
    fn mk_select(&self, term1: &T, term2: &T) -> T;
    fn mk_store(&self, term1: &T, term2: &T, term3: &T) -> T;
    fn convert_term(&self, term: &Term) -> T {
        match &term.term {
            UnsortedTerm::Constant(const_term) => match const_term {
                GenConstant::Numeral(x) => {
                    self.mk_bv_value_uint64(&self.convert_sort(&term.sort), *x)
                }
                GenConstant::Boolean(x) => self.mk_smt_bool(*x),
                GenConstant::Symbol(x) => self.mk_smt_symbol(x, &self.convert_sort(&term.sort)),
            },
            UnsortedTerm::Operation(operation) => match operation.as_ref() {
                GenOperation::Uno(kind, term1) => {
                    let t1 = self.convert_term(term1);
                    match kind {
                        UnoOperationKind::Not => self.mk_not(&t1),
                        UnoOperationKind::BvNeg => self.mk_bvneg(&t1),
                        UnoOperationKind::BvNot => self.mk_bvnot(&t1),
                    }
                }
                GenOperation::Duo(kind, term1, term2) => {
                    let t1 = self.convert_term(term1);
                    let t2 = self.convert_term(term2);
                    match kind {
                        DuoOperationKind::Eq => self.mk_eq(&t1, &t2),
                        DuoOperationKind::And => self.mk_and(&t1, &t2),
                        DuoOperationKind::Implies => self.mk_implies(&t1, &t2),
                        DuoOperationKind::Neq => self.mk_neq(&t1, &t2),
                        DuoOperationKind::Or => self.mk_or(&t1, &t2),
                        DuoOperationKind::Xor => self.mk_xor(&t1, &t2),
                        DuoOperationKind::Select => self.mk_select(&t1, &t2),
                        DuoOperationKind::BvAdd => self.mk_bvadd(&t1, &t2),
                        DuoOperationKind::BvAnd => self.mk_bvand(&t1, &t2),
                        DuoOperationKind::BvAshr => self.mk_bvashr(&t1, &t2),
                        DuoOperationKind::BvLshr => self.mk_bvlshr(&t1, &t2),
                        DuoOperationKind::BvMul => self.mk_bvmul(&t1, &t2),
                        DuoOperationKind::BvNand => self.mk_bvnand(&t1, &t2),
                        DuoOperationKind::BvNor => self.mk_bvnor(&t1, &t2),
                        DuoOperationKind::BvNxor => self.mk_bvnxor(&t1, &t2),
                        DuoOperationKind::BvOr => self.mk_bvor(&t1, &t2),
                        DuoOperationKind::BvSdiv => self.mk_bvsdiv(&t1, &t2),
                        DuoOperationKind::BvSge => self.mk_bvsge(&t1, &t2),
                        DuoOperationKind::BvSgt => self.mk_bvsgt(&t1, &t2),
                        DuoOperationKind::BvShl => self.mk_bvshl(&t1, &t2),
                        DuoOperationKind::BvSle => self.mk_bvsle(&t1, &t2),
                        DuoOperationKind::BvSlt => self.mk_bvslt(&t1, &t2),
                        DuoOperationKind::BvSmod => self.mk_bvsmod(&t1, &t2),
                        DuoOperationKind::BvSub => self.mk_bvsub(&t1, &t2),
                        DuoOperationKind::BvUdiv => self.mk_bvudiv(&t1, &t2),
                        DuoOperationKind::BvUge => self.mk_bvuge(&t1, &t2),
                        DuoOperationKind::BvUgt => self.mk_bvugt(&t1, &t2),
                        DuoOperationKind::BvUle => self.mk_bvule(&t1, &t2),
                        DuoOperationKind::BvUlt => self.mk_bvult(&t1, &t2),
                        DuoOperationKind::BvUmod => self.mk_bvumod(&t1, &t2),
                        DuoOperationKind::BvXor => self.mk_bvxor(&t1, &t2),
                    }
                }
                GenOperation::Trio(kind, term1, term2, term3) => {
                    let t1 = self.convert_term(term1);
                    let t2 = self.convert_term(term2);
                    let t3 = self.convert_term(term3);
                    match kind {
                        TrioOperationKind::Store => self.mk_store(&t1, &t2, &t3),
                    }
                }
            },
        }
    }
    fn convert_sort(&self, sort: &Sort) -> S {
        match sort {
            Sort::BvSort(x) => self.mk_bv_sort(*x),
            Sort::BoolSort() => self.mk_bool_sort(),
            Sort::ArraySort(index, element) => {
                self.mk_array_sort(&self.convert_sort(index), &self.convert_sort(element))
            }
        }
    }
}

pub trait GeneralUnsatCoreSolver {
    fn unsat_core(&self) -> Vec<Term>;
}
pub trait GeneralSolver {
    fn assert(&self, term: &Term);
    fn check_sat(&self) -> SolverResult;
    fn eval(&self, term: &Term) -> Option<Term>;
}
