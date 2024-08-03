use core::fmt;
use serde::{Deserialize, Serialize};

pub trait GeneralSort {}

pub trait GeneralTerm {}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone)]
pub enum GenConstant {
    Numeral(u64),
    Boolean(bool),
    Symbol(String),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone)]
pub enum UnoOperationKind {
    Not,
    BvNeg,
    BvNot,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone)]
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

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone)]
pub enum TrioOperationKind {
    Store,
}
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone)]
pub enum GenOperation {
    Uno(UnoOperationKind, Term),
    Duo(DuoOperationKind, Term, Term),
    Trio(TrioOperationKind, Term, Term, Term),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone)]
pub enum UnsortedTerm {
    Constant(GenConstant),
    Operation(Box<GenOperation>),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone)]
pub enum Sort {
    BvSort(u64),
    BoolSort(),
    ArraySort(Box<Sort>, Box<Sort>),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone)]
pub struct Term {
    pub term: UnsortedTerm,
    pub sort: Sort,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone)]
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
    fn assert(&'a self, term: &T);
    fn check_sat(&'a self) -> SolverResult;
    fn mk_bv_sort(&'a self, size: u64) -> S;
    fn mk_bool_sort(&'a self) -> S;
    fn mk_and(&'a self, term1: &T, term2: &T) -> T;
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
    fn mk_array_sort(&'a self, index: &S, element: &S) -> S;
    fn mk_select(&'a self, term1: &T, term2: &T) -> T;
    fn mk_store(&'a self, term1: &T, term2: &T, term3: &T) -> T;
    fn convert_term(&'a self, term: &Term) -> T {
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
    fn convert_sort(&'a self, sort: &Sort) -> S {
        match sort {
            Sort::BvSort(x) => self.mk_bv_sort(*x),
            Sort::BoolSort() => self.mk_bool_sort(),
            Sort::ArraySort(index, element) => {
                self.mk_array_sort(&self.convert_sort(index), &self.convert_sort(element))
            }
        }
    }
}

pub trait GeneralSolver {
    fn assert(&self, term: &Term);
    fn check_sat(&self) -> SolverResult;
}
