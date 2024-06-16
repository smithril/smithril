use core::fmt;
use std::{collections::HashMap, ffi::CString};

pub trait GeneralSort {}

pub trait GeneralTerm {}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum GenConstant {
    Numeral(u64),
    Boolean(bool),
    Symbol(String),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum UnoOperationKind {
    Not,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum DuoOperationKind {
    Eq,
    And,
    Implies,
    Neq,
    Or,
    Xor,
    Select,
}
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum GenOperation {
    Uno(UnoOperationKind, Term),
    Duo(DuoOperationKind, Term, Term),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum UnsortedTerm {
    Constant(GenConstant),
    Operation(Box<GenOperation>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Sort {
    BvSort(u64),
    BoolSort(),
    ArraySort(Box<Sort>, Box<Sort>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Term {
    pub term: UnsortedTerm,
    pub sort: Sort,
}

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
    fn mk_const_array(&'a self, sort: &S, value: &T) -> T;
    fn mk_select(&'a self, term1: &T, term2: &T)  -> T;
    fn convert_term(&'a self, term: &Term) -> T {
        match &term.term {
            UnsortedTerm::Constant(const_term) => match const_term {
                GenConstant::Numeral(x) => {
                    self.mk_bv_value_uint64(&self.convert_sort(&term.sort), *x)
                }
                GenConstant::Boolean(x) => self.mk_smt_bool(*x),
                GenConstant::Symbol(x) => self.mk_smt_symbol(&x, &self.convert_sort(&term.sort)),
            },
            UnsortedTerm::Operation(operation) => match operation.as_ref() {
                GenOperation::Uno(kind, term1) => {
                    let t1 = self.convert_term(term1);
                    match kind {
                        UnoOperationKind::Not => self.mk_not(&t1),
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
                        DuoOperationKind::Select => self.mk_select(&t1,&t2),
                    }
                }
            },
        }
    }
    fn convert_sort(&'a self, sort: &Sort) -> S {
        match sort {
            Sort::BvSort(x) => self.mk_bv_sort(*x),
            Sort::BoolSort() => self.mk_bool_sort(),
            Sort::ArraySort(index, element) => self.mk_array_sort(&self.convert_sort(index), &self.convert_sort(element)),
        }
    }
}
