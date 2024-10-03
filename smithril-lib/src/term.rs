use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum GenConstant {
    Boolean(bool),
    Numeral(u64),
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

impl Sort {
    fn is_array(&self) -> bool {
        matches!(self, Sort::ArraySort(_, _))
    }
    fn try_get_elem_sort(&self) -> Option<&Sort> {
        match self {
            Sort::ArraySort(_, elem) => Some(elem.as_ref()),
            _ => None,
        }
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub struct Term {
    pub term: UnsortedTerm,
    pub sort: Sort,
}

pub fn mk_bv_sort(size: u64) -> Sort {
    Sort::BvSort(size)
}

pub fn mk_bool_sort() -> Sort {
    Sort::BoolSort()
}

pub fn mk_bv_value_uint64(val: u64, sort: &Sort) -> Term {
    Term {
        term: UnsortedTerm::Constant(GenConstant::Numeral(val)),
        sort: sort.clone(),
    }
}

macro_rules! boolean_unary_function {
    ($func_name:ident, $kind:ident) => {
        pub fn $func_name(term: &Term) -> Term {
            Term {
                term: UnsortedTerm::Operation(Box::new(GenOperation::Uno(
                    UnoOperationKind::$kind,
                    term.clone(),
                ))),
                sort: mk_bool_sort(),
            }
        }
    };
}

macro_rules! boolean_binary_function {
    ($func_name:ident, $kind:ident) => {
        pub fn $func_name(term1: &Term, term2: &Term) -> Term {
            Term {
                term: UnsortedTerm::Operation(Box::new(GenOperation::Duo(
                    DuoOperationKind::$kind,
                    term1.clone(),
                    term2.clone(),
                ))),
                sort: mk_bool_sort(),
            }
        }
    };
}

macro_rules! bv_binary_function {
    ($func_name:ident, $kind:ident) => {
        pub fn $func_name(term1: &Term, term2: &Term) -> Term {
            Term {
                term: UnsortedTerm::Operation(Box::new(GenOperation::Duo(
                    DuoOperationKind::$kind,
                    term1.clone(),
                    term2.clone(),
                ))),
                sort: term1.sort.clone(),
            }
        }
    };
}

macro_rules! bv_unary_function {
    ($func_name:ident, $kind:ident) => {
        pub fn $func_name(term: &Term) -> Term {
            Term {
                term: UnsortedTerm::Operation(Box::new(GenOperation::Uno(
                    UnoOperationKind::$kind,
                    term.clone(),
                ))),
                sort: term.sort.clone(),
            }
        }
    };
}

boolean_binary_function!(mk_and, And);
bv_binary_function!(mk_bvadd, BvAdd);
bv_binary_function!(mk_bvand, BvAnd);
bv_binary_function!(mk_bvashr, BvAshr);
bv_binary_function!(mk_bvlshr, BvLshr);
bv_binary_function!(mk_bvmul, BvMul);
bv_binary_function!(mk_bvnand, BvAnd);
bv_unary_function!(mk_bvneg, BvNeg);
bv_binary_function!(mk_bvnor, BvNor);
bv_unary_function!(mk_bvnot, BvNot);
bv_binary_function!(mk_bvnxor, BvNxor);

bv_binary_function!(mk_bvor, BvOr);
bv_binary_function!(mk_bvsdiv, BvSdiv);
bv_binary_function!(mk_bvsge, BvSge);
bv_binary_function!(mk_bvsgt, BvSgt);
bv_binary_function!(mk_bvshl, BvShl);
bv_binary_function!(mk_bvsle, BvSle);
bv_binary_function!(mk_bvslt, BvSlt);
bv_binary_function!(mk_bvsmod, BvSmod);
bv_binary_function!(mk_bvsub, BvSub);
bv_binary_function!(mk_bvudiv, BvUdiv);
bv_binary_function!(mk_bvuge, BvUge);
bv_binary_function!(mk_bvugt, BvUgt);
bv_binary_function!(mk_bvule, BvUle);
bv_binary_function!(mk_bvult, BvUlt);
bv_binary_function!(mk_bvumod, BvUmod);
bv_binary_function!(mk_bvxor, BvXor);
boolean_binary_function!(mk_eq, Eq);
boolean_binary_function!(mk_implies, Implies);
boolean_binary_function!(mk_neq, Neq);
boolean_unary_function!(mk_not, Not);
boolean_binary_function!(mk_or, Or);
pub fn mk_smt_bool(val: bool) -> Term {
    Term {
        term: UnsortedTerm::Constant(GenConstant::Boolean(val)),
        sort: mk_bool_sort(),
    }
}
pub fn mk_smt_symbol(name: &str, sort: &Sort) -> Term {
    Term {
        term: UnsortedTerm::Constant(GenConstant::Symbol(name.to_string())),
        sort: sort.clone(),
    }
}
boolean_binary_function!(mk_xor, Xor);
pub fn mk_array_sort(index: &Sort, element: &Sort) -> Sort {
    Sort::ArraySort(Box::new(index.clone()), Box::new(element.clone()))
}
pub fn mk_select(term1: &Term, term2: &Term) -> Term {
    assert!(term1.sort.is_array());
    let elem_sort = term1.sort.try_get_elem_sort().unwrap();
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::Duo(
            DuoOperationKind::Select,
            term1.clone(),
            term2.clone(),
        ))),
        sort: elem_sort.clone(),
    }
}

pub fn mk_store(term1: &Term, term2: &Term, term3: &Term) -> Term {
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::Trio(
            TrioOperationKind::Store,
            term1.clone(),
            term2.clone(),
            term3.clone(),
        ))),
        sort: term1.sort.clone(),
    }
}

pub fn try_constant_to_string(term: &Term) -> Option<String> {
    match &term.term {
        UnsortedTerm::Constant(constant) => match constant {
            GenConstant::Boolean(val) => Some(format!("{}", val)),
            GenConstant::Numeral(val) => Some(format!("{}", val)),
            GenConstant::Symbol(_) => None,
        },
        UnsortedTerm::Operation(_) => None,
    }
}
