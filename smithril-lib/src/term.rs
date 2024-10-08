use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum FpConstant {
    PosZero,
    PosInf,
    NegZero,
    NegInf,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum GenConstant {
    Boolean(bool),
    Numeral(u64),
    Symbol(String),
    Fp(FpConstant),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum UnoOperationKind {
    Not,
    BvNeg,
    BvNot,
    FpIsInf,
    FpIsNan,
    FpIsNorm,
    FpIsSubnorm,
    FpIsZero,
    FpIsPos,
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
    FpEq,
    Concat,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum TrioOperationKind {
    Store,
    MkFpValue,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum FpUnoOperationKind {
    FpSqrt,
    FpRti,
    FpAbs,
    FpNeg,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum FpDuoOperationKind {
    FpMin,
    FpMax,
    FpLT,
    FpLEQ,
    FpGT,
    FpGEQ,
    FpAdd,
    FpSub,
    FpMul,
    FpDiv,
    FpRem,
}

#[repr(C)]
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum RoundingMode {
    RNA,
    RNE,
    RTN,
    RTP,
    RTZ,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum FpToFpOperationKind {
    FromFp,
    FromSBv,
    FromUBv,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum FpToOperationKind {
    SBv,
    UBv,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum GenOperation {
    Uno(UnoOperationKind, Term),
    Extract(u64, u64, Term),
    FpToFp(FpToFpOperationKind, RoundingMode, u64, u64, Term),
    FpTo(FpToOperationKind, RoundingMode, u64, Term),
    Duo(DuoOperationKind, Term, Term),
    Trio(TrioOperationKind, Term, Term, Term),
    FpUno(FpUnoOperationKind, RoundingMode, Term),
    FpDuo(FpDuoOperationKind, RoundingMode, Term, Term),
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
    FpSort(u64, u64),
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
    fn try_get_bv_size(&self) -> Option<u64> {
        match self {
            Sort::BvSort(size) => Some(*size),
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

pub fn mk_fp_sort(ew: u64, sw: u64) -> Sort {
    Sort::FpSort(ew, sw)
}

pub fn mk_fp_value(bv_sign: &Term, bv_exponent: &Term, bv_significand: &Term) -> Term {
    let exp_size = bv_exponent.sort.try_get_bv_size().unwrap();
    let sign_size = bv_significand.sort.try_get_bv_size().unwrap();
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::Trio(
            TrioOperationKind::MkFpValue,
            bv_sign.clone(),
            bv_exponent.clone(),
            bv_significand.clone(),
        ))),
        sort: mk_fp_sort(exp_size, sign_size),
    }
}

pub fn mk_fp_pos_zero(sort: &Sort) -> Term {
    Term {
        term: UnsortedTerm::Constant(GenConstant::Fp(FpConstant::PosZero)),
        sort: sort.clone(),
    }
}
pub fn mk_fp_pos_inf(sort: &Sort) -> Term {
    Term {
        term: UnsortedTerm::Constant(GenConstant::Fp(FpConstant::PosInf)),
        sort: sort.clone(),
    }
}
pub fn mk_fp_neg_zero(sort: &Sort) -> Term {
    Term {
        term: UnsortedTerm::Constant(GenConstant::Fp(FpConstant::NegZero)),
        sort: sort.clone(),
    }
}
pub fn mk_fp_neg_inf(sort: &Sort) -> Term {
    Term {
        term: UnsortedTerm::Constant(GenConstant::Fp(FpConstant::NegInf)),
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

macro_rules! binary_function {
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

macro_rules! unary_function {
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

macro_rules! rm_unary_function {
    ($func_name:ident, $kind:ident) => {
        pub fn $func_name(r_mode: &RoundingMode, term: &Term) -> Term {
            Term {
                term: UnsortedTerm::Operation(Box::new(GenOperation::FpUno(
                    FpUnoOperationKind::$kind,
                    r_mode.clone(),
                    term.clone(),
                ))),
                sort: term.sort.clone(),
            }
        }
    };
}

macro_rules! rm_binary_function {
    ($func_name:ident, $kind:ident) => {
        pub fn $func_name(r_mode: &RoundingMode, term1: &Term, term2: &Term) -> Term {
            Term {
                term: UnsortedTerm::Operation(Box::new(GenOperation::FpDuo(
                    FpDuoOperationKind::$kind,
                    r_mode.clone(),
                    term1.clone(),
                    term2.clone(),
                ))),
                sort: term1.sort.clone(),
            }
        }
    };
}

macro_rules! rm_boolean_binary_function {
    ($func_name:ident, $kind:ident) => {
        pub fn $func_name(r_mode: &RoundingMode, term1: &Term, term2: &Term) -> Term {
            Term {
                term: UnsortedTerm::Operation(Box::new(GenOperation::FpDuo(
                    FpDuoOperationKind::$kind,
                    r_mode.clone(),
                    term1.clone(),
                    term2.clone(),
                ))),
                sort: mk_bool_sort(),
            }
        }
    };
}

boolean_unary_function!(fp_is_nan, FpIsNan);
boolean_unary_function!(fp_is_inf, FpIsInf);
boolean_unary_function!(fp_is_normal, FpIsNorm);
boolean_unary_function!(fp_is_subnormal, FpIsSubnorm);
boolean_unary_function!(fp_is_zero, FpIsZero);
boolean_unary_function!(fp_is_pos, FpIsPos);
boolean_binary_function!(mk_fp_eq, FpEq);

rm_binary_function!(mk_fp_rem, FpRem);
rm_binary_function!(mk_fp_min, FpMin);
rm_binary_function!(mk_fp_max, FpMax);
rm_boolean_binary_function!(mk_fp_lt, FpLT);
rm_boolean_binary_function!(mk_fp_leq, FpLEQ);
rm_boolean_binary_function!(mk_fp_gt, FpGT);
rm_boolean_binary_function!(mk_fp_geq, FpGEQ);
rm_binary_function!(mk_fp_add, FpAdd);
rm_binary_function!(mk_fp_sub, FpSub);
rm_binary_function!(mk_fp_mul, FpMul);
rm_binary_function!(mk_fp_div, FpDiv);

rm_unary_function!(mk_fp_sqrt, FpSqrt);
rm_unary_function!(mk_fp_rti, FpRti);
rm_unary_function!(mk_fp_abs, FpAbs);
rm_unary_function!(mk_fp_neg, FpNeg);

pub fn mk_fp_to_fp_from_fp(r_mode: &RoundingMode, term: &Term, ew: u64, sw: u64) -> Term {
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::FpToFp(
            FpToFpOperationKind::FromFp,
            r_mode.clone(),
            ew,
            sw,
            term.clone(),
        ))),
        sort: mk_fp_sort(ew, sw),
    }
}
pub fn mk_fp_to_sbv(r_mode: &RoundingMode, term: &Term, w: u64) -> Term {
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::FpTo(
            FpToOperationKind::SBv,
            r_mode.clone(),
            w,
            term.clone(),
        ))),
        sort: mk_bv_sort(w),
    }
}

pub fn mk_fp_to_ubv(r_mode: &RoundingMode, term: &Term, w: u64) -> Term {
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::FpTo(
            FpToOperationKind::UBv,
            r_mode.clone(),
            w,
            term.clone(),
        ))),
        sort: mk_bv_sort(w),
    }
}

pub fn mk_fp_to_fp_from_sbv(r_mode: &RoundingMode, term: &Term, ew: u64, sw: u64) -> Term {
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::FpToFp(
            FpToFpOperationKind::FromSBv,
            r_mode.clone(),
            ew,
            sw,
            term.clone(),
        ))),
        sort: mk_fp_sort(ew, sw),
    }
}

pub fn mk_fp_to_fp_from_ubv(r_mode: &RoundingMode, term: &Term, ew: u64, sw: u64) -> Term {
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::FpToFp(
            FpToFpOperationKind::FromUBv,
            r_mode.clone(),
            ew,
            sw,
            term.clone(),
        ))),
        sort: mk_fp_sort(ew, sw),
    }
}

boolean_binary_function!(mk_and, And);
binary_function!(mk_bv_add, BvAdd);
binary_function!(mk_bv_and, BvAnd);
binary_function!(mk_bv_ashr, BvAshr);
binary_function!(mk_bv_lshr, BvLshr);
binary_function!(mk_bv_mul, BvMul);
binary_function!(mk_bv_nand, BvAnd);
unary_function!(mk_bv_neg, BvNeg);
binary_function!(mk_bv_nor, BvNor);
unary_function!(mk_bv_not, BvNot);
binary_function!(mk_bv_nxor, BvNxor);

binary_function!(mk_bv_or, BvOr);
binary_function!(mk_bv_sdiv, BvSdiv);
binary_function!(mk_bv_sge, BvSge);
binary_function!(mk_bv_sgt, BvSgt);
binary_function!(mk_bv_shl, BvShl);
binary_function!(mk_bv_sle, BvSle);
binary_function!(mk_bv_slt, BvSlt);
binary_function!(mk_bv_smod, BvSmod);
binary_function!(mk_bv_sub, BvSub);
binary_function!(mk_bv_udiv, BvUdiv);
binary_function!(mk_bv_uge, BvUge);
binary_function!(mk_bv_ugt, BvUgt);
binary_function!(mk_bv_ule, BvUle);
binary_function!(mk_bv_ult, BvUlt);
binary_function!(mk_bv_umod, BvUmod);
binary_function!(mk_bv_xor, BvXor);
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
            GenConstant::Fp(_) => None,
        },
        UnsortedTerm::Operation(_) => None,
    }
}
