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
    ConstantSymbol(Box<Term>),
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
    FpAbs,
    FpNeg,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum DuoOperationKind {
    Eq,
    And,
    Implies,
    Neq,
    Or,
    Xor,
    Iff,
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
    FpRem,
    FpMin,
    FpMax,
    FpLT,
    FpLEQ,
    FpGT,
    FpGEQ,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum TrioOperationKind {
    Store,
    Ite,
    Fp,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum ExtendOperationKind {
    Sign,
    Zero,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum FpUnoOperationKind {
    FpSqrt,
    FpRti,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum FpDuoOperationKind {
    FpAdd,
    FpSub,
    FpMul,
    FpDiv,
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
    Extend(ExtendOperationKind, u64, Term),
    FpToFp(FpToFpOperationKind, RoundingMode, u64, u64, Term),
    FpToFpFromBv(u64, u64, Term),
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

#[repr(C)]
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum SortKind {
    Bv,
    Bool,
    Array,
    Fp,
}

impl Sort {
    fn is_array_sort(&self) -> bool {
        matches!(self, Sort::ArraySort(_, _))
    }

    fn try_get_elem_sort(&self) -> Option<&Sort> {
        match self {
            Sort::ArraySort(_, elem) => Some(elem.as_ref()),
            _ => None,
        }
    }

    pub fn try_get_bv_sort_size(&self) -> Option<u64> {
        match self {
            Sort::BvSort(size) => Some(*size),
            _ => None,
        }
    }

    pub fn get_kind(&self) -> SortKind {
        match self {
            Sort::BvSort(_) => SortKind::Bv,
            Sort::BoolSort() => SortKind::Bool,
            Sort::ArraySort(_, _) => SortKind::Array,
            Sort::FpSort(_, _) => SortKind::Fp,
        }
    }

    pub fn try_fp_get_bv_exp_size(&self) -> Option<u64> {
        match self {
            Sort::FpSort(exp, _) => Some(*exp),
            _ => None,
        }
    }

    pub fn try_fp_get_bv_sig_size(&self) -> Option<u64> {
        match self {
            Sort::FpSort(_, sig) => Some(*sig),
            _ => None,
        }
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub struct Term {
    pub term: UnsortedTerm,
    pub sort: Sort,
}

impl Term {
    pub fn get_sort(&self) -> Sort {
        self.sort.clone()
    }
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

pub fn mk_fp(bv_sign: &Term, bv_exponent: &Term, bv_significand: &Term) -> Term {
    let exp_size = bv_exponent.sort.try_get_bv_sort_size().unwrap();
    let sign_size = bv_significand.sort.try_get_bv_sort_size().unwrap() + 1;
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::Trio(
            TrioOperationKind::Fp,
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

boolean_unary_function!(fp_is_nan, FpIsNan);
boolean_unary_function!(fp_is_inf, FpIsInf);
boolean_unary_function!(fp_is_normal, FpIsNorm);
boolean_unary_function!(fp_is_subnormal, FpIsSubnorm);
boolean_unary_function!(fp_is_zero, FpIsZero);
boolean_unary_function!(fp_is_pos, FpIsPos);
boolean_binary_function!(mk_fp_eq, FpEq);

binary_function!(mk_fp_rem, FpRem);
binary_function!(mk_fp_min, FpMin);
binary_function!(mk_fp_max, FpMax);
boolean_binary_function!(mk_fp_lt, FpLT);
boolean_binary_function!(mk_fp_leq, FpLEQ);
boolean_binary_function!(mk_fp_gt, FpGT);
boolean_binary_function!(mk_fp_geq, FpGEQ);
rm_binary_function!(mk_fp_add, FpAdd);
rm_binary_function!(mk_fp_sub, FpSub);
rm_binary_function!(mk_fp_mul, FpMul);
rm_binary_function!(mk_fp_div, FpDiv);

rm_unary_function!(mk_fp_sqrt, FpSqrt);
rm_unary_function!(mk_fp_rti, FpRti);
unary_function!(mk_fp_abs, FpAbs);
unary_function!(mk_fp_neg, FpNeg);

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

pub fn mk_fp_to_fp_from_bv(term: &Term, ew: u64, sw: u64) -> Term {
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::FpToFpFromBv(ew, sw, term.clone()))),
        sort: mk_fp_sort(ew, sw),
    }
}

boolean_binary_function!(mk_and, And);
binary_function!(mk_bv_add, BvAdd);
pub fn mk_bv_and(term1: &Term, term2: &Term) -> Term {
    dbg!("bv_and", term1, term2);
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::Duo(
            DuoOperationKind::BvAnd,
            term1.clone(),
            term2.clone(),
        ))),
        sort: term1.sort.clone(),
    }
}
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
boolean_binary_function!(mk_bv_sge, BvSge);
boolean_binary_function!(mk_bv_sgt, BvSgt);
binary_function!(mk_bv_shl, BvShl);
boolean_binary_function!(mk_bv_sle, BvSle);
boolean_binary_function!(mk_bv_slt, BvSlt);
binary_function!(mk_bv_smod, BvSmod);
binary_function!(mk_bv_sub, BvSub);
binary_function!(mk_bv_udiv, BvUdiv);
boolean_binary_function!(mk_bv_uge, BvUge);
boolean_binary_function!(mk_bv_ugt, BvUgt);
boolean_binary_function!(mk_bv_ule, BvUle);
boolean_binary_function!(mk_bv_ult, BvUlt);
binary_function!(mk_bv_umod, BvUmod);
binary_function!(mk_bv_xor, BvXor);
boolean_binary_function!(mk_eq, Eq);
boolean_binary_function!(mk_implies, Implies);
boolean_binary_function!(mk_neq, Neq);
boolean_unary_function!(mk_not, Not);
boolean_binary_function!(mk_or, Or);
boolean_binary_function!(mk_iff, Iff);
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
pub fn mk_smt_const_symbol(term: &Term, sort: &Sort) -> Term {
    Term {
        term: UnsortedTerm::Constant(GenConstant::ConstantSymbol(Box::new(term.clone()))),
        sort: sort.clone(),
    }
}
boolean_binary_function!(mk_xor, Xor);
pub fn mk_array_sort(index: &Sort, element: &Sort) -> Sort {
    Sort::ArraySort(Box::new(index.clone()), Box::new(element.clone()))
}
pub fn mk_select(term1: &Term, term2: &Term) -> Term {
    assert!(term1.sort.is_array_sort());
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

pub fn mk_ite(term1: &Term, term2: &Term, term3: &Term) -> Term {
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::Trio(
            TrioOperationKind::Ite,
            term1.clone(),
            term2.clone(),
            term3.clone(),
        ))),
        sort: term2.sort.clone(),
    }
}

pub fn try_constant_to_string(term: &Term) -> Option<String> {
    match &term.term {
        UnsortedTerm::Constant(constant) => match constant {
            GenConstant::Boolean(val) => Some(format!("{}", val)),
            GenConstant::Numeral(val) => {
                print!("{}", val);
                Some(format!("{}", val))
            }
            GenConstant::Symbol(_) => None,
            GenConstant::Fp(_) => None,
            GenConstant::ConstantSymbol(_) => None,
        },
        UnsortedTerm::Operation(_) => None,
    }
}

pub fn mk_concat(term1: &Term, term2: &Term) -> Term {
    let size =
        term1.sort.try_get_bv_sort_size().unwrap() + term2.sort.try_get_bv_sort_size().unwrap();
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::Duo(
            DuoOperationKind::Concat,
            term1.clone(),
            term2.clone(),
        ))),
        sort: mk_bv_sort(size),
    }
}

pub fn mk_extract(high: u64, low: u64, term: &Term) -> Term {
    let size = high - low + 1;
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::Extract(high, low, term.clone()))),
        sort: mk_bv_sort(size),
    }
}

pub fn mk_sing_extend(ext: u64, term: &Term) -> Term {
    let size = term.sort.try_get_bv_sort_size().unwrap() + ext;
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::Extend(
            ExtendOperationKind::Sign,
            ext,
            term.clone(),
        ))),
        sort: mk_bv_sort(size),
    }
}

pub fn mk_zero_extend(ext: u64, term: &Term) -> Term {
    let size = term.sort.try_get_bv_sort_size().unwrap() + ext;
    Term {
        term: UnsortedTerm::Operation(Box::new(GenOperation::Extend(
            ExtendOperationKind::Zero,
            ext,
            term.clone(),
        ))),
        sort: mk_bv_sort(size),
    }
}
