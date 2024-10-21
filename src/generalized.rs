use core::fmt;
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, sync::Arc, time::Duration};

use crate::term::DuoOperationKind;
use crate::term::FpDuoOperationKind;
use crate::term::FpUnoOperationKind;
use crate::term::GenConstant;
use crate::term::GenOperation;
use crate::term::RoundingMode;
use crate::term::Sort;
use crate::term::Term;
use crate::term::TrioOperationKind;
use crate::term::UnoOperationKind;
use crate::term::UnsortedTerm;

pub trait GeneralSort {}

pub trait GeneralTerm {}

#[repr(C)]
#[derive(PartialEq, Eq, Serialize, Deserialize, Debug, Clone, Copy)]
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

pub trait Factory<C, SL, I>
where
    C: Context,
    SL: Solver,
    I: Interrupter + Sync + Send,
{
    fn new_context(&mut self) -> Arc<C>;
    fn delete_context(&mut self, context: Arc<C>);
    fn new_solver(&mut self, context: Arc<C>, options: &Options) -> Arc<SL>;
    fn delete_solver(&mut self, solver: Arc<SL>);
    fn new_interrupter(&self, solver: Arc<SL>) -> I;
    fn new_default_solver(&mut self, context: Arc<C>) -> Arc<SL> {
        self.new_solver(context, &Default::default())
    }
}

pub trait AsyncContext {}

pub trait ResultFactory<C, SL>
where
    C: AsyncContext,
    SL: ResultSolver,
{
    fn terminate(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn new_context(&self) -> Result<C, Box<dyn std::error::Error + Send + Sync>>;
    fn new_solver(
        &self,
        context: &C,
        options: &Options,
    ) -> Result<Arc<SL>, Box<dyn std::error::Error + Send + Sync>>;
    fn delete_context(&self, context: C) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn delete_solver(
        &self,
        solver: Arc<SL>,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
}

pub trait AsyncFactory<C, SL>
where
    C: AsyncContext,
    SL: AsyncSolver,
{
    fn terminate(&self);
    fn new_context(&self) -> Arc<C>;
    fn new_solver(&self, context: Arc<C>, options: &Options) -> Arc<SL>;
    fn delete_context(&self, context: Arc<C>);
    fn delete_solver(&self, solver: Arc<SL>);
}

pub trait GeneralSolver<S, T, O, C>
where
    S: GeneralSort,
    T: GeneralTerm,
    O: GeneralOptions,
    C: GeneralConverter<S, T>,
{
    fn eval(&self, term1: &T) -> Option<T>;
    fn assert(&self, term: &T);
    fn reset(&self);
    fn interrupt(&self);
    fn check_sat(&self) -> SolverResult;
    fn unsat_core(&self) -> Vec<T>;
    fn push(&self);
    fn pop(&self, size: u64);
}

pub trait ResultSolver {
    fn assert(&self, term: &Term) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn reset(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn interrupt(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn check_sat(&self) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>>;
    fn unsat_core(&self) -> Result<Vec<Term>, Box<dyn std::error::Error + Send + Sync>>;
    fn eval(&self, term: &Term) -> Result<Option<Term>, Box<dyn std::error::Error + Send + Sync>>;
    fn push(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn pop(&self, size: u64) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
}

pub trait AsyncSolver {
    fn assert(&self, term: &Term);
    fn reset(&self);
    fn interrupt(&self);
    fn check_sat(&self) -> SolverResult;
    fn unsat_core(&self) -> Vec<Term>;
    fn eval(&self, term: &Term) -> Option<Term>;
    fn push(&self);
    fn pop(&self, size: u64);
}

macro_rules! define_converter_unary_function {
    ($func_name:ident) => {
        fn $func_name(&self, term1: &T) -> T;
    };
}

macro_rules! define_converter_binary_function {
    ($func_name:ident) => {
        fn $func_name(&self, term1: &T, term2: &T) -> T;
    };
}

pub trait Context {}

macro_rules! define_converter_ternary_function {
    ($func_name:ident) => {
        fn $func_name(&self, term1: &T, term2: &T, term3: &T) -> T;
    };
}

macro_rules! define_converter_fp_unary_function {
    ($func_name:ident) => {
        fn $func_name(&self, r_mode: &RoundingMode, term1: &T) -> T;
    };
}

macro_rules! define_converter_fp_binary_function {
    ($func_name:ident) => {
        fn $func_name(&self, r_mode: &RoundingMode, term1: &T, term2: &T) -> T;
    };
}

pub trait GeneralConverter<S, T>
where
    S: GeneralSort,
    T: GeneralTerm,
{
    fn mk_smt_symbol(&self, name: &str, sort: &S) -> T;
    fn mk_smt_const_symbol(&self, term: &T, sort: &S) -> T;
    define_converter_binary_function!(mk_eq);

    fn convert_term(&self, term: &Term) -> T {
        match &term.term {
            UnsortedTerm::Constant(const_term) => match const_term {
                GenConstant::Numeral(x) => self
                    .try_get_bv_converter()
                    .unwrap()
                    .mk_bv_value_uint64(&self.convert_sort(&term.sort), *x),
                GenConstant::Boolean(x) => self.try_get_bool_converter().unwrap().mk_smt_bool(*x),
                GenConstant::Symbol(x) => self.mk_smt_symbol(x, &self.convert_sort(&term.sort)),
                GenConstant::ConstantSymbol(_) => todo!(),
                GenConstant::Fp(x) => {
                    let sort = self.convert_sort(&term.sort);

                    match x {
                        crate::term::FpConstant::PosZero => {
                            self.try_get_fp_converter().unwrap().mk_fp_pos_zero(&sort)
                        }
                        crate::term::FpConstant::PosInf => {
                            self.try_get_fp_converter().unwrap().mk_fp_pos_inf(&sort)
                        }
                        crate::term::FpConstant::NegZero => {
                            self.try_get_fp_converter().unwrap().mk_fp_neg_zero(&sort)
                        }
                        crate::term::FpConstant::NegInf => {
                            self.try_get_fp_converter().unwrap().mk_fp_neg_inf(&sort)
                        }
                    }
                }
            },
            UnsortedTerm::Operation(operation) => match operation.as_ref() {
                GenOperation::Uno(kind, term1) => {
                    let t1 = self.convert_term(term1);
                    match kind {
                        UnoOperationKind::Not => self.try_get_bool_converter().unwrap().mk_not(&t1),
                        UnoOperationKind::BvNeg => {
                            self.try_get_bv_converter().unwrap().mk_bv_neg(&t1)
                        }
                        UnoOperationKind::BvNot => {
                            self.try_get_bv_converter().unwrap().mk_bv_not(&t1)
                        }
                        UnoOperationKind::FpIsInf => {
                            self.try_get_fp_converter().unwrap().fp_is_inf(&t1)
                        }
                        UnoOperationKind::FpIsNan => {
                            self.try_get_fp_converter().unwrap().fp_is_nan(&t1)
                        }
                        UnoOperationKind::FpIsNorm => {
                            self.try_get_fp_converter().unwrap().fp_is_normal(&t1)
                        }
                        UnoOperationKind::FpIsSubnorm => {
                            self.try_get_fp_converter().unwrap().fp_is_subnormal(&t1)
                        }
                        UnoOperationKind::FpIsZero => {
                            self.try_get_fp_converter().unwrap().fp_is_zero(&t1)
                        }
                        UnoOperationKind::FpIsPos => {
                            self.try_get_fp_converter().unwrap().fp_is_pos(&t1)
                        }
                        UnoOperationKind::FpAbs => {
                            self.try_get_fp_converter().unwrap().mk_fp_abs(&t1)
                        }
                        UnoOperationKind::FpNeg => {
                            self.try_get_fp_converter().unwrap().mk_fp_neg(&t1)
                        }
                    }
                }
                GenOperation::Duo(kind, term1, term2) => {
                    let t1 = self.convert_term(term1);
                    let t2 = self.convert_term(term2);
                    match kind {
                        DuoOperationKind::Eq => self.mk_eq(&t1, &t2),
                        DuoOperationKind::And => {
                            self.try_get_bool_converter().unwrap().mk_and(&t1, &t2)
                        }
                        DuoOperationKind::Implies => {
                            self.try_get_bool_converter().unwrap().mk_implies(&t1, &t2)
                        }
                        DuoOperationKind::Neq => {
                            self.try_get_bool_converter().unwrap().mk_neq(&t1, &t2)
                        }
                        DuoOperationKind::Or => {
                            self.try_get_bool_converter().unwrap().mk_or(&t1, &t2)
                        }
                        DuoOperationKind::Xor => {
                            self.try_get_bool_converter().unwrap().mk_xor(&t1, &t2)
                        }
                        DuoOperationKind::Iff => {
                            self.try_get_bool_converter().unwrap().mk_iff(&t1, &t2)
                        }
                        DuoOperationKind::Select => {
                            self.try_get_array_converter().unwrap().mk_select(&t1, &t2)
                        }
                        DuoOperationKind::BvAdd => {
                            self.try_get_bv_converter().unwrap().mk_bv_add(&t1, &t2)
                        }
                        DuoOperationKind::BvAnd => {
                            self.try_get_bv_converter().unwrap().mk_bv_and(&t1, &t2)
                        }
                        DuoOperationKind::BvAshr => {
                            self.try_get_bv_converter().unwrap().mk_bv_ashr(&t1, &t2)
                        }
                        DuoOperationKind::BvLshr => {
                            self.try_get_bv_converter().unwrap().mk_bv_lshr(&t1, &t2)
                        }
                        DuoOperationKind::BvMul => {
                            self.try_get_bv_converter().unwrap().mk_bv_mul(&t1, &t2)
                        }
                        DuoOperationKind::BvNand => {
                            self.try_get_bv_converter().unwrap().mk_bv_nand(&t1, &t2)
                        }
                        DuoOperationKind::BvNor => {
                            self.try_get_bv_converter().unwrap().mk_bv_nor(&t1, &t2)
                        }
                        DuoOperationKind::BvNxor => {
                            self.try_get_bv_converter().unwrap().mk_bv_nxor(&t1, &t2)
                        }
                        DuoOperationKind::BvOr => {
                            self.try_get_bv_converter().unwrap().mk_bv_or(&t1, &t2)
                        }
                        DuoOperationKind::BvSdiv => {
                            self.try_get_bv_converter().unwrap().mk_bv_sdiv(&t1, &t2)
                        }
                        DuoOperationKind::BvSge => {
                            self.try_get_bv_converter().unwrap().mk_bv_sge(&t1, &t2)
                        }
                        DuoOperationKind::BvSgt => {
                            self.try_get_bv_converter().unwrap().mk_bv_sgt(&t1, &t2)
                        }
                        DuoOperationKind::BvShl => {
                            self.try_get_bv_converter().unwrap().mk_bv_shl(&t1, &t2)
                        }
                        DuoOperationKind::BvSle => {
                            self.try_get_bv_converter().unwrap().mk_bv_sle(&t1, &t2)
                        }
                        DuoOperationKind::BvSlt => {
                            self.try_get_bv_converter().unwrap().mk_bv_slt(&t1, &t2)
                        }
                        DuoOperationKind::BvSmod => {
                            self.try_get_bv_converter().unwrap().mk_bv_smod(&t1, &t2)
                        }
                        DuoOperationKind::BvSub => {
                            self.try_get_bv_converter().unwrap().mk_bv_sub(&t1, &t2)
                        }
                        DuoOperationKind::BvUdiv => {
                            self.try_get_bv_converter().unwrap().mk_bv_udiv(&t1, &t2)
                        }
                        DuoOperationKind::BvUge => {
                            self.try_get_bv_converter().unwrap().mk_bv_uge(&t1, &t2)
                        }
                        DuoOperationKind::BvUgt => {
                            self.try_get_bv_converter().unwrap().mk_bv_ugt(&t1, &t2)
                        }
                        DuoOperationKind::BvUle => {
                            self.try_get_bv_converter().unwrap().mk_bv_ule(&t1, &t2)
                        }
                        DuoOperationKind::BvUlt => {
                            self.try_get_bv_converter().unwrap().mk_bv_ult(&t1, &t2)
                        }
                        DuoOperationKind::BvUrem => {
                            self.try_get_bv_converter().unwrap().mk_bv_urem(&t1, &t2)
                        }
                        DuoOperationKind::BvSrem => {
                            self.try_get_bv_converter().unwrap().mk_bv_srem(&t1, &t2)
                        }
                        DuoOperationKind::BvXor => {
                            self.try_get_bv_converter().unwrap().mk_bv_xor(&t1, &t2)
                        }
                        DuoOperationKind::FpEq => {
                            self.try_get_fp_converter().unwrap().mk_fp_eq(&t1, &t2)
                        }
                        DuoOperationKind::Concat => {
                            self.try_get_bv_converter().unwrap().mk_concat(&t1, &t2)
                        }
                        DuoOperationKind::FpRem => {
                            self.try_get_fp_converter().unwrap().mk_fp_rem(&t1, &t2)
                        }
                        DuoOperationKind::FpMin => {
                            self.try_get_fp_converter().unwrap().mk_fp_min(&t1, &t2)
                        }
                        DuoOperationKind::FpMax => {
                            self.try_get_fp_converter().unwrap().mk_fp_max(&t1, &t2)
                        }
                        DuoOperationKind::FpLT => {
                            self.try_get_fp_converter().unwrap().mk_fp_lt(&t1, &t2)
                        }
                        DuoOperationKind::FpLEQ => {
                            self.try_get_fp_converter().unwrap().mk_fp_leq(&t1, &t2)
                        }
                        DuoOperationKind::FpGT => {
                            self.try_get_fp_converter().unwrap().mk_fp_gt(&t1, &t2)
                        }
                        DuoOperationKind::FpGEQ => {
                            self.try_get_fp_converter().unwrap().mk_fp_geq(&t1, &t2)
                        }
                    }
                }
                GenOperation::Trio(kind, term1, term2, term3) => {
                    let t1 = self.convert_term(term1);
                    let t2 = self.convert_term(term2);
                    let t3 = self.convert_term(term3);
                    match kind {
                        TrioOperationKind::Store => self
                            .try_get_array_converter()
                            .unwrap()
                            .mk_store(&t1, &t2, &t3),
                        TrioOperationKind::Fp => {
                            self.try_get_fp_converter().unwrap().mk_fp(&t1, &t2, &t3)
                        }
                        TrioOperationKind::Ite => {
                            self.try_get_bool_converter().unwrap().mk_ite(&t1, &t2, &t3)
                        }
                    }
                }
                GenOperation::Extract(high, low, term) => {
                    let t = self.convert_term(term);
                    self.try_get_bv_converter()
                        .unwrap()
                        .mk_extract(*high, *low, &t)
                }
                GenOperation::FpUno(kind, rmode, term) => {
                    let t = self.convert_term(term);
                    match kind {
                        FpUnoOperationKind::FpSqrt => {
                            self.try_get_fp_converter().unwrap().mk_fp_sqrt(rmode, &t)
                        }
                        FpUnoOperationKind::FpRti => {
                            self.try_get_fp_converter().unwrap().mk_fp_rti(rmode, &t)
                        }
                    }
                }
                GenOperation::FpDuo(kind, rmode, term1, term2) => {
                    let t1 = self.convert_term(term1);
                    let t2 = self.convert_term(term2);
                    match kind {
                        FpDuoOperationKind::FpAdd => self
                            .try_get_fp_converter()
                            .unwrap()
                            .mk_fp_add(rmode, &t1, &t2),
                        FpDuoOperationKind::FpSub => self
                            .try_get_fp_converter()
                            .unwrap()
                            .mk_fp_sub(rmode, &t1, &t2),
                        FpDuoOperationKind::FpMul => self
                            .try_get_fp_converter()
                            .unwrap()
                            .mk_fp_mul(rmode, &t1, &t2),
                        FpDuoOperationKind::FpDiv => self
                            .try_get_fp_converter()
                            .unwrap()
                            .mk_fp_div(rmode, &t1, &t2),
                    }
                }
                GenOperation::FpToFp(kind, rmode, ew, sw, term) => {
                    let t = self.convert_term(term);
                    match kind {
                        crate::term::FpToFpOperationKind::FromFp => self
                            .try_get_fp_converter()
                            .unwrap()
                            .mk_fp_to_fp_from_fp(rmode, &t, *ew, *sw),
                        crate::term::FpToFpOperationKind::FromSBv => self
                            .try_get_fp_converter()
                            .unwrap()
                            .mk_fp_to_fp_from_sbv(rmode, &t, *ew, *sw),
                        crate::term::FpToFpOperationKind::FromUBv => self
                            .try_get_fp_converter()
                            .unwrap()
                            .mk_fp_to_fp_from_ubv(rmode, &t, *ew, *sw),
                    }
                }
                GenOperation::FpTo(kind, rmode, w, term) => {
                    let t = self.convert_term(term);
                    match kind {
                        crate::term::FpToOperationKind::SBv => self
                            .try_get_fp_converter()
                            .unwrap()
                            .mk_fp_to_sbv(rmode, &t, *w),
                        crate::term::FpToOperationKind::UBv => self
                            .try_get_fp_converter()
                            .unwrap()
                            .mk_fp_to_ubv(rmode, &t, *w),
                    }
                }
                GenOperation::Extend(kind, size, term) => {
                    let t = self.convert_term(term);
                    match kind {
                        crate::term::ExtendOperationKind::Sign => self
                            .try_get_bv_converter()
                            .unwrap()
                            .mk_sign_extend(*size, &t),
                        crate::term::ExtendOperationKind::Zero => self
                            .try_get_bv_converter()
                            .unwrap()
                            .mk_zero_extend(*size, &t),
                    }
                }
                GenOperation::FpToFpFromBv(ew, sw, term) => {
                    let t = self.convert_term(term);
                    self.try_get_fp_converter()
                        .unwrap()
                        .mk_fp_to_fp_from_bv(&t, *ew, *sw)
                }
            },
        }
    }

    fn convert_sort(&self, sort: &Sort) -> S {
        match sort {
            Sort::BvSort(x) => self.try_get_bv_converter().unwrap().mk_bv_sort(*x),
            Sort::BoolSort() => self.try_get_bool_converter().unwrap().mk_bool_sort(),
            Sort::ArraySort(index, element) => self
                .try_get_array_converter()
                .unwrap()
                .mk_array_sort(&self.convert_sort(index), &self.convert_sort(element)),
            Sort::FpSort(ew, sw) => self.try_get_fp_converter().unwrap().mk_fp_sort(*ew, *sw),
        }
    }

    fn try_get_bool_converter(&self) -> Option<&dyn GeneralBoolConverter<S, T>>;
    fn try_get_bv_converter(&self) -> Option<&dyn GeneralBvConverter<S, T>>;
    fn try_get_array_converter(&self) -> Option<&dyn GeneralArrayConverter<S, T>>;
    fn try_get_fp_converter(&self) -> Option<&dyn GeneralFpConverter<S, T>>;
}

pub trait GeneralFpConverter<S, T>: GeneralConverter<S, T>
where
    S: GeneralSort,
    T: GeneralTerm,
{
    fn mk_fp_sort(&self, ew: u64, sw: u64) -> S;
    fn mk_fp(&self, bv_sign: &T, bv_exponent: &T, bv_significand: &T) -> T;
    fn mk_fp_pos_zero(&self, sort: &S) -> T;
    fn mk_fp_pos_inf(&self, sort: &S) -> T;
    fn mk_fp_neg_zero(&self, sort: &S) -> T;
    fn mk_fp_neg_inf(&self, sort: &S) -> T;

    fn fp_get_bv_exp_size(&self, term: &T) -> u64;
    fn fp_get_bv_sig_size(&self, term: &T) -> u64;
    fn fp_is_nan(&self, term: &T) -> T;
    fn fp_is_inf(&self, term: &T) -> T;
    fn fp_is_normal(&self, term: &T) -> T;
    fn fp_is_subnormal(&self, term: &T) -> T;
    fn fp_is_zero(&self, term: &T) -> T;
    fn fp_is_pos(&self, term: &T) -> T;

    fn mk_fp_eq(&self, term1: &T, term2: &T) -> T;
    define_converter_fp_binary_function!(mk_fp_add);
    define_converter_fp_binary_function!(mk_fp_sub);
    define_converter_fp_binary_function!(mk_fp_mul);
    define_converter_fp_binary_function!(mk_fp_div);
    define_converter_binary_function!(mk_fp_rem);
    define_converter_binary_function!(mk_fp_min);
    define_converter_binary_function!(mk_fp_max);
    define_converter_binary_function!(mk_fp_lt); //less than
    define_converter_binary_function!(mk_fp_leq); //less or equal than
    define_converter_binary_function!(mk_fp_gt); //greater than
    define_converter_binary_function!(mk_fp_geq); //greater or equal than
    define_converter_fp_unary_function!(mk_fp_sqrt);
    define_converter_fp_unary_function!(mk_fp_rti);
    define_converter_unary_function!(mk_fp_abs);
    define_converter_unary_function!(mk_fp_neg);

    fn get_rouning_mode(&self, r_mode: &RoundingMode) -> T;

    fn mk_fp_to_fp_from_fp(&self, r_mode: &RoundingMode, term: &T, ew: u64, sw: u64) -> T;
    fn mk_fp_to_sbv(&self, r_mode: &RoundingMode, term: &T, w: u64) -> T;
    fn mk_fp_to_ubv(&self, r_mode: &RoundingMode, term: &T, w: u64) -> T;
    fn mk_fp_to_fp_from_sbv(&self, r_mode: &RoundingMode, term: &T, ew: u64, sw: u64) -> T;
    fn mk_fp_to_fp_from_ubv(&self, r_mode: &RoundingMode, term: &T, ew: u64, sw: u64) -> T;
    fn mk_fp_to_fp_from_bv(&self, term: &T, ew: u64, sw: u64) -> T;
}

pub trait GeneralBoolConverter<S, T>: GeneralConverter<S, T>
where
    S: GeneralSort,
    T: GeneralTerm,
{
    fn mk_bool_sort(&self) -> S;
    fn mk_smt_bool(&self, val: bool) -> T;
    define_converter_unary_function!(mk_not);
    define_converter_binary_function!(mk_implies);
    define_converter_binary_function!(mk_neq);
    define_converter_binary_function!(mk_and);
    define_converter_binary_function!(mk_or);
    define_converter_binary_function!(mk_xor);
    define_converter_binary_function!(mk_iff);
    define_converter_ternary_function!(mk_ite);
}

pub trait GeneralBvConverter<S, T>: GeneralConverter<S, T>
where
    S: GeneralSort,
    T: GeneralTerm,
{
    fn mk_bv_sort(&self, size: u64) -> S;
    fn mk_bv_value_uint64(&self, sort: &S, val: u64) -> T;
    define_converter_unary_function!(mk_bv_neg);
    define_converter_unary_function!(mk_bv_not);
    define_converter_binary_function!(mk_bv_add);
    define_converter_binary_function!(mk_bv_and);
    define_converter_binary_function!(mk_bv_ashr);
    define_converter_binary_function!(mk_bv_lshr);
    define_converter_binary_function!(mk_bv_mul);
    define_converter_binary_function!(mk_bv_nand);
    define_converter_binary_function!(mk_bv_nor);
    define_converter_binary_function!(mk_bv_nxor);
    define_converter_binary_function!(mk_bv_or);
    define_converter_binary_function!(mk_bv_sdiv);
    define_converter_binary_function!(mk_bv_sge);
    define_converter_binary_function!(mk_bv_sgt);
    define_converter_binary_function!(mk_bv_shl);
    define_converter_binary_function!(mk_bv_sle);
    define_converter_binary_function!(mk_bv_slt);
    define_converter_binary_function!(mk_bv_smod);
    define_converter_binary_function!(mk_bv_srem);
    define_converter_binary_function!(mk_bv_sub);
    define_converter_binary_function!(mk_bv_udiv);
    define_converter_binary_function!(mk_bv_uge);
    define_converter_binary_function!(mk_bv_ugt);
    define_converter_binary_function!(mk_bv_ule);
    define_converter_binary_function!(mk_bv_ult);
    define_converter_binary_function!(mk_bv_urem);
    define_converter_binary_function!(mk_bv_xor);
    define_converter_binary_function!(mk_concat);
    fn mk_extract(&self, high: u64, low: u64, term: &T) -> T;
    fn mk_sign_extend(&self, size: u64, term: &T) -> T;
    fn mk_zero_extend(&self, size: u64, term: &T) -> T;
}

pub trait GeneralArrayConverter<S, T>: GeneralConverter<S, T>
where
    S: GeneralSort,
    T: GeneralTerm,
{
    fn mk_array_sort(&self, index: &S, element: &S) -> S;
    define_converter_binary_function!(mk_select);
    define_converter_ternary_function!(mk_store);
}

pub trait Interrupter {
    fn interrupt(&self);
}

pub trait Solver {
    fn assert(&self, term: &Term);
    fn reset(&self);
    fn check_sat(&self) -> SolverResult;
    fn eval(&self, term: &Term) -> Option<Term>;
    fn unsat_core(&self) -> Vec<Term>;
    fn push(&self);
    fn pop(&self, size: u64);
}

#[derive(PartialEq, Eq, Hash, Serialize, Deserialize, Debug, Clone)]
pub enum OptionKind {
    ProduceUnsatCore,
}

#[derive(Default, PartialEq, Eq, Serialize, Deserialize, Debug, Clone)]
pub struct Options {
    pub bool_options: HashMap<OptionKind, bool>,
    pub external_timeout: Option<Duration>,
}

impl Options {
    pub fn set_produce_unsat_core(&mut self, val: bool) {
        self.bool_options.insert(OptionKind::ProduceUnsatCore, val);
    }
    pub fn get_produce_unsat_core(&self) -> bool {
        *self
            .bool_options
            .get(&OptionKind::ProduceUnsatCore)
            .unwrap_or(&false)
    }
    pub fn set_external_timeout(&mut self, val: Option<Duration>) {
        self.external_timeout = val;
    }
    pub fn get_external_timeout(&self) -> Option<Duration> {
        self.external_timeout
    }
}

pub trait GeneralOptions {
    fn set_produce_unsat_core(&self, val: bool);
    fn get_produce_unsat_core(&self) -> bool;
}
