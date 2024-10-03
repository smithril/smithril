use core::fmt;
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, sync::Arc, time::Duration};

pub trait GeneralSort {}

pub trait GeneralTerm {}

pub enum TheoryKind {
    Bool,
    Fp,
    Bv,
    Array,
    Native,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum RoundingMode {
    RNA,
    RNE,
    RTN,
    RTP,
    RTZ,
}

pub trait TheoryDefinition {
    fn define_theory(&self) -> TheoryKind;
}

impl TheoryDefinition for Term {
    fn define_theory(&self) -> TheoryKind {
        match &self.term {
            UnsortedTerm::Constant(const_term) => match const_term {
                GenConstant::Numeral(_) => TheoryKind::Bv,
                GenConstant::Boolean(_) => TheoryKind::Bool,
                GenConstant::Symbol(_) => TheoryKind::Native,
            },
            UnsortedTerm::Operation(operation) => match operation.as_ref() {
                GenOperation::Uno(kind, _) => match kind {
                    UnoOperationKind::Not => TheoryKind::Bool,
                    UnoOperationKind::BvNeg => TheoryKind::Bv,
                    UnoOperationKind::BvNot => TheoryKind::Bv,
                    UnoOperationKind::FpIsInf => TheoryKind::Fp,
                    UnoOperationKind::FpIsNan => TheoryKind::Fp,
                    UnoOperationKind::FpIsNorm => TheoryKind::Fp,
                    UnoOperationKind::FpIsSubnorm => TheoryKind::Fp,
                    UnoOperationKind::FpIsZero => TheoryKind::Fp,
                },
                GenOperation::Duo(kind, _, _) => match kind {
                    DuoOperationKind::Eq => TheoryKind::Native,
                    DuoOperationKind::And => TheoryKind::Bool,
                    DuoOperationKind::Implies => TheoryKind::Bool,
                    DuoOperationKind::Neq => TheoryKind::Bool,
                    DuoOperationKind::Or => TheoryKind::Bool,
                    DuoOperationKind::Xor => TheoryKind::Bool,
                    DuoOperationKind::Select => TheoryKind::Array,
                    DuoOperationKind::BvAdd => TheoryKind::Bv,
                    DuoOperationKind::BvAnd => TheoryKind::Bv,
                    DuoOperationKind::BvAshr => TheoryKind::Bv,
                    DuoOperationKind::BvLshr => TheoryKind::Bv,
                    DuoOperationKind::BvMul => TheoryKind::Bv,
                    DuoOperationKind::BvNand => TheoryKind::Bv,
                    DuoOperationKind::BvNor => TheoryKind::Bv,
                    DuoOperationKind::BvNxor => TheoryKind::Bv,
                    DuoOperationKind::BvOr => TheoryKind::Bv,
                    DuoOperationKind::BvSdiv => TheoryKind::Bv,
                    DuoOperationKind::BvSge => TheoryKind::Bv,
                    DuoOperationKind::BvSgt => TheoryKind::Bv,
                    DuoOperationKind::BvShl => TheoryKind::Bv,
                    DuoOperationKind::BvSle => TheoryKind::Bv,
                    DuoOperationKind::BvSlt => TheoryKind::Bv,
                    DuoOperationKind::BvSmod => TheoryKind::Bv,
                    DuoOperationKind::BvSub => TheoryKind::Bv,
                    DuoOperationKind::BvUdiv => TheoryKind::Bv,
                    DuoOperationKind::BvUge => TheoryKind::Bv,
                    DuoOperationKind::BvUgt => TheoryKind::Bv,
                    DuoOperationKind::BvUle => TheoryKind::Bv,
                    DuoOperationKind::BvUlt => TheoryKind::Bv,
                    DuoOperationKind::BvUmod => TheoryKind::Bv,
                    DuoOperationKind::BvXor => TheoryKind::Bv,
                    DuoOperationKind::FpEq => TheoryKind::Fp,
                    DuoOperationKind::Concat => TheoryKind::Bv,
                },
                GenOperation::Trio(kind, _, _, _) => match kind {
                    TrioOperationKind::Store => TheoryKind::Array,
                    TrioOperationKind::MkFpValue => TheoryKind::Fp,
                },
                GenOperation::FpUno(_, _, _) => TheoryKind::Fp,
                GenOperation::FpDuo(_, _, _, _) => TheoryKind::Fp,
                GenOperation::Extract(_, _, _) => TheoryKind::Bv,
            },
        }
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub struct FloatingPointAsBvStr {
    pub sign: String,
    pub exponent: String,
    pub significand: String,
}

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
    FpIsInf,
    FpIsNan,
    FpIsNorm,
    FpIsSubnorm,
    FpIsZero,
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

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Clone, Hash)]
pub enum GenOperation {
    Uno(UnoOperationKind, Term),
    Extract(Term, u64, u64),
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

pub trait AsyncResultFactory<C, SL>
where
    C: AsyncContext,
    SL: AsyncResultSolver,
{
    fn terminate(
        &self,
    ) -> impl std::future::Future<Output = Result<(), Box<dyn std::error::Error + Send + Sync>>> + Send;
    fn new_context(
        &self,
    ) -> impl std::future::Future<Output = Result<C, Box<dyn std::error::Error + Send + Sync>>> + Send;
    fn new_solver(
        &self,
        context: &C,
        options: &Options,
    ) -> impl std::future::Future<Output = Result<Arc<SL>, Box<dyn std::error::Error + Send + Sync>>>
           + Send;
    fn delete_context(
        &self,
        context: C,
    ) -> impl std::future::Future<Output = Result<(), Box<dyn std::error::Error + Send + Sync>>> + Send;
    fn delete_solver(
        &self,
        solver: Arc<SL>,
    ) -> impl std::future::Future<Output = Result<(), Box<dyn std::error::Error + Send + Sync>>> + Send;
}

pub trait AsyncFactory<C, SL>
where
    C: AsyncContext,
    SL: AsyncSolver,
{
    fn terminate(&self) -> impl std::future::Future<Output = ()> + Send;
    fn new_context(&self) -> impl std::future::Future<Output = Arc<C>> + Send;
    fn new_solver(
        &self,
        context: Arc<C>,
        options: &Options,
    ) -> impl std::future::Future<Output = Arc<SL>> + Send;
    fn delete_context(&self, context: Arc<C>) -> impl std::future::Future<Output = ()> + Send;
    fn delete_solver(&self, solver: Arc<SL>) -> impl std::future::Future<Output = ()> + Send;
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
}

pub trait AsyncResultSolver {
    fn assert(
        &self,
        term: &Term,
    ) -> impl std::future::Future<Output = Result<(), Box<dyn std::error::Error + Send + Sync>>> + Send;
    fn reset(
        &self,
    ) -> impl std::future::Future<Output = Result<(), Box<dyn std::error::Error + Send + Sync>>> + Send;
    fn interrupt(
        &self,
    ) -> impl std::future::Future<Output = Result<(), Box<dyn std::error::Error + Send + Sync>>> + Send;
    fn check_sat(
        &self,
    ) -> impl std::future::Future<
        Output = Result<SolverResult, Box<dyn std::error::Error + Send + Sync>>,
    > + Send;
    fn unsat_core(
        &self,
    ) -> impl std::future::Future<Output = Result<Vec<Term>, Box<dyn std::error::Error + Send + Sync>>>
           + Send;
    fn eval(
        &self,
        term: &Term,
    ) -> impl std::future::Future<
        Output = Result<Option<Term>, Box<dyn std::error::Error + Send + Sync>>,
    > + Send;
}

pub trait AsyncSolver {
    fn assert(&self, term: &Term) -> impl std::future::Future<Output = ()> + Send;
    fn reset(&self) -> impl std::future::Future<Output = ()> + Send;
    fn interrupt(&self) -> impl std::future::Future<Output = ()> + Send;
    fn check_sat(&self) -> impl std::future::Future<Output = SolverResult> + Send;
    fn unsat_core(&self) -> impl std::future::Future<Output = Vec<Term>> + Send;
    fn eval(&self, term: &Term) -> impl std::future::Future<Output = Option<Term>> + Send;
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
    define_converter_binary_function!(mk_eq);

    fn convert_term(&self, term: &Term) -> T {
        match term.define_theory() {
            TheoryKind::Bool => self
                .try_get_bool_converter()
                .unwrap()
                .convert_bool_term(term)
                .unwrap(),
            TheoryKind::Bv => self
                .try_get_bv_converter()
                .unwrap()
                .convert_bv_term(term)
                .unwrap(),

            TheoryKind::Array => self
                .try_get_array_converter()
                .unwrap()
                .convert_array_term(term)
                .unwrap(),

            TheoryKind::Fp => self
                .try_get_fp_converter()
                .unwrap()
                .convert_fp_term(term)
                .unwrap(),

            TheoryKind::Native => match &term.term {
                UnsortedTerm::Constant(const_term) => match const_term {
                    GenConstant::Symbol(x) => self.mk_smt_symbol(x, &self.convert_sort(&term.sort)),
                    _ => panic!("Unsupported term type"),
                },
                UnsortedTerm::Operation(operation) => match operation.as_ref() {
                    GenOperation::Duo(kind, term1, term2) => match kind {
                        DuoOperationKind::Eq => {
                            self.mk_eq(&self.convert_term(term1), &self.convert_term(term2))
                        }
                        _ => panic!("Unsupported DuoOperation type"),
                    },
                    _ => panic!("Unsupported GenOperation type"),
                },
            },
        }
    }

    fn convert_sort(&self, sort: &Sort) -> S {
        match sort {
            Sort::BvSort(_) => self
                .try_get_bv_converter()
                .unwrap()
                .convert_bv_sort(sort)
                .unwrap(),
            Sort::BoolSort() => self
                .try_get_bool_converter()
                .unwrap()
                .convert_bool_sort(sort)
                .unwrap(),
            Sort::ArraySort(_, _) => self
                .try_get_array_converter()
                .unwrap()
                .convert_array_sort(sort)
                .unwrap(),
            Sort::FpSort(_, _) => self
                .try_get_fp_converter()
                .unwrap()
                .convert_fp_sort(sort)
                .unwrap(),
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
    fn mk_fp_value(&self, bv_sign: &T, bv_exponent: &T, bv_significand: &T) -> T;
    fn mk_fp_pos_zero(&self, ew: u64, sw: u64) -> T;
    fn mk_fp_pos_inf(&self, ew: u64, sw: u64) -> T;
    fn mk_fp_neg_zero(&self, ew: u64, sw: u64) -> T;
    fn mk_fp_neg_inf(&self, ew: u64, sw: u64) -> T;

    fn fp_get_bv_exp_size(&self, term: &T) -> u64;
    fn fp_get_bv_sig_size(&self, term: &T) -> u64;
    fn fp_get_values_ieee(&self, term: &T) -> FloatingPointAsBvStr;
    fn fp_is_nan(&self, term: &T) -> T;
    fn fp_is_inf(&self, term: &T) -> T;
    fn fp_is_normal(&self, term: &T) -> T;
    fn fp_is_subnormal(&self, term: &T) -> T;
    fn fp_is_zero(&self, term: &T) -> T;
    fn fp_is_pos(&self, term: &T) -> T;

    fn fp_eq(&self, term1: &T, term2: &T) -> T;
    define_converter_fp_binary_function!(mk_fp_rem);
    define_converter_fp_binary_function!(mk_fp_min);
    define_converter_fp_binary_function!(mk_fp_max);
    define_converter_fp_binary_function!(mk_fp_lt); //less than
    define_converter_fp_binary_function!(mk_fp_leq); //less or equal than
    define_converter_fp_binary_function!(mk_fp_gt); //greater than
    define_converter_fp_binary_function!(mk_fp_geq); //greater or equal than
    define_converter_fp_binary_function!(mk_fp_add);
    define_converter_fp_binary_function!(mk_fp_sub);
    define_converter_fp_binary_function!(mk_fp_mul);
    define_converter_fp_binary_function!(mk_fp_div);

    define_converter_fp_unary_function!(mk_fp_sqrt);
    define_converter_fp_unary_function!(mk_fp_rti);
    define_converter_fp_unary_function!(mk_fp_abs);
    define_converter_fp_unary_function!(mk_fp_neg);

    fn get_rouning_mode(&self, r_mode: RoundingMode) -> T;

    fn mk_fp_to_fp_from_fp(&self, rmterm: &T, term1: &T, ew: u64, sw: u64) -> T;
    fn mk_fp_to_sbv(&self, rmterm: &T, term1: &T, w: u64) -> T;
    fn mk_fp_to_ubv(&self, rmterm: &T, term1: &T, w: u64) -> T;
    fn mk_fp_to_fp_from_sbv(&self, rmterm: &T, term1: &T, ew: u64, sw: u64) -> T;
    fn mk_fp_to_fp_from_ubv(&self, rmterm: &T, term1: &T, ew: u64, sw: u64) -> T;

    fn convert_fp_term(&self, term: &Term) -> Option<T> {
        match &term.term {
            UnsortedTerm::Constant(_const_term) => None,
            UnsortedTerm::Operation(operation) => match operation.as_ref() {
                GenOperation::Uno(kind, term1) => {
                    let t1 = self.convert_term(term1);
                    match kind {
                        UnoOperationKind::FpIsInf => Some(self.fp_is_inf(&t1)),
                        UnoOperationKind::FpIsNan => Some(self.fp_is_nan(&t1)),
                        UnoOperationKind::FpIsNorm => Some(self.fp_is_normal(&t1)),
                        UnoOperationKind::FpIsSubnorm => Some(self.fp_is_subnormal(&t1)),
                        UnoOperationKind::FpIsZero => Some(self.fp_is_zero(&t1)),
                        _ => None,
                    }
                }
                GenOperation::Duo(kind, term1, term2) => {
                    let t1 = self.convert_term(term1);
                    let t2 = self.convert_term(term2);
                    match kind {
                        DuoOperationKind::FpEq => Some(self.fp_eq(&t1, &t2)),
                        _ => None,
                    }
                }
                GenOperation::Trio(kind, term1, term2, term3) => {
                    let t1 = self.convert_term(term1);
                    let t2 = self.convert_term(term2);
                    let t3 = self.convert_term(term3);
                    match kind {
                        TrioOperationKind::MkFpValue => Some(self.mk_fp_value(&t1, &t2, &t3)),
                        _ => None,
                    }
                }
                GenOperation::FpUno(kind, r_mode, term1) => {
                    let t1 = self.convert_term(term1);
                    match kind {
                        FpUnoOperationKind::FpSqrt => Some(self.mk_fp_sqrt(r_mode, &t1)),
                        FpUnoOperationKind::FpRti => Some(self.mk_fp_rti(r_mode, &t1)),
                        FpUnoOperationKind::FpAbs => Some(self.mk_fp_abs(r_mode, &t1)),
                        FpUnoOperationKind::FpNeg => Some(self.mk_fp_neg(r_mode, &t1)),
                    }
                }
                GenOperation::FpDuo(kind, r_mode, term1, term2) => {
                    let t1 = self.convert_term(term1);
                    let t2 = self.convert_term(term2);
                    match kind {
                        FpDuoOperationKind::FpMin => Some(self.mk_fp_min(r_mode, &t1, &t2)),
                        FpDuoOperationKind::FpMax => Some(self.mk_fp_max(r_mode, &t1, &t2)),
                        FpDuoOperationKind::FpLT => Some(self.mk_fp_lt(r_mode, &t1, &t2)),
                        FpDuoOperationKind::FpLEQ => Some(self.mk_fp_leq(r_mode, &t1, &t2)),
                        FpDuoOperationKind::FpGT => Some(self.mk_fp_gt(r_mode, &t1, &t2)),
                        FpDuoOperationKind::FpGEQ => Some(self.mk_fp_geq(r_mode, &t1, &t2)),
                        FpDuoOperationKind::FpAdd => Some(self.mk_fp_add(r_mode, &t1, &t2)),
                        FpDuoOperationKind::FpSub => Some(self.mk_fp_sub(r_mode, &t1, &t2)),
                        FpDuoOperationKind::FpMul => Some(self.mk_fp_mul(r_mode, &t1, &t2)),
                        FpDuoOperationKind::FpDiv => Some(self.mk_fp_div(r_mode, &t1, &t2)),
                        FpDuoOperationKind::FpRem => Some(self.mk_fp_rem(r_mode, &t1, &t2)),
                    }
                }
                GenOperation::Extract(_, _, _) => None,
            },
        }
    }
    fn convert_fp_sort(&self, sort: &Sort) -> Option<S> {
        match sort {
            Sort::FpSort(exp, sig) => Some(self.mk_fp_sort(*exp, *sig)),
            _ => None,
        }
    }
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
    fn convert_bool_term(&self, term: &Term) -> Option<T> {
        match &term.term {
            UnsortedTerm::Constant(const_term) => match const_term {
                GenConstant::Boolean(x) => Some(self.mk_smt_bool(*x)),
                _ => None,
            },
            UnsortedTerm::Operation(operation) => match operation.as_ref() {
                GenOperation::Uno(kind, term1) => {
                    let t1 = self.convert_term(term1);
                    match kind {
                        UnoOperationKind::Not => Some(self.mk_not(&t1)),
                        _ => None,
                    }
                }
                GenOperation::Duo(kind, term1, term2) => {
                    let t1 = self.convert_term(term1);
                    let t2 = self.convert_term(term2);
                    match kind {
                        DuoOperationKind::And => Some(self.mk_and(&t1, &t2)),
                        DuoOperationKind::Implies => Some(self.mk_implies(&t1, &t2)),
                        DuoOperationKind::Neq => Some(self.mk_neq(&t1, &t2)),
                        DuoOperationKind::Or => Some(self.mk_or(&t1, &t2)),
                        DuoOperationKind::Xor => Some(self.mk_xor(&t1, &t2)),
                        _ => None,
                    }
                }
                _ => None,
            },
        }
    }
    fn convert_bool_sort(&self, sort: &Sort) -> Option<S> {
        match sort {
            Sort::BoolSort() => Some(self.mk_bool_sort()),
            _ => None,
        }
    }
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
    define_converter_binary_function!(mk_bv_sub);
    define_converter_binary_function!(mk_bv_udiv);
    define_converter_binary_function!(mk_bv_uge);
    define_converter_binary_function!(mk_bv_ugt);
    define_converter_binary_function!(mk_bv_ule);
    define_converter_binary_function!(mk_bv_ult);
    define_converter_binary_function!(mk_bv_umod);
    define_converter_binary_function!(mk_bv_xor);
    define_converter_binary_function!(mk_concat);
    fn mk_extract(&self, high: u64, low: u64, term: &T) -> T;
    fn convert_bv_term(&self, term: &Term) -> Option<T> {
        match &term.term {
            UnsortedTerm::Constant(const_term) => match const_term {
                GenConstant::Numeral(x) => {
                    Some(self.mk_bv_value_uint64(&self.convert_sort(&term.sort), *x))
                }
                GenConstant::Symbol(x) => {
                    Some(self.mk_smt_symbol(x, &self.convert_sort(&term.sort)))
                }
                _ => None,
            },
            UnsortedTerm::Operation(operation) => match operation.as_ref() {
                GenOperation::Uno(kind, term1) => {
                    let t1 = self.convert_term(term1);
                    match kind {
                        UnoOperationKind::BvNeg => Some(self.mk_bv_neg(&t1)),
                        UnoOperationKind::BvNot => Some(self.mk_bv_not(&t1)),
                        _ => None,
                    }
                }
                GenOperation::Duo(kind, term1, term2) => {
                    let t1 = self.convert_term(term1);
                    let t2 = self.convert_term(term2);
                    match kind {
                        DuoOperationKind::BvAdd => Some(self.mk_bv_add(&t1, &t2)),
                        DuoOperationKind::BvAnd => Some(self.mk_bv_and(&t1, &t2)),
                        DuoOperationKind::BvAshr => Some(self.mk_bv_ashr(&t1, &t2)),
                        DuoOperationKind::BvLshr => Some(self.mk_bv_lshr(&t1, &t2)),
                        DuoOperationKind::BvMul => Some(self.mk_bv_mul(&t1, &t2)),
                        DuoOperationKind::BvNand => Some(self.mk_bv_nand(&t1, &t2)),
                        DuoOperationKind::BvNor => Some(self.mk_bv_nor(&t1, &t2)),
                        DuoOperationKind::BvNxor => Some(self.mk_bv_nxor(&t1, &t2)),
                        DuoOperationKind::BvOr => Some(self.mk_bv_or(&t1, &t2)),
                        DuoOperationKind::BvSdiv => Some(self.mk_bv_sdiv(&t1, &t2)),
                        DuoOperationKind::BvSge => Some(self.mk_bv_sge(&t1, &t2)),
                        DuoOperationKind::BvSgt => Some(self.mk_bv_sgt(&t1, &t2)),
                        DuoOperationKind::BvShl => Some(self.mk_bv_shl(&t1, &t2)),
                        DuoOperationKind::BvSle => Some(self.mk_bv_sle(&t1, &t2)),
                        DuoOperationKind::BvSlt => Some(self.mk_bv_slt(&t1, &t2)),
                        DuoOperationKind::BvSmod => Some(self.mk_bv_smod(&t1, &t2)),
                        DuoOperationKind::BvSub => Some(self.mk_bv_sub(&t1, &t2)),
                        DuoOperationKind::BvUdiv => Some(self.mk_bv_udiv(&t1, &t2)),
                        DuoOperationKind::BvUge => Some(self.mk_bv_uge(&t1, &t2)),
                        DuoOperationKind::BvUgt => Some(self.mk_bv_ugt(&t1, &t2)),
                        DuoOperationKind::BvUle => Some(self.mk_bv_ule(&t1, &t2)),
                        DuoOperationKind::BvUlt => Some(self.mk_bv_ult(&t1, &t2)),
                        DuoOperationKind::BvUmod => Some(self.mk_bv_umod(&t1, &t2)),
                        DuoOperationKind::BvXor => Some(self.mk_bv_xor(&t1, &t2)),
                        DuoOperationKind::Concat => Some(self.mk_concat(&t1, &t2)),
                        _ => None,
                    }
                }
                _ => None,
            },
        }
    }
    fn convert_bv_sort(&self, sort: &Sort) -> Option<S> {
        match sort {
            Sort::BvSort(x) => Some(self.mk_bv_sort(*x)),
            _ => None,
        }
    }
}

pub trait GeneralArrayConverter<S, T>: GeneralConverter<S, T>
where
    S: GeneralSort,
    T: GeneralTerm,
{
    fn mk_array_sort(&self, index: &S, element: &S) -> S;
    define_converter_binary_function!(mk_select);
    define_converter_ternary_function!(mk_store);
    fn convert_array_term(&self, term: &Term) -> Option<T> {
        match &term.term {
            UnsortedTerm::Constant(_const_term) => None,
            UnsortedTerm::Operation(operation) => match operation.as_ref() {
                GenOperation::Duo(kind, term1, term2) => {
                    let t1 = self.convert_term(term1);
                    let t2 = self.convert_term(term2);
                    match kind {
                        DuoOperationKind::Select => Some(self.mk_select(&t1, &t2)),
                        _ => None,
                    }
                }
                GenOperation::Trio(kind, term1, term2, term3) => {
                    let t1 = self.convert_term(term1);
                    let t2 = self.convert_term(term2);
                    let t3 = self.convert_term(term3);
                    match kind {
                        TrioOperationKind::Store => Some(self.mk_store(&t1, &t2, &t3)),
                        _ => None,
                    }
                }
                _ => None,
            },
        }
    }
    fn convert_array_sort(&self, sort: &Sort) -> Option<S> {
        match sort {
            Sort::ArraySort(index, element) => {
                Some(self.mk_array_sort(&self.convert_sort(index), &self.convert_sort(element)))
            }
            _ => None,
        }
    }
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

pub struct SolverOptions {
    pub unsat_core_enabled: bool,
    pub max_time: i32,
    pub max_memory: i32,
}

impl SolverOptions {
    pub fn new() -> Self {
        Self {
            unsat_core_enabled: false,
            max_time: 0,
            max_memory: 0,
        }
    }
}

impl Default for SolverOptions {
    fn default() -> Self {
        Self::new()
    }
}
