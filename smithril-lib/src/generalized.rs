use core::fmt;
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, sync::Arc, time::Duration};

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

pub trait GeneralFactory<S, T, O, C, SL, I>
where
    S: GeneralSort,
    T: GeneralTerm,
    O: GeneralOptions,
    C: GeneralConverter<S, T>,
    SL: GeneralSolver<S, T, O, C>,
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
}

pub trait AsyncSolver {
    fn assert(&self, term: &Term) -> impl std::future::Future<Output = ()> + Send;
    fn reset(&self) -> impl std::future::Future<Output = ()> + Send;
    fn interrupt(&self) -> impl std::future::Future<Output = ()> + Send;
    fn check_sat(&self) -> impl std::future::Future<Output = SolverResult> + Send;
    fn unsat_core(&self) -> impl std::future::Future<Output = Vec<Term>> + Send;
}

macro_rules! define_converter_binary_function {
    ($func_name:ident) => {
        fn $func_name(&self, term1: &T, term2: &T) -> T;
    };
}

pub trait GeneralConverter<S, T>
where
    S: GeneralSort,
    T: GeneralTerm,
{
    fn mk_bv_sort(&self, size: u64) -> S;
    fn mk_bool_sort(&self) -> S;
    fn mk_bv_value_uint64(&self, sort: &S, val: u64) -> T;
    define_converter_binary_function!(mk_and);
    define_converter_binary_function!(mk_bvadd);
    define_converter_binary_function!(mk_bvand);
    define_converter_binary_function!(mk_bvashr);
    define_converter_binary_function!(mk_bvlshr);
    define_converter_binary_function!(mk_bvmul);
    define_converter_binary_function!(mk_bvnand);
    fn mk_bvneg(&self, term: &T) -> T;
    define_converter_binary_function!(mk_bvnor);
    fn mk_bvnot(&self, term: &T) -> T;
    define_converter_binary_function!(mk_bvnxor);
    define_converter_binary_function!(mk_bvor);
    define_converter_binary_function!(mk_bvsdiv);
    define_converter_binary_function!(mk_bvsge);
    define_converter_binary_function!(mk_bvsgt);
    define_converter_binary_function!(mk_bvshl);
    define_converter_binary_function!(mk_bvsle);
    define_converter_binary_function!(mk_bvslt);
    define_converter_binary_function!(mk_bvsmod);
    define_converter_binary_function!(mk_bvsub);
    define_converter_binary_function!(mk_bvudiv);
    define_converter_binary_function!(mk_bvuge);
    define_converter_binary_function!(mk_bvugt);
    define_converter_binary_function!(mk_bvule);
    define_converter_binary_function!(mk_bvult);
    define_converter_binary_function!(mk_bvumod);
    define_converter_binary_function!(mk_bvxor);
    define_converter_binary_function!(mk_eq);
    define_converter_binary_function!(mk_implies);
    define_converter_binary_function!(mk_neq);
    fn mk_not(&self, term: &T) -> T;
    define_converter_binary_function!(mk_or);
    fn mk_smt_bool(&self, val: bool) -> T;
    fn mk_smt_symbol(&self, name: &str, sort: &S) -> T;
    define_converter_binary_function!(mk_xor);
    fn mk_array_sort(&self, index: &S, element: &S) -> S;
    define_converter_binary_function!(mk_select);
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
