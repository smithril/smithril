use crate::generalized::GeneralOptions;
use crate::generalized::GeneralUnsatCoreSolver;
use crate::generalized::Interrupter;
use crate::generalized::Options;
use crate::generalized::UnsatCoreSolver;
use std::hash::Hash;
use std::sync::Arc;
use std::sync::RwLock;
use std::thread::sleep;
use std::time::Duration;

use crate::generalized::GeneralConverter;
use crate::generalized::GeneralFactory;
use crate::generalized::GeneralSolver;
use crate::generalized::GeneralSort;
use crate::generalized::GeneralTerm;
use crate::generalized::Solver;
use crate::generalized::SolverResult;
use crate::generalized::Term;
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(PartialEq, Eq, Hash)]
pub struct DummyTerm {}

pub struct DummySort {}

impl GeneralSort for DummySort {}

impl GeneralTerm for DummyTerm {}

#[derive(PartialEq, Eq, Hash)]
pub struct DummyContext {}

impl DummyContext {
    pub fn new() -> Self {
        Self {}
    }
}

impl Default for DummyContext {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(PartialEq, Eq, Hash, Default)]
pub struct DummyOptions {}

impl From<&Options> for DummyOptions {
    fn from(_value: &Options) -> Self {
        Self::default()
    }
}

#[derive(Default)]
pub struct DummyFactory {
    contexts: HashSet<Arc<DummyConverter>>,
    solvers: HashSet<Arc<DummySolver>>,
}

impl
    GeneralFactory<
        DummySort,
        DummyTerm,
        DummyOptions,
        DummyConverter,
        DummySolver,
        DummyInterrupter,
    > for DummyFactory
{
    fn new_context(&mut self) -> Arc<DummyConverter> {
        let context = Arc::new(DummyConverter::default());
        self.contexts.insert(context.clone());
        context
    }

    fn delete_context(&mut self, context: Arc<DummyConverter>) {
        self.contexts.remove(&context);
        assert_eq!(Arc::strong_count(&context), 1);
    }

    fn delete_solver(&mut self, solver: Arc<DummySolver>) {
        self.solvers.remove(&solver);
        assert_eq!(Arc::strong_count(&solver), 1);
    }

    fn new_interrupter(&self, _solver: Arc<DummySolver>) -> DummyInterrupter {
        DummyInterrupter {}
    }

    fn new_solver(&mut self, context: Arc<DummyConverter>, options: &Options) -> Arc<DummySolver> {
        let solver = Arc::new(DummySolver::new(context, options));
        self.solvers.insert(solver.clone());
        solver
    }
}

pub struct DummySolver {
    pub context: Arc<DummyConverter>,
    pub options: DummyOptions,
    pub asserted_terms_map: RwLock<HashMap<DummyTerm, Term>>,
}

impl GeneralOptions for DummyOptions {
    fn set_produce_unsat_core(&self, _val: bool) {}

    fn get_produce_unsat_core(&self) -> bool {
        false
    }
}

impl DummySolver {
    pub fn new(context: Arc<DummyConverter>, options: &Options) -> Self {
        let options = DummyOptions::from(options);
        Self {
            options,
            asserted_terms_map: RwLock::new(HashMap::new()),
            context,
        }
    }
}

impl PartialEq for DummySolver {
    fn eq(&self, other: &Self) -> bool {
        let res = self.context.eq(&other.context);
        res && self.options.eq(&other.options)
    }
}

impl Eq for DummySolver {}

impl Hash for DummySolver {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.context.hash(state);
        self.options.hash(state);
    }
}

pub struct DummyInterrupter {}

impl Interrupter for DummyInterrupter {
    fn interrupt(&self) {}
}

pub struct DummyConverter {
    pub context: DummyContext,
}

impl PartialEq for DummyConverter {
    fn eq(&self, other: &Self) -> bool {
        self.context.eq(&other.context)
    }
}

impl Eq for DummyConverter {}

impl Hash for DummyConverter {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.context.hash(state)
    }
}

unsafe impl Send for DummyContext {}
unsafe impl Sync for DummyContext {}

unsafe impl Send for DummyOptions {}
unsafe impl Sync for DummyOptions {}

impl DummyConverter {
    pub fn new(context: DummyContext) -> Self {
        Self { context }
    }
}

impl Default for DummyConverter {
    fn default() -> Self {
        Self::new(DummyContext::new())
    }
}

impl DummyConverter {}

macro_rules! create_converter_ternary_function_dummy {
    ($func_name:ident, $dummy_sys_kind_name:ident) => {
        fn $func_name(
            &self,
            _term1: &DummyTerm,
            _term2: &DummyTerm,
            _term3: &DummyTerm,
        ) -> DummyTerm {
            DummyTerm {}
        }
    };
}

macro_rules! create_converter_binary_function_dummy {
    ($func_name:ident, $dummy_sys_kind_name:ident) => {
        fn $func_name(&self, _term1: &DummyTerm, _term2: &DummyTerm) -> DummyTerm {
            DummyTerm {}
        }
    };
}

macro_rules! create_converter_unary_function_dummy {
    ($func_name:ident, $dummy_sys_kind_name:ident) => {
        fn $func_name(&self, _term: &DummyTerm) -> DummyTerm {
            DummyTerm {}
        }
    };
}

impl GeneralUnsatCoreSolver<DummySort, DummyTerm, DummyConverter> for DummySolver {
    fn unsat_core(&self) -> Vec<DummyTerm> {
        Vec::new()
    }
}

impl GeneralSolver<DummySort, DummyTerm, DummyOptions, DummyConverter> for DummySolver {
    fn assert(&self, _term: &DummyTerm) {}

    fn eval(&self, _term1: &DummyTerm) -> Option<DummyTerm> {
        let res = DummyTerm {};
        Some(res)
    }

    fn reset(&self) {}

    fn interrupt(&self) {}

    fn check_sat(&self) -> SolverResult {
        sleep(Duration::from_secs(100));
        SolverResult::Unknown
    }
}

impl GeneralConverter<DummySort, DummyTerm> for DummyConverter {
    fn mk_smt_symbol(&self, _name: &str, _sort: &DummySort) -> DummyTerm {
        DummyTerm {}
    }

    create_converter_binary_function_dummy!(mk_eq, dummy_KIND_EQUAL);

    fn mk_bv_sort(&self, _size: u64) -> DummySort {
        DummySort {}
    }

    fn mk_bool_sort(&self) -> DummySort {
        DummySort {}
    }

    fn mk_array_sort(&self, _index: &DummySort, _elementt: &DummySort) -> DummySort {
        DummySort {}
    }

    fn mk_bv_value_uint64(&self, _sort: &DummySort, _val: u64) -> DummyTerm {
        DummyTerm {}
    }

    fn mk_smt_bool(&self, _val: bool) -> DummyTerm {
        DummyTerm {}
    }

    create_converter_binary_function_dummy!(mk_and, dummy_KIND_AND);
    create_converter_binary_function_dummy!(mk_bvadd, dummy_KIND_BV_ADD);
    create_converter_binary_function_dummy!(mk_bvand, dummy_KIND_BV_AND);
    create_converter_binary_function_dummy!(mk_bvashr, dummy_KIND_BV_ASHR);
    create_converter_binary_function_dummy!(mk_bvlshr, dummy_KIND_BV_SHR);
    create_converter_binary_function_dummy!(mk_bvnand, dummy_KIND_BV_NAND);
    create_converter_unary_function_dummy!(mk_bvneg, dummy_KIND_BV_NEG);
    create_converter_unary_function_dummy!(mk_bvnot, dummy_KIND_BV_NOT);
    create_converter_binary_function_dummy!(mk_bvor, dummy_KIND_BV_OR);
    create_converter_binary_function_dummy!(mk_bvnor, dummy_KIND_BV_NOR);
    create_converter_binary_function_dummy!(mk_bvnxor, dummy_KIND_BV_XNOR);
    create_converter_binary_function_dummy!(mk_bvsdiv, dummy_KIND_BV_SDIV);
    create_converter_binary_function_dummy!(mk_bvsge, dummy_KIND_BV_SGE);
    create_converter_binary_function_dummy!(mk_bvsgt, dummy_KIND_BV_SGT);
    create_converter_binary_function_dummy!(mk_bvshl, dummy_KIND_BV_SHL);
    create_converter_binary_function_dummy!(mk_bvsle, dummy_KIND_BV_SLE);
    create_converter_binary_function_dummy!(mk_bvslt, dummy_KIND_BV_SLT);
    create_converter_binary_function_dummy!(mk_bvsmod, dummy_KIND_BV_SMOD);
    create_converter_binary_function_dummy!(mk_bvsub, dummy_KIND_BV_SUB);
    create_converter_binary_function_dummy!(mk_bvudiv, dummy_KIND_BV_UDIV);
    create_converter_binary_function_dummy!(mk_bvuge, dummy_KIND_BV_UGE);
    create_converter_binary_function_dummy!(mk_bvugt, dummy_KIND_BV_UGT);
    create_converter_binary_function_dummy!(mk_bvule, dummy_KIND_BV_ULE);
    create_converter_binary_function_dummy!(mk_bvult, dummy_KIND_BV_ULT);
    create_converter_binary_function_dummy!(mk_bvumod, dummy_KIND_BV_UREM);
    create_converter_binary_function_dummy!(mk_bvxor, dummy_KIND_BV_XOR);
    create_converter_binary_function_dummy!(mk_implies, dummy_KIND_IMPLIES);
    create_converter_binary_function_dummy!(mk_neq, dummy_KIND_DISTINCT);
    create_converter_unary_function_dummy!(mk_not, dummy_KIND_NOT);
    create_converter_binary_function_dummy!(mk_or, dummy_KIND_OR);
    create_converter_binary_function_dummy!(mk_xor, dummy_KIND_XOR);
    create_converter_binary_function_dummy!(mk_bvmul, dummy_KIND_BV_MUL);
    create_converter_binary_function_dummy!(mk_select, dummy_KIND_ARRAY_SELECT);
    create_converter_ternary_function_dummy!(mk_store, dummy_KIND_ARRAY_STORE);
}

impl UnsatCoreSolver for DummySolver {
    fn unsat_core(&self) -> Vec<Term> {
        let u_core_dummy = GeneralUnsatCoreSolver::unsat_core(self);
        let mut u_core: Vec<Term> = Vec::new();
        for cur_term in u_core_dummy {
            let cur_asserted_terms_map = self.asserted_terms_map.read().unwrap();
            match cur_asserted_terms_map.get(&cur_term) {
                Some(t) => u_core.push(t.clone()),
                None => panic!("Term not found in asserted_terms_map"),
            }
        }
        u_core
    }
}

impl Solver for DummySolver {
    fn assert(&self, term: &crate::generalized::Term) {
        let context = self.context.as_ref();
        let cur_dummy_term = context.convert_term(term);
        GeneralSolver::assert(self, &cur_dummy_term);
        let mut cur_asserted_terms_map = self.asserted_terms_map.write().unwrap();
        cur_asserted_terms_map.insert(cur_dummy_term, term.clone());
    }

    fn check_sat(&self) -> SolverResult {
        GeneralSolver::check_sat(self)
    }

    fn eval(&self, _term: &Term) -> Option<Term> {
        None
    }

    fn reset(&self) {
        GeneralSolver::reset(self)
    }
}
