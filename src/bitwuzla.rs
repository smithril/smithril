use crate::{
    generalized::{
        Context, Factory, FloatingPointAsBinary, GeneralArrayConverter, GeneralBoolConverter,
        GeneralBvConverter, GeneralConverter, GeneralFpConverter, GeneralOptions, GeneralSolver,
        GeneralSort, GeneralTerm, Interrupter, OptionKind, Options, Solver, SolverResult,
    },
    term::{self, Sort, Term},
};
use std::{
    collections::{HashMap, HashSet},
    ffi::{CStr, CString},
    hash::Hash,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc, RwLock,
    },
};
use term::RoundingMode;
use termination_callback::termination_callback;

use crate::utils;

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct BitwuzlaTerm {
    pub term: smithril_bitwuzla_sys::BitwuzlaTerm,
}

unsafe impl Send for BitwuzlaTerm {}
unsafe impl Sync for BitwuzlaTerm {}

pub struct BitwuzlaSort {
    pub sort: smithril_bitwuzla_sys::BitwuzlaSort,
}

unsafe impl Send for BitwuzlaSort {}
unsafe impl Sync for BitwuzlaSort {}

impl GeneralSort for BitwuzlaSort {}

impl GeneralTerm for BitwuzlaTerm {}

pub struct BitwuzlaTerminationState {
    termination_state: AtomicBool,
}

impl Default for BitwuzlaTerminationState {
    fn default() -> Self {
        Self {
            termination_state: AtomicBool::new(false),
        }
    }
}

impl BitwuzlaTerminationState {
    pub fn terminated(&self) -> bool {
        self.termination_state.load(Ordering::Relaxed)
    }

    pub fn terminate(&self) {
        self.termination_state.store(true, Ordering::Relaxed)
    }

    pub fn start(&self) {
        self.termination_state.store(false, Ordering::Relaxed)
    }
}

mod termination_callback {
    use super::BitwuzlaTerminationState;

    #[no_mangle]
    pub extern "C" fn termination_callback(state: *mut ::std::os::raw::c_void) -> i32 {
        unsafe {
            let state = state as *mut BitwuzlaTerminationState;
            if (*state).terminated() {
                1
            } else {
                0
            }
        }
    }
}

#[derive(PartialEq, Eq, Hash)]
pub struct BitwuzlaContext {
    pub term_manager: *mut smithril_bitwuzla_sys::BitwuzlaTermManager,
}

impl BitwuzlaContext {
    pub fn new() -> Self {
        let term_manager = unsafe { smithril_bitwuzla_sys::bitwuzla_term_manager_new() };
        Self { term_manager }
    }
}

impl Default for BitwuzlaContext {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for BitwuzlaContext {
    fn drop(&mut self) {
        unsafe {
            smithril_bitwuzla_sys::bitwuzla_term_manager_delete(self.term_manager);
        };
    }
}

pub struct BitwuzlaOptions {
    pub options: *mut smithril_bitwuzla_sys::BitwuzlaOptions,
}

impl Default for BitwuzlaOptions {
    fn default() -> Self {
        let options = unsafe { smithril_bitwuzla_sys::bitwuzla_options_new() };
        let cadical_cstr = CString::new("cadical").unwrap();
        unsafe {
            smithril_bitwuzla_sys::bitwuzla_set_option_mode(
                options,
                smithril_bitwuzla_sys::BITWUZLA_OPT_SAT_SOLVER,
                cadical_cstr.as_ptr(),
            );
            smithril_bitwuzla_sys::bitwuzla_set_option(
                options,
                smithril_bitwuzla_sys::BITWUZLA_OPT_PRODUCE_MODELS,
                1,
            );
        };
        Self { options }
    }
}

impl From<&Options> for BitwuzlaOptions {
    fn from(value: &Options) -> Self {
        let options = Self::default();
        for opt_kind in value.bool_options.iter() {
            match opt_kind {
                (OptionKind::ProduceUnsatCore, val) => options.set_produce_unsat_core(*val),
            }
        }
        options
    }
}

impl PartialEq for BitwuzlaOptions {
    fn eq(&self, other: &Self) -> bool {
        self.options.eq(&other.options)
    }
}

impl Eq for BitwuzlaOptions {}

impl Hash for BitwuzlaOptions {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.options.hash(state);
    }
}

macro_rules! create_converter_fp_binary_function_bitwuzla {
    ($func_name:ident, $bitwuzla_sys_kind_name:ident) => {
        fn $func_name(
            &self,
            r_mode: &RoundingMode,
            term1: &BitwuzlaTerm,
            term2: &BitwuzlaTerm,
        ) -> BitwuzlaTerm {
            BitwuzlaTerm {
                term: unsafe {
                    smithril_bitwuzla_sys::bitwuzla_mk_term3(
                        self.term_manager(),
                        smithril_bitwuzla_sys::$bitwuzla_sys_kind_name,
                        self.get_rouning_mode(r_mode).term,
                        term1.term,
                        term2.term,
                    )
                },
            }
        }
    };
}

macro_rules! create_converter_fp_unary_function_bitwuzla {
    ($func_name:ident, $bitwuzla_sys_kind_name:ident) => {
        fn $func_name(&self, r_mode: &RoundingMode, term: &BitwuzlaTerm) -> BitwuzlaTerm {
            BitwuzlaTerm {
                term: unsafe {
                    smithril_bitwuzla_sys::bitwuzla_mk_term2(
                        self.term_manager(),
                        smithril_bitwuzla_sys::$bitwuzla_sys_kind_name,
                        self.get_rouning_mode(r_mode).term,
                        term.term,
                    )
                },
            }
        }
    };
}

#[derive(Default)]
pub struct BitwuzlaFactory {
    contexts: HashSet<Arc<BitwuzlaConverter>>,
    solvers: HashSet<Arc<BitwuzlaSolver>>,
}

impl Factory<BitwuzlaConverter, BitwuzlaSolver, BitwuzlaInterrupter> for BitwuzlaFactory {
    fn new_context(&mut self) -> Arc<BitwuzlaConverter> {
        let context = Arc::new(BitwuzlaConverter::default());
        self.contexts.insert(context.clone());
        context
    }

    fn delete_context(&mut self, context: Arc<BitwuzlaConverter>) {
        self.contexts.remove(&context);
        assert_eq!(Arc::strong_count(&context), 1);
    }

    fn delete_solver(&mut self, solver: Arc<BitwuzlaSolver>) {
        self.solvers.remove(&solver);
        assert_eq!(Arc::strong_count(&solver), 1);
    }

    fn new_interrupter(&self, solver: Arc<BitwuzlaSolver>) -> BitwuzlaInterrupter {
        BitwuzlaInterrupter {
            holder: BitwuzlaSolverSys(solver.solver()),
        }
    }

    fn new_solver(
        &mut self,
        context: Arc<BitwuzlaConverter>,
        options: &Options,
    ) -> Arc<BitwuzlaSolver> {
        let solver = Arc::new(BitwuzlaSolver::new(context, options));
        self.solvers.insert(solver.clone());
        solver
    }
}

pub struct BitwuzlaSolver {
    pub context: Arc<BitwuzlaConverter>,
    pub options: BitwuzlaOptions,
    pub asserted_terms_map: RwLock<HashMap<BitwuzlaTerm, Term>>,
    pub last_check_sat: RwLock<Option<SolverResult>>,
    solver: RwLock<BitwuzlaSolverSys>,
}

impl Drop for BitwuzlaOptions {
    fn drop(&mut self) {
        unsafe {
            smithril_bitwuzla_sys::bitwuzla_options_delete(self.options);
        };
    }
}

impl GeneralOptions for BitwuzlaOptions {
    fn set_produce_unsat_core(&self, val: bool) {
        unsafe {
            smithril_bitwuzla_sys::bitwuzla_set_option(
                self.options,
                smithril_bitwuzla_sys::BITWUZLA_OPT_PRODUCE_UNSAT_CORES,
                val as u64,
            );
        }
    }

    fn get_produce_unsat_core(&self) -> bool {
        unsafe {
            let res = smithril_bitwuzla_sys::bitwuzla_get_option(
                self.options,
                smithril_bitwuzla_sys::BITWUZLA_OPT_PRODUCE_UNSAT_CORES,
            );
            res != 0
        }
    }
}

impl BitwuzlaSolver {
    pub fn new(context: Arc<BitwuzlaConverter>, options: &Options) -> Self {
        let options = BitwuzlaOptions::from(options);
        let solver =
            unsafe { smithril_bitwuzla_sys::bitwuzla_new(context.term_manager(), options.options) };
        let solver = RwLock::new(BitwuzlaSolverSys(solver));
        let termination_state = BitwuzlaTerminationState::default();
        unsafe {
            smithril_bitwuzla_sys::bitwuzla_set_termination_callback(
                solver.read().unwrap().0,
                Some(termination_callback),
                Box::into_raw(Box::new(termination_state)) as *mut ::std::os::raw::c_void,
            )
        }
        Self {
            options,
            asserted_terms_map: RwLock::new(HashMap::new()),
            solver,
            context,
            last_check_sat: RwLock::new(Default::default()),
        }
    }

    fn solver(&self) -> *mut smithril_bitwuzla_sys::Bitwuzla {
        self.solver.read().unwrap().0
    }
}

impl PartialEq for BitwuzlaSolver {
    fn eq(&self, other: &Self) -> bool {
        let res = self.context.eq(&other.context);
        let res = res && self.options.eq(&other.options);
        res && self
            .solver
            .read()
            .unwrap()
            .0
            .eq(&other.solver.read().unwrap().0)
    }
}

impl Eq for BitwuzlaSolver {}

impl Hash for BitwuzlaSolver {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.context.hash(state);
        self.options.hash(state);
        self.solver().hash(state);
    }
}

impl Drop for BitwuzlaSolver {
    fn drop(&mut self) {
        unsafe {
            smithril_bitwuzla_sys::bitwuzla_delete(self.solver());
        };
    }
}

struct BitwuzlaSolverSys(*mut smithril_bitwuzla_sys::Bitwuzla);

unsafe impl Send for BitwuzlaSolverSys {}
unsafe impl Sync for BitwuzlaSolverSys {}

pub struct BitwuzlaInterrupter {
    holder: BitwuzlaSolverSys,
}

impl Interrupter for BitwuzlaInterrupter {
    fn interrupt(&self) {
        unsafe {
            let termination_callback_state =
                smithril_bitwuzla_sys::bitwuzla_get_termination_callback_state(self.holder.0)
                    as *mut BitwuzlaTerminationState;
            (*termination_callback_state).terminate();
        }
    }
}

pub struct BitwuzlaConverter {
    pub context: BitwuzlaContext,
    pub symbol_cache: RwLock<HashMap<String, BitwuzlaTerm>>,
}

impl Context for BitwuzlaConverter {}

impl PartialEq for BitwuzlaConverter {
    fn eq(&self, other: &Self) -> bool {
        self.context.eq(&other.context)
    }
}

impl Eq for BitwuzlaConverter {}

impl Hash for BitwuzlaConverter {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.context.hash(state)
    }
}

unsafe impl Send for BitwuzlaContext {}
unsafe impl Sync for BitwuzlaContext {}

unsafe impl Send for BitwuzlaOptions {}
unsafe impl Sync for BitwuzlaOptions {}

impl BitwuzlaConverter {
    pub fn new(context: BitwuzlaContext) -> Self {
        Self {
            context,
            symbol_cache: RwLock::new(HashMap::new()),
        }
    }

    fn term_manager(&self) -> *mut smithril_bitwuzla_sys::BitwuzlaTermManager {
        self.context.term_manager
    }
}

impl Default for BitwuzlaConverter {
    fn default() -> Self {
        Self::new(BitwuzlaContext::new())
    }
}

impl BitwuzlaConverter {}

macro_rules! create_converter_ternary_function_bitwuzla {
    ($func_name:ident, $bitwuzla_sys_kind_name:ident) => {
        fn $func_name(
            &self,
            term1: &BitwuzlaTerm,
            term2: &BitwuzlaTerm,
            term3: &BitwuzlaTerm,
        ) -> BitwuzlaTerm {
            BitwuzlaTerm {
                term: unsafe {
                    smithril_bitwuzla_sys::bitwuzla_mk_term3(
                        self.term_manager(),
                        smithril_bitwuzla_sys::$bitwuzla_sys_kind_name,
                        term1.term,
                        term2.term,
                        term3.term,
                    )
                },
            }
        }
    };
}

macro_rules! create_converter_binary_function_bitwuzla {
    ($func_name:ident, $bitwuzla_sys_kind_name:ident) => {
        fn $func_name(&self, term1: &BitwuzlaTerm, term2: &BitwuzlaTerm) -> BitwuzlaTerm {
            BitwuzlaTerm {
                term: unsafe {
                    smithril_bitwuzla_sys::bitwuzla_mk_term2(
                        self.term_manager(),
                        smithril_bitwuzla_sys::$bitwuzla_sys_kind_name,
                        term1.term,
                        term2.term,
                    )
                },
            }
        }
    };
}

macro_rules! create_converter_unary_function_bitwuzla {
    ($func_name:ident, $bitwuzla_sys_kind_name:ident) => {
        fn $func_name(&self, term: &BitwuzlaTerm) -> BitwuzlaTerm {
            BitwuzlaTerm {
                term: unsafe {
                    smithril_bitwuzla_sys::bitwuzla_mk_term1(
                        self.term_manager(),
                        smithril_bitwuzla_sys::$bitwuzla_sys_kind_name,
                        term.term,
                    )
                },
            }
        }
    };
}

impl GeneralSolver<BitwuzlaSort, BitwuzlaTerm, BitwuzlaOptions, BitwuzlaConverter>
    for BitwuzlaSolver
{
    fn unsat_core(&self) -> Vec<BitwuzlaTerm> {
        let last_check_sat = { *self.last_check_sat.read().unwrap() };
        assert_eq!(last_check_sat.unwrap(), SolverResult::Unsat);
        let mut size: usize = 0;
        let u_core =
            unsafe { smithril_bitwuzla_sys::bitwuzla_get_unsat_core(self.solver(), &mut size) };
        let mut res: Vec<BitwuzlaTerm> = Vec::new();
        let slice = unsafe { std::slice::from_raw_parts(u_core, std::ptr::read(&size)) };
        for cur_term in slice {
            res.push(BitwuzlaTerm { term: *cur_term });
        }
        res
    }

    fn assert(&self, term: &BitwuzlaTerm) {
        unsafe { smithril_bitwuzla_sys::bitwuzla_assert(self.solver(), term.term) }
    }

    fn eval(&self, term1: &BitwuzlaTerm) -> Option<BitwuzlaTerm> {
        let last_check_sat = { *self.last_check_sat.read().unwrap() };
        assert_eq!(last_check_sat.unwrap(), SolverResult::Sat);
        let bitwuzla_term =
            unsafe { smithril_bitwuzla_sys::bitwuzla_get_value(self.solver(), term1.term) };
        let res = BitwuzlaTerm {
            term: bitwuzla_term,
        };
        Some(res)
    }

    fn reset(&self) {
        let context = self.context.as_ref();
        let termination_state = BitwuzlaTerminationState::default();
        unsafe {
            let termination_callback_state =
                smithril_bitwuzla_sys::bitwuzla_get_termination_callback_state(self.solver())
                    as *mut BitwuzlaTerminationState;
            drop(Box::from_raw(termination_callback_state));
            smithril_bitwuzla_sys::bitwuzla_delete(self.solver());
            {
                let mut solver = self.solver.write().unwrap();
                *solver = BitwuzlaSolverSys(smithril_bitwuzla_sys::bitwuzla_new(
                    context.term_manager(),
                    self.options.options,
                ));
            }
            smithril_bitwuzla_sys::bitwuzla_set_termination_callback(
                self.solver(),
                Some(termination_callback),
                Box::into_raw(Box::new(termination_state)) as *mut ::std::os::raw::c_void,
            )
        }
    }

    fn interrupt(&self) {
        unsafe {
            let termination_callback_state =
                smithril_bitwuzla_sys::bitwuzla_get_termination_callback_state(self.solver())
                    as *mut BitwuzlaTerminationState;
            (*termination_callback_state).terminate();
        }
    }

    fn check_sat(&self) -> SolverResult {
        {
            *self.last_check_sat.write().unwrap() = None;
        }
        unsafe {
            let termination_callback_state =
                smithril_bitwuzla_sys::bitwuzla_get_termination_callback_state(self.solver())
                    as *mut BitwuzlaTerminationState;
            (*termination_callback_state).start();
        }
        let res = unsafe { smithril_bitwuzla_sys::bitwuzla_check_sat(self.solver()) };
        let res = match res {
            smithril_bitwuzla_sys::BITWUZLA_SAT => SolverResult::Sat,
            smithril_bitwuzla_sys::BITWUZLA_UNSAT => SolverResult::Unsat,
            _ => SolverResult::Unknown,
        };
        {
            *self.last_check_sat.write().unwrap() = Some(res);
        }
        res
    }

    fn push(&self) {
        unsafe {
            smithril_bitwuzla_sys::bitwuzla_push(self.solver(), 1);
        }
    }

    fn pop(&self, size: u64) {
        unsafe {
            smithril_bitwuzla_sys::bitwuzla_pop(self.solver(), size);
        }
    }
}

impl GeneralArrayConverter<BitwuzlaSort, BitwuzlaTerm> for BitwuzlaConverter {
    fn mk_array_sort(&self, index: &BitwuzlaSort, element: &BitwuzlaSort) -> BitwuzlaSort {
        let i = index.sort;
        let e = element.sort;
        BitwuzlaSort {
            sort: unsafe {
                smithril_bitwuzla_sys::bitwuzla_mk_array_sort(self.term_manager(), i, e)
            },
        }
    }

    create_converter_binary_function_bitwuzla!(mk_select, BITWUZLA_KIND_ARRAY_SELECT);
    create_converter_ternary_function_bitwuzla!(mk_store, BITWUZLA_KIND_ARRAY_STORE);
}

impl GeneralBvConverter<BitwuzlaSort, BitwuzlaTerm> for BitwuzlaConverter {
    fn mk_bv_sort(&self, size: u64) -> BitwuzlaSort {
        BitwuzlaSort {
            sort: unsafe { smithril_bitwuzla_sys::bitwuzla_mk_bv_sort(self.term_manager(), size) },
        }
    }

    fn mk_bv_value_uint64(&self, sort: &BitwuzlaSort, val: u64) -> BitwuzlaTerm {
        BitwuzlaTerm {
            term: unsafe {
                smithril_bitwuzla_sys::bitwuzla_mk_bv_value_uint64(
                    self.term_manager(),
                    sort.sort,
                    val,
                )
            },
        }
    }

    create_converter_binary_function_bitwuzla!(mk_bv_add, BITWUZLA_KIND_BV_ADD);
    create_converter_binary_function_bitwuzla!(mk_bv_and, BITWUZLA_KIND_BV_AND);
    create_converter_binary_function_bitwuzla!(mk_bv_ashr, BITWUZLA_KIND_BV_ASHR);
    create_converter_binary_function_bitwuzla!(mk_bv_lshr, BITWUZLA_KIND_BV_SHR);
    create_converter_binary_function_bitwuzla!(mk_bv_nand, BITWUZLA_KIND_BV_NAND);
    create_converter_unary_function_bitwuzla!(mk_bv_neg, BITWUZLA_KIND_BV_NEG);
    create_converter_unary_function_bitwuzla!(mk_bv_not, BITWUZLA_KIND_BV_NOT);
    create_converter_binary_function_bitwuzla!(mk_bv_or, BITWUZLA_KIND_BV_OR);
    create_converter_binary_function_bitwuzla!(mk_bv_nor, BITWUZLA_KIND_BV_NOR);
    create_converter_binary_function_bitwuzla!(mk_bv_nxor, BITWUZLA_KIND_BV_XNOR);
    create_converter_binary_function_bitwuzla!(mk_bv_sdiv, BITWUZLA_KIND_BV_SDIV);
    create_converter_binary_function_bitwuzla!(mk_bv_sge, BITWUZLA_KIND_BV_SGE);
    create_converter_binary_function_bitwuzla!(mk_bv_sgt, BITWUZLA_KIND_BV_SGT);
    create_converter_binary_function_bitwuzla!(mk_bv_shl, BITWUZLA_KIND_BV_SHL);
    create_converter_binary_function_bitwuzla!(mk_bv_sle, BITWUZLA_KIND_BV_SLE);
    create_converter_binary_function_bitwuzla!(mk_bv_slt, BITWUZLA_KIND_BV_SLT);
    create_converter_binary_function_bitwuzla!(mk_bv_smod, BITWUZLA_KIND_BV_SMOD);
    create_converter_binary_function_bitwuzla!(mk_bv_srem, BITWUZLA_KIND_BV_SREM);
    create_converter_binary_function_bitwuzla!(mk_bv_sub, BITWUZLA_KIND_BV_SUB);
    create_converter_binary_function_bitwuzla!(mk_bv_udiv, BITWUZLA_KIND_BV_UDIV);
    create_converter_binary_function_bitwuzla!(mk_bv_uge, BITWUZLA_KIND_BV_UGE);
    create_converter_binary_function_bitwuzla!(mk_bv_ugt, BITWUZLA_KIND_BV_UGT);
    create_converter_binary_function_bitwuzla!(mk_bv_ule, BITWUZLA_KIND_BV_ULE);
    create_converter_binary_function_bitwuzla!(mk_bv_ult, BITWUZLA_KIND_BV_ULT);
    create_converter_binary_function_bitwuzla!(mk_bv_urem, BITWUZLA_KIND_BV_UREM);
    create_converter_binary_function_bitwuzla!(mk_bv_xor, BITWUZLA_KIND_BV_XOR);
    create_converter_binary_function_bitwuzla!(mk_bv_mul, BITWUZLA_KIND_BV_MUL);
    create_converter_binary_function_bitwuzla!(mk_concat, BITWUZLA_KIND_BV_CONCAT);

    fn mk_extract(&self, high: u64, low: u64, term: &BitwuzlaTerm) -> BitwuzlaTerm {
        unsafe {
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term1_indexed2(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_BV_EXTRACT,
                term.term,
                high,
                low,
            );
            BitwuzlaTerm { term }
        }
    }

    fn mk_sign_extend(&self, size: u64, term: &BitwuzlaTerm) -> BitwuzlaTerm {
        unsafe {
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term1_indexed1(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_BV_SIGN_EXTEND,
                term.term,
                size,
            );
            BitwuzlaTerm { term }
        }
    }

    fn mk_zero_extend(&self, size: u64, term: &BitwuzlaTerm) -> BitwuzlaTerm {
        unsafe {
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term1_indexed1(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_BV_ZERO_EXTEND,
                term.term,
                size,
            );
            BitwuzlaTerm { term }
        }
    }
}

impl GeneralBoolConverter<BitwuzlaSort, BitwuzlaTerm> for BitwuzlaConverter {
    fn mk_bool_sort(&self) -> BitwuzlaSort {
        BitwuzlaSort {
            sort: unsafe { smithril_bitwuzla_sys::bitwuzla_mk_bool_sort(self.term_manager()) },
        }
    }

    fn mk_smt_bool(&self, val: bool) -> BitwuzlaTerm {
        let term = unsafe {
            match val {
                true => smithril_bitwuzla_sys::bitwuzla_mk_true(self.term_manager()),
                false => smithril_bitwuzla_sys::bitwuzla_mk_false(self.term_manager()),
            }
        };
        BitwuzlaTerm { term }
    }

    create_converter_binary_function_bitwuzla!(mk_implies, BITWUZLA_KIND_IMPLIES);
    create_converter_binary_function_bitwuzla!(mk_neq, BITWUZLA_KIND_DISTINCT);
    create_converter_unary_function_bitwuzla!(mk_not, BITWUZLA_KIND_NOT);
    create_converter_binary_function_bitwuzla!(mk_or, BITWUZLA_KIND_OR);
    create_converter_binary_function_bitwuzla!(mk_xor, BITWUZLA_KIND_XOR);
    create_converter_binary_function_bitwuzla!(mk_and, BITWUZLA_KIND_AND);
    create_converter_binary_function_bitwuzla!(mk_iff, BITWUZLA_KIND_IFF);
    create_converter_ternary_function_bitwuzla!(mk_ite, BITWUZLA_KIND_ITE);
}

impl GeneralFpConverter<BitwuzlaSort, BitwuzlaTerm> for BitwuzlaConverter {
    create_converter_ternary_function_bitwuzla!(mk_fp, BITWUZLA_KIND_FP_FP);

    fn mk_fp_sort(&self, ew: u64, sw: u64) -> BitwuzlaSort {
        BitwuzlaSort {
            sort: unsafe {
                smithril_bitwuzla_sys::bitwuzla_mk_fp_sort(self.term_manager(), ew, sw)
            },
        }
    }

    fn fp_get_bv_exp_size(&self, term: &BitwuzlaTerm) -> u64 {
        unsafe { smithril_bitwuzla_sys::bitwuzla_term_fp_get_exp_size(term.term) }
    }

    fn fp_get_bv_sig_size(&self, term: &BitwuzlaTerm) -> u64 {
        unsafe { smithril_bitwuzla_sys::bitwuzla_term_fp_get_sig_size(term.term) }
    }

    fn fp_is_pos(&self, term1: &BitwuzlaTerm) -> BitwuzlaTerm {
        unsafe {
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term1(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_FP_IS_POS,
                term1.term,
            );
            BitwuzlaTerm { term }
        }
    }

    fn fp_is_nan(&self, term1: &BitwuzlaTerm) -> BitwuzlaTerm {
        unsafe {
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term1(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_FP_IS_NAN,
                term1.term,
            );
            BitwuzlaTerm { term }
        }
    }

    fn fp_is_inf(&self, term1: &BitwuzlaTerm) -> BitwuzlaTerm {
        unsafe {
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term1(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_FP_IS_INF,
                term1.term,
            );
            BitwuzlaTerm { term }
        }
    }

    fn fp_is_normal(&self, term1: &BitwuzlaTerm) -> BitwuzlaTerm {
        unsafe {
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term1(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_FP_IS_NORMAL,
                term1.term,
            );
            BitwuzlaTerm { term }
        }
    }

    fn fp_is_subnormal(&self, term1: &BitwuzlaTerm) -> BitwuzlaTerm {
        unsafe {
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term1(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_FP_IS_SUBNORMAL,
                term1.term,
            );
            BitwuzlaTerm { term }
        }
    }

    fn fp_is_zero(&self, term1: &BitwuzlaTerm) -> BitwuzlaTerm {
        unsafe {
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term1(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_FP_IS_ZERO,
                term1.term,
            );
            BitwuzlaTerm { term }
        }
    }

    fn mk_fp_eq(&self, term1: &BitwuzlaTerm, term2: &BitwuzlaTerm) -> BitwuzlaTerm {
        unsafe {
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term2(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_FP_EQUAL,
                term1.term,
                term2.term,
            );
            BitwuzlaTerm { term }
        }
    }

    create_converter_binary_function_bitwuzla!(mk_fp_rem, BITWUZLA_KIND_FP_REM);
    create_converter_binary_function_bitwuzla!(mk_fp_min, BITWUZLA_KIND_FP_MIN);
    create_converter_binary_function_bitwuzla!(mk_fp_max, BITWUZLA_KIND_FP_MAX);
    create_converter_binary_function_bitwuzla!(mk_fp_lt, BITWUZLA_KIND_FP_LT);
    create_converter_binary_function_bitwuzla!(mk_fp_leq, BITWUZLA_KIND_FP_LEQ);
    create_converter_binary_function_bitwuzla!(mk_fp_gt, BITWUZLA_KIND_FP_GT);
    create_converter_binary_function_bitwuzla!(mk_fp_geq, BITWUZLA_KIND_FP_GEQ);
    create_converter_fp_binary_function_bitwuzla!(mk_fp_add, BITWUZLA_KIND_FP_ADD);
    create_converter_fp_binary_function_bitwuzla!(mk_fp_sub, BITWUZLA_KIND_FP_SUB);
    create_converter_fp_binary_function_bitwuzla!(mk_fp_mul, BITWUZLA_KIND_FP_MUL);
    create_converter_fp_binary_function_bitwuzla!(mk_fp_div, BITWUZLA_KIND_FP_DIV);
    create_converter_fp_unary_function_bitwuzla!(mk_fp_sqrt, BITWUZLA_KIND_FP_SQRT);
    create_converter_fp_unary_function_bitwuzla!(mk_fp_rti, BITWUZLA_KIND_FP_RTI);
    create_converter_unary_function_bitwuzla!(mk_fp_abs, BITWUZLA_KIND_FP_ABS);
    create_converter_unary_function_bitwuzla!(mk_fp_neg, BITWUZLA_KIND_FP_NEG);

    fn get_rouning_mode(&self, r_mode: &RoundingMode) -> BitwuzlaTerm {
        unsafe {
            let rm = match r_mode {
                RoundingMode::RNA => smithril_bitwuzla_sys::BITWUZLA_RM_RNA,
                RoundingMode::RNE => smithril_bitwuzla_sys::BITWUZLA_RM_RNE,
                RoundingMode::RTN => smithril_bitwuzla_sys::BITWUZLA_RM_RTN,
                RoundingMode::RTP => smithril_bitwuzla_sys::BITWUZLA_RM_RTP,
                RoundingMode::RTZ => smithril_bitwuzla_sys::BITWUZLA_RM_RTZ,
            };
            let r_mode_term = smithril_bitwuzla_sys::bitwuzla_mk_rm_value(self.term_manager(), rm);
            BitwuzlaTerm { term: r_mode_term }
        }
    }

    fn mk_fp_to_fp_from_fp(
        &self,
        r_mode: &RoundingMode,
        term: &BitwuzlaTerm,
        ew: u64,
        sw: u64,
    ) -> BitwuzlaTerm {
        unsafe {
            let r_mode = self.get_rouning_mode(r_mode);
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term2_indexed2(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_FP_TO_FP_FROM_FP,
                r_mode.term,
                term.term,
                ew,
                sw,
            );
            BitwuzlaTerm { term }
        }
    }

    fn mk_fp_to_sbv(&self, r_mode: &RoundingMode, term: &BitwuzlaTerm, w: u64) -> BitwuzlaTerm {
        unsafe {
            let r_mode = self.get_rouning_mode(r_mode);
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term2_indexed1(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_FP_TO_SBV,
                r_mode.term,
                term.term,
                w,
            );
            BitwuzlaTerm { term }
        }
    }

    fn mk_fp_to_ubv(&self, r_mode: &RoundingMode, term: &BitwuzlaTerm, w: u64) -> BitwuzlaTerm {
        unsafe {
            let r_mode = self.get_rouning_mode(r_mode);
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term2_indexed1(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_FP_TO_UBV,
                r_mode.term,
                term.term,
                w,
            );
            BitwuzlaTerm { term }
        }
    }

    fn mk_fp_to_fp_from_sbv(
        &self,
        r_mode: &RoundingMode,
        term: &BitwuzlaTerm,
        ew: u64,
        sw: u64,
    ) -> BitwuzlaTerm {
        unsafe {
            let r_mode = self.get_rouning_mode(r_mode);
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term2_indexed2(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_FP_TO_FP_FROM_SBV,
                r_mode.term,
                term.term,
                ew,
                sw,
            );
            BitwuzlaTerm { term }
        }
    }

    fn mk_fp_to_fp_from_ubv(
        &self,
        r_mode: &RoundingMode,
        term: &BitwuzlaTerm,
        ew: u64,
        sw: u64,
    ) -> BitwuzlaTerm {
        unsafe {
            let r_mode = self.get_rouning_mode(r_mode);
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term2_indexed2(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_FP_TO_FP_FROM_UBV,
                r_mode.term,
                term.term,
                ew,
                sw,
            );
            BitwuzlaTerm { term }
        }
    }

    fn mk_fp_to_fp_from_bv(&self, term: &BitwuzlaTerm, ew: u64, sw: u64) -> BitwuzlaTerm {
        unsafe {
            let term = smithril_bitwuzla_sys::bitwuzla_mk_term1_indexed2(
                self.term_manager(),
                smithril_bitwuzla_sys::BITWUZLA_KIND_FP_TO_FP_FROM_BV,
                term.term,
                ew,
                sw,
            );
            BitwuzlaTerm { term }
        }
    }

    fn mk_fp_pos_zero(&self, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        unsafe {
            let term =
                smithril_bitwuzla_sys::bitwuzla_mk_fp_pos_zero(self.term_manager(), sort.sort);
            BitwuzlaTerm { term }
        }
    }

    fn mk_fp_pos_inf(&self, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        unsafe {
            let term =
                smithril_bitwuzla_sys::bitwuzla_mk_fp_pos_inf(self.term_manager(), sort.sort);
            BitwuzlaTerm { term }
        }
    }

    fn mk_fp_neg_zero(&self, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        unsafe {
            let term =
                smithril_bitwuzla_sys::bitwuzla_mk_fp_neg_zero(self.term_manager(), sort.sort);
            BitwuzlaTerm { term }
        }
    }

    fn mk_fp_neg_inf(&self, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        unsafe {
            let term =
                smithril_bitwuzla_sys::bitwuzla_mk_fp_neg_inf(self.term_manager(), sort.sort);
            BitwuzlaTerm { term }
        }
    }
}

impl GeneralConverter<BitwuzlaSort, BitwuzlaTerm> for BitwuzlaConverter {
    fn mk_smt_symbol(&self, name: &str, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        let mut sym_table = self.symbol_cache.write().unwrap();
        let term = if let Some(term2) = sym_table.get(name) {
            term2.clone()
        } else {
            let name_cstr = CString::new(name).unwrap();
            let term = unsafe {
                smithril_bitwuzla_sys::bitwuzla_mk_const(
                    self.term_manager(),
                    sort.sort,
                    name_cstr.as_ptr(),
                )
            };
            let term = BitwuzlaTerm { term };
            let old_term = sym_table.insert(name.to_string(), term.clone());
            assert!(old_term.is_none());
            term
        };
        term
    }

    fn mk_smt_const_symbol(&self, term: &BitwuzlaTerm, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        let term = unsafe {
            smithril_bitwuzla_sys::bitwuzla_mk_const_array(
                self.term_manager(),
                sort.sort,
                term.term,
            )
        };
        BitwuzlaTerm { term }
    }

    fn try_get_bool_converter(
        &self,
    ) -> Option<&dyn GeneralBoolConverter<BitwuzlaSort, BitwuzlaTerm>> {
        Some(self)
    }
    fn try_get_bv_converter(&self) -> Option<&dyn GeneralBvConverter<BitwuzlaSort, BitwuzlaTerm>> {
        Some(self)
    }
    fn try_get_array_converter(
        &self,
    ) -> Option<&dyn GeneralArrayConverter<BitwuzlaSort, BitwuzlaTerm>> {
        Some(self)
    }
    fn try_get_fp_converter(&self) -> Option<&dyn GeneralFpConverter<BitwuzlaSort, BitwuzlaTerm>> {
        Some(self)
    }
    create_converter_binary_function_bitwuzla!(mk_eq, BITWUZLA_KIND_EQUAL);
}

impl Solver for BitwuzlaSolver {
    fn unsat_core(&self) -> Vec<Term> {
        let u_core_bitwuzla = GeneralSolver::unsat_core(self);
        let mut u_core: Vec<Term> = Vec::new();
        for cur_term in u_core_bitwuzla {
            let cur_asserted_terms_map = self.asserted_terms_map.read().unwrap();
            match cur_asserted_terms_map.get(&cur_term) {
                Some(t) => u_core.push(t.clone()),
                None => panic!("Term not found in asserted_terms_map"),
            }
        }
        u_core
    }

    fn assert(&self, term: &term::Term) {
        let context = self.context.as_ref();
        let cur_bitwuzla_term = context.convert_term(term);
        GeneralSolver::assert(self, &cur_bitwuzla_term);
        let mut cur_asserted_terms_map = self.asserted_terms_map.write().unwrap();
        cur_asserted_terms_map.insert(cur_bitwuzla_term, term.clone());
    }

    fn check_sat(&self) -> SolverResult {
        GeneralSolver::check_sat(self)
    }

    fn eval(&self, term: &Term) -> Option<Term> {
        let context = self.context.as_ref();
        let expr = GeneralSolver::eval(self, &context.convert_term(term))?;
        match term.sort {
            Sort::BvSort(_) => {
                let bitwuzla_string: *const i8 =
                    unsafe { smithril_bitwuzla_sys::bitwuzla_term_to_string(expr.term) };
                let s = unsafe {
                    CStr::from_ptr(bitwuzla_string)
                        .to_string_lossy()
                        .into_owned()
                };
                let bv_const = utils::binary2integer(s);
                let res = term::mk_bv_value_uint64(bv_const, &term.sort);
                Some(res)
            }
            Sort::BoolSort() => {
                let bitwuzla_string =
                    unsafe { smithril_bitwuzla_sys::bitwuzla_term_to_string(expr.term) };
                let s_cstr: &CStr = unsafe { CStr::from_ptr(bitwuzla_string) };
                let s = s_cstr.to_string_lossy().into_owned();
                match s.as_str() {
                    "true" => {
                        let res = term::mk_smt_bool(true);
                        Some(res)
                    }
                    "false" => {
                        let res = term::mk_smt_bool(false);
                        Some(res)
                    }
                    _ => {
                        panic!("Can't get boolean value from bitwuzla")
                    }
                }
            }

            Sort::ArraySort(_, _) => panic!("Unexpected sort"),
            Sort::FpSort(_, _) => panic!("Unexpected sort"),
        }
    }

    fn reset(&self) {
        GeneralSolver::reset(self)
    }

    fn push(&self) {
        GeneralSolver::push(self)
    }

    fn pop(&self, size: u64) {
        GeneralSolver::pop(self, size)
    }
}
