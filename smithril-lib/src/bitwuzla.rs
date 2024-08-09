use crate::generalized::GenConstant;
use crate::generalized::GeneralOptions;
use crate::generalized::GeneralUnsatCoreSolver;
use crate::generalized::Interrupter;
use crate::generalized::Options;
use crate::generalized::UnsatCoreSolver;
use std::hash::Hash;
use termination_callback::termination_callback;

use crate::generalized::GeneralConverter;
use crate::generalized::GeneralFactory;
use crate::generalized::GeneralSolver;
use crate::generalized::GeneralSort;
use crate::generalized::GeneralTerm;
use crate::generalized::Solver;
use crate::generalized::SolverResult;
use crate::generalized::Sort;
use crate::generalized::Term;
use crate::generalized::UnsortedTerm;
use crate::utils;
use std::cell::Cell;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::ffi::CStr;
use std::ffi::CString;
use std::rc::Rc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

#[derive(PartialEq, Eq, Hash)]
pub struct BitwuzlaTerm {
    pub term: smithril_bitwuzla_sys::BitwuzlaTerm,
}

pub struct BitwuzlaSort {
    pub sort: smithril_bitwuzla_sys::BitwuzlaSort,
}

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

impl BitwuzlaOptions {
    pub fn new(opt: &Options) -> Self {
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
        let res = Self { options };
        if opt.get_produce_unsat_core() {
            res.set_produce_unsat_core(true)
        }
        res
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

#[derive(Default)]
pub struct BitwuzlaFactory {
    contexts: HashSet<Rc<BitwuzlaConverter>>,
    solvers: HashSet<Rc<BitwuzlaSolver>>,
}

impl
    GeneralFactory<
        BitwuzlaSort,
        BitwuzlaTerm,
        BitwuzlaOptions,
        BitwuzlaConverter,
        BitwuzlaSolver,
        BitwuzlaInterrupter,
    > for BitwuzlaFactory
{
    fn new_context(&mut self) -> Rc<BitwuzlaConverter> {
        let context = Rc::new(BitwuzlaConverter::default());
        self.contexts.insert(context.clone());
        context
    }

    fn delete_context(&mut self, context: Rc<BitwuzlaConverter>) {
        self.contexts.remove(&context);
        assert_eq!(Rc::strong_count(&context), 1);
    }

    fn new_solver(&mut self, context: Rc<BitwuzlaConverter>) -> Rc<BitwuzlaSolver> {
        let solver = Rc::new(BitwuzlaSolver::new(context.clone(), &Options::default()));
        self.solvers.insert(solver.clone());
        solver
    }

    fn delete_solver(&mut self, solver: Rc<BitwuzlaSolver>) {
        self.solvers.remove(&solver);
        assert_eq!(Rc::strong_count(&solver), 1);
    }

    fn new_interrupter(&self, solver: Rc<BitwuzlaSolver>) -> BitwuzlaInterrupter {
        BitwuzlaInterrupter {
            holder: BitwuzlaHolder(solver.solver()),
        }
    }

    fn new_solver_with_options(
        &mut self,
        context: Rc<BitwuzlaConverter>,
        options: &Options,
    ) -> Rc<BitwuzlaSolver> {
        let solver = Rc::new(BitwuzlaSolver::new(context, options));
        self.solvers.insert(solver.clone());
        solver
    }
}

pub struct BitwuzlaSolver {
    pub context: Rc<BitwuzlaConverter>,
    pub options: BitwuzlaOptions,
    pub asserted_terms_map: Cell<HashMap<BitwuzlaTerm, Term>>,
    pub solver: RefCell<*mut smithril_bitwuzla_sys::Bitwuzla>,
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
    pub fn new(context: Rc<BitwuzlaConverter>, options: &Options) -> Self {
        let options = BitwuzlaOptions::new(options);
        let solver =
            unsafe { smithril_bitwuzla_sys::bitwuzla_new(context.term_manager(), options.options) };
        let solver = RefCell::new(solver);
        let termination_state = BitwuzlaTerminationState::default();
        unsafe {
            smithril_bitwuzla_sys::bitwuzla_set_termination_callback(
                *solver.borrow(),
                Some(termination_callback),
                Box::into_raw(Box::new(termination_state)) as *mut ::std::os::raw::c_void,
            )
        }
        Self {
            options,
            asserted_terms_map: Cell::new(HashMap::new()),
            solver,
            context,
        }
    }

    fn solver(&self) -> *mut smithril_bitwuzla_sys::Bitwuzla {
        *self.solver.borrow()
    }
}

impl PartialEq for BitwuzlaSolver {
    fn eq(&self, other: &Self) -> bool {
        let res = self.context.eq(&other.context);
        let res = res && self.options.eq(&other.options);
        res && self.solver.eq(&other.solver)
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

struct BitwuzlaHolder(*mut smithril_bitwuzla_sys::Bitwuzla);

unsafe impl Send for BitwuzlaHolder {}
unsafe impl Sync for BitwuzlaHolder {}

pub struct BitwuzlaInterrupter {
    holder: BitwuzlaHolder,
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
    pub symbol_cache: Cell<HashMap<String, BitwuzlaTerm>>,
}

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

unsafe impl Send for BitwuzlaConverter {}
unsafe impl Sync for BitwuzlaConverter {}

unsafe impl Send for BitwuzlaSolver {}
unsafe impl Sync for BitwuzlaSolver {}

impl BitwuzlaConverter {
    pub fn new(context: BitwuzlaContext) -> Self {
        Self {
            context,
            symbol_cache: Cell::new(HashMap::new()),
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

impl GeneralUnsatCoreSolver<BitwuzlaSort, BitwuzlaTerm, BitwuzlaConverter> for BitwuzlaSolver {
    fn unsat_core(&self) -> Vec<BitwuzlaTerm> {
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
}

impl GeneralSolver<BitwuzlaSort, BitwuzlaTerm, BitwuzlaOptions, BitwuzlaConverter>
    for BitwuzlaSolver
{
    fn assert(&self, term: &BitwuzlaTerm) {
        unsafe { smithril_bitwuzla_sys::bitwuzla_assert(self.solver(), term.term) }
    }

    fn eval(&self, term1: &BitwuzlaTerm) -> Option<BitwuzlaTerm> {
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
            self.solver.replace(smithril_bitwuzla_sys::bitwuzla_new(
                context.term_manager(),
                self.options.options,
            ));
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
        unsafe {
            let termination_callback_state =
                smithril_bitwuzla_sys::bitwuzla_get_termination_callback_state(self.solver())
                    as *mut BitwuzlaTerminationState;
            (*termination_callback_state).start();
        }
        let res = unsafe { smithril_bitwuzla_sys::bitwuzla_check_sat(self.solver()) };
        match res {
            smithril_bitwuzla_sys::BITWUZLA_SAT => SolverResult::Sat,
            smithril_bitwuzla_sys::BITWUZLA_UNSAT => SolverResult::Unsat,
            _ => SolverResult::Unknown,
        }
    }
}

impl GeneralConverter<BitwuzlaSort, BitwuzlaTerm> for BitwuzlaConverter {
    fn mk_smt_symbol(&self, name: &str, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        let mut sym_table = self.symbol_cache.take();
        let term = if let Some(term2) = sym_table.get(name) {
            term2.term
        } else {
            let name_cstr = CString::new(name).unwrap();
            let term = unsafe {
                smithril_bitwuzla_sys::bitwuzla_mk_const(
                    self.term_manager(),
                    sort.sort,
                    name_cstr.as_ptr(),
                )
            };
            let old_term = sym_table.insert(name.to_string(), BitwuzlaTerm { term });
            assert!(old_term.is_none());
            term
        };
        self.symbol_cache.set(sym_table);
        BitwuzlaTerm { term }
    }

    create_converter_binary_function_bitwuzla!(mk_eq, BITWUZLA_KIND_EQUAL);

    fn mk_bv_sort(&self, size: u64) -> BitwuzlaSort {
        BitwuzlaSort {
            sort: unsafe { smithril_bitwuzla_sys::bitwuzla_mk_bv_sort(self.term_manager(), size) },
        }
    }

    fn mk_bool_sort(&self) -> BitwuzlaSort {
        BitwuzlaSort {
            sort: unsafe { smithril_bitwuzla_sys::bitwuzla_mk_bool_sort(self.term_manager()) },
        }
    }

    fn mk_array_sort(&self, index: &BitwuzlaSort, element: &BitwuzlaSort) -> BitwuzlaSort {
        let i = index.sort;
        let e = element.sort;
        BitwuzlaSort {
            sort: unsafe {
                smithril_bitwuzla_sys::bitwuzla_mk_array_sort(self.term_manager(), i, e)
            },
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

    fn mk_smt_bool(&self, val: bool) -> BitwuzlaTerm {
        let term = unsafe {
            match val {
                true => smithril_bitwuzla_sys::bitwuzla_mk_true(self.term_manager()),
                false => smithril_bitwuzla_sys::bitwuzla_mk_false(self.term_manager()),
            }
        };
        BitwuzlaTerm { term }
    }

    create_converter_binary_function_bitwuzla!(mk_and, BITWUZLA_KIND_AND);
    create_converter_binary_function_bitwuzla!(mk_bvadd, BITWUZLA_KIND_BV_ADD);
    create_converter_binary_function_bitwuzla!(mk_bvand, BITWUZLA_KIND_BV_AND);
    create_converter_binary_function_bitwuzla!(mk_bvashr, BITWUZLA_KIND_BV_ASHR);
    create_converter_binary_function_bitwuzla!(mk_bvlshr, BITWUZLA_KIND_BV_SHR);
    create_converter_binary_function_bitwuzla!(mk_bvnand, BITWUZLA_KIND_BV_NAND);
    create_converter_unary_function_bitwuzla!(mk_bvneg, BITWUZLA_KIND_BV_NEG);
    create_converter_unary_function_bitwuzla!(mk_bvnot, BITWUZLA_KIND_BV_NOT);
    create_converter_binary_function_bitwuzla!(mk_bvor, BITWUZLA_KIND_BV_OR);
    create_converter_binary_function_bitwuzla!(mk_bvnor, BITWUZLA_KIND_BV_NOR);
    create_converter_binary_function_bitwuzla!(mk_bvnxor, BITWUZLA_KIND_BV_XNOR);
    create_converter_binary_function_bitwuzla!(mk_bvsdiv, BITWUZLA_KIND_BV_SDIV);
    create_converter_binary_function_bitwuzla!(mk_bvsge, BITWUZLA_KIND_BV_SGE);
    create_converter_binary_function_bitwuzla!(mk_bvsgt, BITWUZLA_KIND_BV_SGT);
    create_converter_binary_function_bitwuzla!(mk_bvshl, BITWUZLA_KIND_BV_SHL);
    create_converter_binary_function_bitwuzla!(mk_bvsle, BITWUZLA_KIND_BV_SLE);
    create_converter_binary_function_bitwuzla!(mk_bvslt, BITWUZLA_KIND_BV_SLT);
    create_converter_binary_function_bitwuzla!(mk_bvsmod, BITWUZLA_KIND_BV_SMOD);
    create_converter_binary_function_bitwuzla!(mk_bvsub, BITWUZLA_KIND_BV_SUB);
    create_converter_binary_function_bitwuzla!(mk_bvudiv, BITWUZLA_KIND_BV_UDIV);
    create_converter_binary_function_bitwuzla!(mk_bvuge, BITWUZLA_KIND_BV_UGE);
    create_converter_binary_function_bitwuzla!(mk_bvugt, BITWUZLA_KIND_BV_UGT);
    create_converter_binary_function_bitwuzla!(mk_bvule, BITWUZLA_KIND_BV_ULE);
    create_converter_binary_function_bitwuzla!(mk_bvult, BITWUZLA_KIND_BV_ULT);
    create_converter_binary_function_bitwuzla!(mk_bvumod, BITWUZLA_KIND_BV_UREM);
    create_converter_binary_function_bitwuzla!(mk_bvxor, BITWUZLA_KIND_BV_XOR);
    create_converter_binary_function_bitwuzla!(mk_implies, BITWUZLA_KIND_IMPLIES);
    create_converter_binary_function_bitwuzla!(mk_neq, BITWUZLA_KIND_DISTINCT);
    create_converter_unary_function_bitwuzla!(mk_not, BITWUZLA_KIND_NOT);
    create_converter_binary_function_bitwuzla!(mk_or, BITWUZLA_KIND_OR);
    create_converter_binary_function_bitwuzla!(mk_xor, BITWUZLA_KIND_XOR);
    create_converter_binary_function_bitwuzla!(mk_bvmul, BITWUZLA_KIND_BV_MUL);
    create_converter_binary_function_bitwuzla!(mk_select, BITWUZLA_KIND_ARRAY_SELECT);
    create_converter_ternary_function_bitwuzla!(mk_store, BITWUZLA_KIND_ARRAY_STORE);
}

impl UnsatCoreSolver for BitwuzlaSolver {
    fn unsat_core(&self) -> Vec<Term> {
        let u_core_bitwuzla = GeneralUnsatCoreSolver::unsat_core(self);
        let mut u_core: Vec<Term> = Vec::new();
        for cur_term in u_core_bitwuzla {
            let cur_asserted_terms_map = self.asserted_terms_map.take();
            match cur_asserted_terms_map.get(&cur_term) {
                Some(t) => u_core.push(t.clone()),
                None => panic!("Term not found in asserted_terms_map"),
            }
            self.asserted_terms_map.set(cur_asserted_terms_map);
        }
        u_core
    }
}

impl Solver for BitwuzlaSolver {
    fn assert(&self, term: &crate::generalized::Term) {
        let context = self.context.as_ref();
        let cur_bitwuzla_term = context.convert_term(term);
        GeneralSolver::assert(self, &cur_bitwuzla_term);
        let mut cur_asserted_terms_map = self.asserted_terms_map.take();
        cur_asserted_terms_map.insert(cur_bitwuzla_term, term.clone());
        self.asserted_terms_map.set(cur_asserted_terms_map);
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
                let res = Term {
                    term: UnsortedTerm::Constant(GenConstant::Numeral(bv_const)),
                    sort: term.sort.clone(),
                };
                Some(res)
            }
            Sort::BoolSort() => {
                let bitwuzla_string =
                    unsafe { smithril_bitwuzla_sys::bitwuzla_term_to_string(expr.term) };
                let s_cstr: &CStr = unsafe { CStr::from_ptr(bitwuzla_string) };
                let s = s_cstr.to_string_lossy().into_owned();
                match s.as_str() {
                    "true" => {
                        let res = Term {
                            term: UnsortedTerm::Constant(GenConstant::Boolean(true)),
                            sort: term.sort.clone(),
                        };
                        Some(res)
                    }
                    "false" => {
                        let res = Term {
                            term: UnsortedTerm::Constant(GenConstant::Boolean(false)),
                            sort: term.sort.clone(),
                        };
                        Some(res)
                    }
                    _ => {
                        panic!("Can't get boolean value from bitwuzla")
                    }
                }
            }

            Sort::ArraySort(_, _) => panic!("Unexpected sort"),
        }
    }

    fn reset(&self) {
        GeneralSolver::reset(self)
    }
}
