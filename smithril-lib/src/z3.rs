use crate::generalized::Context;
use crate::generalized::Factory;
use crate::generalized::FloatingPointAsBvStr;
use crate::generalized::GenConstant;
use crate::generalized::GeneralArrayConverter;
use crate::generalized::GeneralBitVectorConverter;
use crate::generalized::GeneralBoolConverter;
use crate::generalized::GeneralConverter;
use crate::generalized::GeneralFpConverter;
use crate::generalized::GeneralOptions;
use crate::generalized::GeneralSolver;
use crate::generalized::GeneralSort;
use crate::generalized::GeneralTerm;
use crate::generalized::Interrupter;
use crate::generalized::OptionKind;
use crate::generalized::Options;
use crate::generalized::RoundingMode;
use crate::generalized::Solver;
use crate::generalized::SolverResult;
use crate::generalized::Sort;
use crate::generalized::Term;
use crate::generalized::UnsortedTerm;
use std::ffi::c_uint;

use crate::utils;
use core::panic;
use std::collections::HashMap;
use std::collections::HashSet;
use std::ffi::CStr;
use std::ffi::CString;
use std::hash::Hash;
use std::ptr;
use std::sync::Arc;
use std::sync::RwLock;

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Z3Context {
    context: smithril_z3_sys::Z3_context,
}

unsafe impl Send for Z3Context {}
unsafe impl Sync for Z3Context {}

impl Z3Context {
    fn new() -> Self {
        Z3Context {
            context: unsafe {
                let cfg = smithril_z3_sys::Z3_mk_config();
                let ctx = smithril_z3_sys::Z3_mk_context(cfg);
                smithril_z3_sys::Z3_set_error_handler(ctx, None);
                smithril_z3_sys::Z3_set_ast_print_mode(
                    ctx,
                    smithril_z3_sys::Z3_PRINT_SMTLIB2_COMPLIANT,
                );
                smithril_z3_sys::Z3_del_config(cfg);
                ctx
            },
        }
    }

    fn check_error(&self) -> smithril_z3_sys::Z3_error_code {
        let error = unsafe { smithril_z3_sys::Z3_get_error_code(self.context) };
        if error != smithril_z3_sys::Z3_OK {
            let error_msg = unsafe {
                CStr::from_ptr(smithril_z3_sys::Z3_get_error_msg(self.context, error))
                    .to_str()
                    .unwrap()
            };
            panic!("{}", error_msg);
        }
        error
    }
}

impl Default for Z3Context {
    fn default() -> Self {
        Z3Context::new()
    }
}

impl Drop for Z3Context {
    fn drop(&mut self) {
        unsafe {
            smithril_z3_sys::Z3_del_context(self.context);
        };
    }
}

struct Z3OptionsSys(smithril_z3_sys::Z3_params);

unsafe impl Send for Z3OptionsSys {}
unsafe impl Sync for Z3OptionsSys {}

pub struct Z3Options {
    options: Z3OptionsSys,
    pub context: Arc<Z3Converter>,
}

impl PartialEq for Z3Options {
    fn eq(&self, other: &Self) -> bool {
        self.options.0.eq(&other.options.0)
    }
}

impl Eq for Z3Options {}

impl Hash for Z3Options {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.options.0.hash(state);
    }
}

impl From<(Arc<Z3Converter>, &Options)> for Z3Options {
    fn from(value: (Arc<Z3Converter>, &Options)) -> Self {
        let context = value.0;
        let opt = value.1;
        let options = Self::new(context);
        for opt_kind in opt.bool_options.iter() {
            match opt_kind {
                (OptionKind::ProduceUnsatCore, val) => options.set_produce_unsat_core(*val),
            }
        }
        options
    }
}

impl Z3Options {
    pub fn new(conv: Arc<Z3Converter>) -> Self {
        let params = unsafe {
            let solver_parameters = smithril_z3_sys::Z3_mk_params(conv.context());
            smithril_z3_sys::Z3_params_inc_ref(conv.context(), solver_parameters);
            solver_parameters
        };
        Self {
            options: Z3OptionsSys(params),
            context: conv.clone(),
        }
    }
}

struct Z3SolverSys(smithril_z3_sys::Z3_solver);

unsafe impl Send for Z3SolverSys {}
unsafe impl Sync for Z3SolverSys {}

pub struct Z3Interrupter {
    context: smithril_z3_sys::Z3_context,
    solver: smithril_z3_sys::Z3_solver,
}

unsafe impl Send for Z3Interrupter {}
unsafe impl Sync for Z3Interrupter {}

impl Z3Interrupter {
    fn check_error(&self) -> smithril_z3_sys::Z3_error_code {
        let error = unsafe { smithril_z3_sys::Z3_get_error_code(self.context) };
        if error != smithril_z3_sys::Z3_OK {
            let error_msg = unsafe {
                CStr::from_ptr(smithril_z3_sys::Z3_get_error_msg(self.context, error))
                    .to_str()
                    .unwrap()
            };
            panic!("{}", error_msg);
        }
        error
    }
}

impl Interrupter for Z3Interrupter {
    fn interrupt(&self) {
        unsafe {
            smithril_z3_sys::Z3_solver_interrupt(self.context, self.solver);
            self.check_error();
        }
    }
}

pub struct Z3Factory {
    contexts: HashSet<Arc<Z3Converter>>,
    solvers: HashSet<Arc<Z3Solver>>,
}

impl Z3Factory {
    fn new() -> Self {
        Self {
            contexts: HashSet::new(),
            solvers: HashSet::new(),
        }
    }
}

impl Drop for Z3Options {
    fn drop(&mut self) {
        unsafe { smithril_z3_sys::Z3_params_dec_ref(self.context.context(), self.options.0) };
    }
}

impl GeneralOptions for Z3Options {
    fn set_produce_unsat_core(&self, val: bool) {
        let unsat_cstr = CString::new("unsat_core").unwrap();
        unsafe {
            let param_symbol =
                smithril_z3_sys::Z3_mk_string_symbol(self.context.context(), unsat_cstr.as_ptr());
            smithril_z3_sys::Z3_params_set_bool(
                self.context.context(),
                self.options.0,
                param_symbol,
                val,
            );
        }
    }

    fn get_produce_unsat_core(&self) -> bool {
        let res = unsafe {
            let param_str =
                smithril_z3_sys::Z3_params_to_string(self.context.context(), self.options.0);
            CStr::from_ptr(param_str)
                .to_string_lossy()
                .contains("unsat_core true")
        };
        res
    }
}
impl Default for Z3Factory {
    fn default() -> Self {
        Z3Factory::new()
    }
}

impl Factory<Z3Converter, Z3Solver, Z3Interrupter> for Z3Factory {
    fn new_context(&mut self) -> Arc<Z3Converter> {
        let context = Arc::new(Z3Converter::default());
        self.contexts.insert(context.clone());
        context
    }

    fn new_solver(&mut self, context: Arc<Z3Converter>, options: &Options) -> Arc<Z3Solver> {
        let solver = Arc::new(Z3Solver::new(context.clone(), options));
        self.solvers.insert(solver.clone());
        solver
    }

    fn delete_context(&mut self, context: Arc<Z3Converter>) {
        self.contexts.remove(&context);
        assert_eq!(Arc::strong_count(&context), 1);
    }

    fn delete_solver(&mut self, solver: Arc<Z3Solver>) {
        self.solvers.remove(&solver);
        assert_eq!(Arc::strong_count(&solver), 1);
    }

    fn new_interrupter(&self, solver: Arc<Z3Solver>) -> Z3Interrupter {
        Z3Interrupter {
            context: solver.context.context(),
            solver: solver.solver.0,
        }
    }
}

macro_rules! create_converter_fp_unary_function_z3 {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, r_mode: &RoundingMode, term: &Z3Term) -> Z3Term {
            Z3Term::new(&self.context, unsafe {
                smithril_z3_sys::$z3_sys_func_name(
                    self.context(),
                    self.get_rouning_mode(r_mode.clone()).term,
                    term.term,
                )
            })
        }
    };
}

macro_rules! create_converter_fp_binary_function_z3 {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, r_mode: &RoundingMode, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
            Z3Term::new(&self.context, unsafe {
                smithril_z3_sys::$z3_sys_func_name(
                    self.context(),
                    self.get_rouning_mode(r_mode.clone()).term,
                    term1.term,
                    term2.term,
                )
            })
        }
    };
}

macro_rules! create_converter_fp_unary_no_rm_function_z3 {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, _r_mode: &RoundingMode, term: &Z3Term) -> Z3Term {
            Z3Term::new(&self.context, unsafe {
                smithril_z3_sys::$z3_sys_func_name(self.context(), term.term)
            })
        }
    };
}

macro_rules! create_converter_fp_binary_no_rm_function_z3 {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, _r_mode: &RoundingMode, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
            Z3Term::new(&self.context, unsafe {
                smithril_z3_sys::$z3_sys_func_name(self.context(), term1.term, term2.term)
            })
        }
    };
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Z3Term {
    pub term: smithril_z3_sys::Z3_ast,
}

unsafe impl Send for Z3Term {}
unsafe impl Sync for Z3Term {}

impl Z3Term {
    pub fn new(context: &Z3Context, term: smithril_z3_sys::Z3_ast) -> Self {
        context.check_error();
        Self { term }
    }
}

pub struct Z3Sort {
    pub sort: smithril_z3_sys::Z3_sort,
}

unsafe impl Send for Z3Sort {}
unsafe impl Sync for Z3Sort {}

impl Z3Sort {
    pub fn new(context: &Z3Context, sort: smithril_z3_sys::Z3_sort) -> Self {
        context.check_error();
        Self { sort }
    }
}

impl GeneralSort for Z3Sort {}

impl GeneralTerm for Z3Term {}

pub struct Z3Solver {
    pub options: Z3Options,
    solver: Z3SolverSys,
    pub context: Arc<Z3Converter>,
    pub asserted_terms_map: RwLock<HashMap<Z3Term, Term>>,
    pub unsat_map: RwLock<HashMap<Z3Term, Z3Term>>,
}

impl PartialEq for Z3Solver {
    fn eq(&self, other: &Self) -> bool {
        self.options.eq(&other.options) && self.solver.0.eq(&other.solver.0)
    }
}

impl Eq for Z3Solver {}

impl Hash for Z3Solver {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.options.hash(state);
        self.solver.0.hash(state)
    }
}

impl Z3Solver {
    pub fn new(context: Arc<Z3Converter>, options: &Options) -> Self {
        let options = Z3Options::from((context.clone(), options));
        let solver = unsafe {
            let native_solver = smithril_z3_sys::Z3_mk_solver(context.context());
            smithril_z3_sys::Z3_solver_inc_ref(context.context(), native_solver);
            smithril_z3_sys::Z3_solver_set_params(
                context.context(),
                native_solver,
                options.options.0,
            );
            native_solver
        };

        Self {
            options,
            solver: Z3SolverSys(solver),
            context,
            asserted_terms_map: RwLock::new(HashMap::new()),
            unsat_map: RwLock::new(HashMap::new()),
        }
    }
}

pub struct Z3Converter {
    pub context: Z3Context,
}

impl Context for Z3Converter {}

impl PartialEq for Z3Converter {
    fn eq(&self, other: &Self) -> bool {
        self.context.eq(&other.context)
    }
}

impl Eq for Z3Converter {}

impl Hash for Z3Converter {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.context.hash(state)
    }
}

impl Z3Converter {
    pub fn new(context: Z3Context) -> Self {
        Self { context }
    }

    pub fn context(&self) -> smithril_z3_sys::Z3_context {
        self.context.context
    }
}

impl Default for Z3Converter {
    fn default() -> Self {
        let context = Z3Context::default();
        Self::new(context)
    }
}

impl Drop for Z3Solver {
    fn drop(&mut self) {
        unsafe {
            smithril_z3_sys::Z3_solver_dec_ref(self.context.context(), self.solver.0);
        };
    }
}

impl Z3Converter {}

macro_rules! create_converter_binary_function_z3_narg {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
            Z3Term::new(&self.context, unsafe {
                let args = vec![term1.term, term2.term];
                smithril_z3_sys::$z3_sys_func_name(self.context(), 2, args.as_ptr())
            })
        }
    };
}

macro_rules! create_converter_unary_function_z3 {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, term: &Z3Term) -> Z3Term {
            Z3Term::new(&self.context, unsafe {
                smithril_z3_sys::$z3_sys_func_name(self.context(), term.term)
            })
        }
    };
}

macro_rules! create_converter_binary_function_z3 {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
            Z3Term::new(&self.context, unsafe {
                smithril_z3_sys::$z3_sys_func_name(self.context(), term1.term, term2.term)
            })
        }
    };
}

macro_rules! create_converter_ternary_function_z3 {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, term1: &Z3Term, term2: &Z3Term, term3: &Z3Term) -> Z3Term {
            Z3Term::new(&self.context, unsafe {
                smithril_z3_sys::$z3_sys_func_name(
                    self.context(),
                    term1.term,
                    term2.term,
                    term3.term,
                )
            })
        }
    };
}

impl GeneralSolver<Z3Sort, Z3Term, Z3Options, Z3Converter> for Z3Solver {
    fn unsat_core(&self) -> Vec<Z3Term> {
        let context = self.context.as_ref();
        let u_core =
            unsafe { smithril_z3_sys::Z3_solver_get_unsat_core(context.context(), self.solver.0) };
        let mut res: Vec<Z3Term> = Vec::new();
        let cur_unsat_map = self.unsat_map.read().unwrap();
        let size = unsafe { smithril_z3_sys::Z3_ast_vector_size(context.context(), u_core) };
        for i in 0..size {
            let track_term =
                unsafe { smithril_z3_sys::Z3_ast_vector_get(context.context(), u_core, i) };
            let cur_term = cur_unsat_map
                .get(&Z3Term { term: track_term })
                .expect("Term not found in unsat_map");
            res.push(cur_term.clone());
        }
        res
    }

    fn assert(&self, term: &Z3Term) {
        if self.options.get_produce_unsat_core() {
            unsafe {
                let mut cur_unsat_map = self.unsat_map.write().unwrap();
                let cur_str = "sym".to_owned() + cur_unsat_map.len().to_string().as_str();
                let track_term = self
                    .context
                    .mk_smt_symbol(cur_str.as_str(), &self.context.mk_bool_sort());
                smithril_z3_sys::Z3_solver_assert_and_track(
                    self.context.context(),
                    self.solver.0,
                    term.term,
                    track_term.term,
                );
                self.context.context.check_error();
                cur_unsat_map.insert(track_term, term.clone());
            }
        } else {
            unsafe {
                smithril_z3_sys::Z3_solver_assert(self.context.context(), self.solver.0, term.term);
            }
        }
    }

    fn eval(&self, term1: &Z3Term) -> Option<Z3Term> {
        let context = self.context.as_ref();
        let mut r: smithril_z3_sys::Z3_ast = ptr::null_mut();
        let model_completion = false;
        let t = term1.term;
        let status = unsafe {
            smithril_z3_sys::Z3_inc_ref(context.context(), t);
            let status = smithril_z3_sys::Z3_model_eval(
                context.context(),
                smithril_z3_sys::Z3_solver_get_model(context.context(), self.solver.0),
                t,
                model_completion,
                &mut r,
            );
            smithril_z3_sys::Z3_dec_ref(context.context(), t);
            status
        };
        if status {
            let res = Z3Term::new(&context.context, r);
            Some(res)
        } else {
            None
        }
    }

    fn reset(&self) {
        let context = self.context.as_ref();
        unsafe {
            smithril_z3_sys::Z3_solver_reset(context.context(), self.solver.0);
            context.context.check_error();
        }
    }

    fn interrupt(&self) {
        let context = self.context.as_ref();
        unsafe {
            smithril_z3_sys::Z3_solver_interrupt(context.context(), self.solver.0);
            context.context.check_error();
        }
    }

    fn check_sat(&self) -> SolverResult {
        let context = self.context.as_ref();
        let res = unsafe { smithril_z3_sys::Z3_solver_check(context.context(), self.solver.0) };
        context.context.check_error();
        match res {
            smithril_z3_sys::Z3_L_TRUE => SolverResult::Sat,
            smithril_z3_sys::Z3_L_FALSE => SolverResult::Unsat,
            _ => SolverResult::Unknown,
        }
    }
}

impl GeneralArrayConverter<Z3Sort, Z3Term> for Z3Converter {
    fn mk_array_sort(&self, index: &Z3Sort, element: &Z3Sort) -> Z3Sort {
        let i = index.sort;
        let e = element.sort;
        Z3Sort::new(&self.context, unsafe {
            smithril_z3_sys::Z3_mk_array_sort(self.context(), i, e)
        })
    }

    create_converter_binary_function_z3!(mk_select, Z3_mk_select);
    create_converter_ternary_function_z3!(mk_store, Z3_mk_store);
}

impl GeneralBoolConverter<Z3Sort, Z3Term> for Z3Converter {
    fn mk_bool_sort(&self) -> Z3Sort {
        Z3Sort::new(&self.context, unsafe {
            smithril_z3_sys::Z3_mk_bool_sort(self.context())
        })
    }
    fn mk_smt_bool(&self, val: bool) -> Z3Term {
        let term = unsafe {
            if val {
                smithril_z3_sys::Z3_mk_true(self.context())
            } else {
                smithril_z3_sys::Z3_mk_false(self.context())
            }
        };
        Z3Term::new(&self.context, term)
    }

    create_converter_binary_function_z3_narg!(mk_neq, Z3_mk_distinct);
    create_converter_binary_function_z3_narg!(mk_and, Z3_mk_and);
    create_converter_binary_function_z3_narg!(mk_or, Z3_mk_or);
    create_converter_binary_function_z3!(mk_implies, Z3_mk_implies);
    create_converter_unary_function_z3!(mk_not, Z3_mk_not);
    create_converter_binary_function_z3!(mk_xor, Z3_mk_xor);
}

impl GeneralBitVectorConverter<Z3Sort, Z3Term> for Z3Converter {
    fn mk_bv_sort(&self, size: u64) -> Z3Sort {
        Z3Sort::new(&self.context, unsafe {
            smithril_z3_sys::Z3_mk_bv_sort(self.context(), size as u32)
        })
    }
    fn mk_bv_value_uint64(&self, sort: &Z3Sort, val: u64) -> Z3Term {
        Z3Term::new(&self.context, unsafe {
            smithril_z3_sys::Z3_mk_unsigned_int64(self.context(), val, sort.sort)
        })
    }
    fn mk_bv_nxor(&self, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
        self.mk_not(&self.mk_xor(term1, term2))
    }

    create_converter_binary_function_z3!(mk_bv_add, Z3_mk_bvadd);
    create_converter_binary_function_z3!(mk_bv_and, Z3_mk_bvand);
    create_converter_binary_function_z3!(mk_bv_ashr, Z3_mk_bvashr);
    create_converter_binary_function_z3!(mk_bv_lshr, Z3_mk_bvlshr);
    create_converter_binary_function_z3!(mk_bv_mul, Z3_mk_bvmul);
    create_converter_binary_function_z3!(mk_bv_nand, Z3_mk_bvnand);
    create_converter_unary_function_z3!(mk_bv_neg, Z3_mk_bvneg);
    create_converter_binary_function_z3!(mk_bv_nor, Z3_mk_bvnor);
    create_converter_unary_function_z3!(mk_bv_not, Z3_mk_bvnot);
    create_converter_binary_function_z3!(mk_bv_or, Z3_mk_bvor);
    create_converter_binary_function_z3!(mk_bv_sdiv, Z3_mk_bvsdiv);
    create_converter_binary_function_z3!(mk_bv_sge, Z3_mk_bvsge);
    create_converter_binary_function_z3!(mk_bv_sgt, Z3_mk_bvsgt);
    create_converter_binary_function_z3!(mk_bv_shl, Z3_mk_bvshl);
    create_converter_binary_function_z3!(mk_bv_sle, Z3_mk_bvsle);
    create_converter_binary_function_z3!(mk_bv_slt, Z3_mk_bvslt);
    create_converter_binary_function_z3!(mk_bv_smod, Z3_mk_bvsmod);
    create_converter_binary_function_z3!(mk_bv_sub, Z3_mk_bvsub);
    create_converter_binary_function_z3!(mk_bv_udiv, Z3_mk_bvudiv);
    create_converter_binary_function_z3!(mk_bv_uge, Z3_mk_bvuge);
    create_converter_binary_function_z3!(mk_bv_ugt, Z3_mk_bvugt);
    create_converter_binary_function_z3!(mk_bv_ule, Z3_mk_bvule);
    create_converter_binary_function_z3!(mk_bv_ult, Z3_mk_bvult);
    create_converter_binary_function_z3!(mk_bv_umod, Z3_mk_bvurem);
    create_converter_binary_function_z3!(mk_bv_xor, Z3_mk_bvxor);
}

impl GeneralFpConverter<Z3Sort, Z3Term> for Z3Converter {
    fn mk_fp_sort(&self, ew: u64, sw: u64) -> Z3Sort {
        Z3Sort {
            sort: unsafe { smithril_z3_sys::Z3_mk_fpa_sort(self.context(), ew as u32, sw as u32) },
        }
    }

    fn mk_fp_value(
        &self,
        bv_sign: &Z3Term,
        bv_exponent: &Z3Term,
        bv_significand: &Z3Term,
    ) -> Z3Term {
        unsafe {
            let term = smithril_z3_sys::Z3_mk_fpa_fp(
                self.context(),
                bv_sign.term,
                bv_exponent.term,
                bv_significand.term,
            );
            Z3Term::new(&self.context, term)
        }
    }

    fn fp_get_bv_exp_size(&self, term1: &Z3Term) -> u64 {
        unsafe {
            let exp_sort = smithril_z3_sys::Z3_get_sort(self.context(), term1.term);
            smithril_z3_sys::Z3_fpa_get_ebits(self.context(), exp_sort) as u64
        }
    }

    fn fp_get_bv_sig_size(&self, term1: &Z3Term) -> u64 {
        unsafe {
            let exp_sort = smithril_z3_sys::Z3_get_sort(self.context(), term1.term);
            (smithril_z3_sys::Z3_fpa_get_sbits(self.context(), exp_sort) - 1) as u64
        }
    }

    fn fp_get_values_ieee(&self, term1: &Z3Term) -> crate::generalized::FloatingPointAsBvStr {
        unsafe {
            let bv_term = smithril_z3_sys::Z3_mk_fpa_to_ieee_bv(self.context(), term1.term);
            let exp_size = self.fp_get_bv_exp_size(term1) as c_uint;
            let sig_size = self.fp_get_bv_sig_size(term1) as c_uint;

            let sign_term = smithril_z3_sys::Z3_mk_extract(
                self.context(),
                exp_size + sig_size,
                exp_size + sig_size,
                bv_term,
            );
            let sign_term = smithril_z3_sys::Z3_simplify(self.context(), sign_term);

            let exponent_term = smithril_z3_sys::Z3_mk_extract(
                self.context(),
                exp_size + sig_size - 1,
                sig_size,
                bv_term,
            );
            let exponent_term = smithril_z3_sys::Z3_simplify(self.context(), exponent_term);

            let significand_term =
                smithril_z3_sys::Z3_mk_extract(self.context(), sig_size - 1, 0, bv_term);
            let significand_term = smithril_z3_sys::Z3_simplify(self.context(), significand_term);

            let sign_str: *const i8 =
                smithril_z3_sys::Z3_get_numeral_binary_string(self.context(), sign_term);
            let sign = CStr::from_ptr(sign_str).to_string_lossy().into_owned();

            let exponent_str: *const i8 =
                smithril_z3_sys::Z3_get_numeral_binary_string(self.context(), exponent_term);
            let exponent = CStr::from_ptr(exponent_str).to_string_lossy().into_owned();

            let significand_str: *const i8 =
                smithril_z3_sys::Z3_get_numeral_binary_string(self.context(), significand_term);
            let significand = CStr::from_ptr(significand_str)
                .to_string_lossy()
                .into_owned();

            FloatingPointAsBvStr {
                sign,
                exponent,
                significand,
            }
        }
    }

    fn fp_is_nan(&self, term1: &Z3Term) -> Z3Term {
        unsafe {
            let term = smithril_z3_sys::Z3_mk_fpa_is_nan(self.context(), term1.term);
            Z3Term::new(&self.context, term)
        }
    }

    fn fp_is_inf(&self, term1: &Z3Term) -> Z3Term {
        unsafe {
            let term = smithril_z3_sys::Z3_mk_fpa_is_infinite(self.context(), term1.term);
            Z3Term::new(&self.context, term)
        }
    }

    fn fp_is_normal(&self, term1: &Z3Term) -> Z3Term {
        unsafe {
            let term = smithril_z3_sys::Z3_mk_fpa_is_normal(self.context(), term1.term);
            Z3Term::new(&self.context, term)
        }
    }

    fn fp_is_subnormal(&self, term1: &Z3Term) -> Z3Term {
        unsafe {
            let term = smithril_z3_sys::Z3_mk_fpa_is_subnormal(self.context(), term1.term);
            Z3Term::new(&self.context, term)
        }
    }

    fn fp_is_zero(&self, term1: &Z3Term) -> Z3Term {
        unsafe {
            let term = smithril_z3_sys::Z3_mk_fpa_is_zero(self.context(), term1.term);
            Z3Term::new(&self.context, term)
        }
    }

    fn fp_is_pos(&self, term1: &Z3Term) -> Z3Term {
        unsafe {
            let term = smithril_z3_sys::Z3_mk_fpa_is_positive(self.context(), term1.term);
            Z3Term::new(&self.context, term)
        }
    }

    fn fp_eq(&self, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
        unsafe {
            let term = smithril_z3_sys::Z3_mk_fpa_eq(self.context(), term1.term, term2.term);
            Z3Term::new(&self.context, term)
        }
    }

    create_converter_fp_binary_no_rm_function_z3!(mk_fp_rem, Z3_mk_fpa_rem);
    create_converter_fp_binary_no_rm_function_z3!(mk_fp_min, Z3_mk_fpa_min);
    create_converter_fp_binary_no_rm_function_z3!(mk_fp_max, Z3_mk_fpa_max);
    create_converter_fp_binary_no_rm_function_z3!(mk_fp_lt, Z3_mk_fpa_lt);
    create_converter_fp_binary_no_rm_function_z3!(mk_fp_leq, Z3_mk_fpa_leq);
    create_converter_fp_binary_no_rm_function_z3!(mk_fp_gt, Z3_mk_fpa_gt);
    create_converter_fp_binary_no_rm_function_z3!(mk_fp_geq, Z3_mk_fpa_geq);
    create_converter_fp_binary_function_z3!(mk_fp_add, Z3_mk_fpa_add);
    create_converter_fp_binary_function_z3!(mk_fp_sub, Z3_mk_fpa_sub);
    create_converter_fp_binary_function_z3!(mk_fp_mul, Z3_mk_fpa_mul);
    create_converter_fp_binary_function_z3!(mk_fp_div, Z3_mk_fpa_div);

    create_converter_fp_unary_function_z3!(mk_fp_sqrt, Z3_mk_fpa_sqrt);
    create_converter_fp_unary_function_z3!(mk_fp_rti, Z3_mk_fpa_round_to_integral);
    create_converter_fp_unary_no_rm_function_z3!(mk_fp_abs, Z3_mk_fpa_abs);
    create_converter_fp_unary_no_rm_function_z3!(mk_fp_neg, Z3_mk_fpa_neg);

    fn get_rouning_mode(&self, r_mode: RoundingMode) -> Z3Term {
        unsafe {
            let rm = match r_mode {
                RoundingMode::RNA => smithril_z3_sys::Z3_mk_fpa_rna(self.context()),
                RoundingMode::RNE => smithril_z3_sys::Z3_mk_fpa_rne(self.context()),
                RoundingMode::RTN => smithril_z3_sys::Z3_mk_fpa_rtn(self.context()),
                RoundingMode::RTP => smithril_z3_sys::Z3_mk_fpa_rtp(self.context()),
                RoundingMode::RTZ => smithril_z3_sys::Z3_mk_fpa_rtz(self.context()),
            };
            Z3Term::new(&self.context, rm)
        }
    }

    fn mk_fp_pos_zero(&self, ew: u64, sw: u64) -> Z3Term {
        unsafe {
            let sort = self.mk_fp_sort(ew, sw);
            let term = smithril_z3_sys::Z3_mk_fpa_zero(self.context(), sort.sort, false);
            Z3Term::new(&self.context, term)
        }
    }

    fn mk_fp_pos_inf(&self, ew: u64, sw: u64) -> Z3Term {
        unsafe {
            let sort = self.mk_fp_sort(ew, sw);
            let term = smithril_z3_sys::Z3_mk_fpa_inf(self.context(), sort.sort, false);
            Z3Term::new(&self.context, term)
        }
    }

    fn mk_fp_neg_zero(&self, ew: u64, sw: u64) -> Z3Term {
        unsafe {
            let sort = self.mk_fp_sort(ew, sw);
            let term = smithril_z3_sys::Z3_mk_fpa_zero(self.context(), sort.sort, true);
            Z3Term::new(&self.context, term)
        }
    }

    fn mk_fp_neg_inf(&self, ew: u64, sw: u64) -> Z3Term {
        unsafe {
            let sort = self.mk_fp_sort(ew, sw);
            let term = smithril_z3_sys::Z3_mk_fpa_inf(self.context(), sort.sort, true);
            Z3Term::new(&self.context, term)
        }
    }

    fn mk_fp_to_fp_from_fp(&self, rmterm: &Z3Term, term1: &Z3Term, ew: u64, sw: u64) -> Z3Term {
        unsafe {
            let sort = self.mk_fp_sort(ew, sw);
            let term = smithril_z3_sys::Z3_mk_fpa_to_fp_float(
                self.context(),
                rmterm.term,
                term1.term,
                sort.sort,
            );
            Z3Term::new(&self.context, term)
        }
    }

    fn mk_fp_to_sbv(&self, rmterm: &Z3Term, term1: &Z3Term, w: u64) -> Z3Term {
        unsafe {
            let term = smithril_z3_sys::Z3_mk_fpa_to_sbv(
                self.context(),
                rmterm.term,
                term1.term,
                w as u32,
            );
            Z3Term::new(&self.context, term)
        }
    }

    fn mk_fp_to_ubv(&self, rmterm: &Z3Term, term1: &Z3Term, w: u64) -> Z3Term {
        unsafe {
            let term = smithril_z3_sys::Z3_mk_fpa_to_ubv(
                self.context(),
                rmterm.term,
                term1.term,
                w as u32,
            );
            Z3Term::new(&self.context, term)
        }
    }

    fn mk_fp_to_fp_from_sbv(&self, rmterm: &Z3Term, term1: &Z3Term, ew: u64, sw: u64) -> Z3Term {
        unsafe {
            let sort = self.mk_fp_sort(ew, sw);
            let term = smithril_z3_sys::Z3_mk_fpa_to_fp_signed(
                self.context(),
                rmterm.term,
                term1.term,
                sort.sort,
            );
            Z3Term::new(&self.context, term)
        }
    }

    fn mk_fp_to_fp_from_ubv(&self, rmterm: &Z3Term, term1: &Z3Term, ew: u64, sw: u64) -> Z3Term {
        unsafe {
            let sort = self.mk_fp_sort(ew, sw);
            let term = smithril_z3_sys::Z3_mk_fpa_to_fp_unsigned(
                self.context(),
                rmterm.term,
                term1.term,
                sort.sort,
            );
            Z3Term::new(&self.context, term)
        }
    }

    fn mk_fp_extract(&self, high: u64, low: u64, term: &Z3Term) -> Z3Term {
        unsafe {
            let term =
                smithril_z3_sys::Z3_mk_extract(self.context(), high as u32, low as u32, term.term);
            Z3Term::new(&self.context, term)
        }
    }

    fn mk_fp_concat(&self, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
        unsafe {
            let term = smithril_z3_sys::Z3_mk_concat(self.context(), term1.term, term2.term);
            Z3Term::new(&self.context, term)
        }
    }
}

impl GeneralConverter<Z3Sort, Z3Term> for Z3Converter {
    fn mk_smt_symbol(&self, name: &str, sort: &Z3Sort) -> Z3Term {
        let name_cstr = CString::new(name).unwrap();
        let term = unsafe {
            let symbol = smithril_z3_sys::Z3_mk_string_symbol(self.context(), name_cstr.as_ptr());
            smithril_z3_sys::Z3_mk_const(self.context(), symbol, sort.sort)
        };
        Z3Term::new(&self.context, term)
    }

    fn try_get_bool_converter(&self) -> Option<&dyn GeneralBoolConverter<Z3Sort, Z3Term>> {
        Some(self)
    }

    fn try_get_bv_converter(&self) -> Option<&dyn GeneralBitVectorConverter<Z3Sort, Z3Term>> {
        Some(self)
    }

    fn try_get_array_converter(&self) -> Option<&dyn GeneralArrayConverter<Z3Sort, Z3Term>> {
        Some(self)
    }

    fn try_get_fp_converter(&self) -> Option<&dyn GeneralFpConverter<Z3Sort, Z3Term>> {
        Some(self)
    }
    create_converter_binary_function_z3!(mk_eq, Z3_mk_eq);
}

impl Solver for Z3Solver {
    fn unsat_core(&self) -> Vec<Term> {
        let u_core_z3 = GeneralSolver::unsat_core(self);
        let mut u_core: Vec<Term> = Vec::new();
        for cur_term in u_core_z3 {
            let cur_asserted_terms_map = self.asserted_terms_map.read().unwrap();
            match cur_asserted_terms_map.get(&cur_term) {
                Some(t) => u_core.push(t.clone()),
                None => panic!("Term not found in asserted_terms_map"),
            }
        }
        u_core
    }

    fn assert(&self, term: &crate::generalized::Term) {
        let context = self.context.as_ref();
        let cur_z3_term = context.convert_term(term);
        GeneralSolver::assert(self, &cur_z3_term);
        let mut cur_asserted_terms_map = self.asserted_terms_map.write().unwrap();
        cur_asserted_terms_map.insert(cur_z3_term, term.clone());
    }

    fn check_sat(&self) -> SolverResult {
        GeneralSolver::check_sat(self)
    }

    fn eval(&self, term: &Term) -> Option<Term> {
        let context = self.context.as_ref();
        let expr = GeneralSolver::eval(self, &context.convert_term(term))?;
        match term.sort {
            Sort::BvSort(_) => {
                let z3_string: *const i8 = unsafe {
                    smithril_z3_sys::Z3_get_numeral_binary_string(context.context(), expr.term)
                };
                let s = unsafe { CStr::from_ptr(z3_string).to_string_lossy().into_owned() };
                let bv_const = utils::binary2integer(s);
                let res = Term {
                    term: UnsortedTerm::Constant(GenConstant::Numeral(bv_const)),
                    sort: term.sort.clone(),
                };
                Some(res)
            }
            Sort::BoolSort() => {
                let z3_lbool =
                    unsafe { smithril_z3_sys::Z3_get_bool_value(context.context(), expr.term) };
                match z3_lbool {
                    smithril_z3_sys::Z3_L_FALSE => {
                        let res = Term {
                            term: UnsortedTerm::Constant(GenConstant::Boolean(false)),
                            sort: term.sort.clone(),
                        };
                        Some(res)
                    }
                    smithril_z3_sys::Z3_L_TRUE => {
                        let res = Term {
                            term: UnsortedTerm::Constant(GenConstant::Boolean(true)),
                            sort: term.sort.clone(),
                        };
                        Some(res)
                    }
                    _ => {
                        panic!("Can't get boolean value from Z3")
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
}
