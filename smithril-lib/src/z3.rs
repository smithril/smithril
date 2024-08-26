use crate::generalized::GenConstant;
use crate::generalized::GeneralConverter;
use crate::generalized::GeneralFactory;
use crate::generalized::GeneralOptions;
use crate::generalized::GeneralSolver;
use crate::generalized::GeneralSort;
use crate::generalized::GeneralTerm;
use crate::generalized::GeneralUnsatCoreSolver;
use crate::generalized::Interrupter;
use crate::generalized::OptionKind;
use crate::generalized::Options;
use crate::generalized::Solver;
use crate::generalized::SolverResult;
use crate::generalized::Sort;
use crate::generalized::Term;
use crate::generalized::UnsatCoreSolver;
use crate::generalized::UnsortedTerm;
use crate::utils;
use core::panic;
use std::cell::Cell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::ffi::CStr;
use std::ffi::CString;
use std::hash::Hash;
use std::ptr;
use std::rc::Rc;

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Z3Context {
    context: smithril_z3_sys::Z3_context,
}

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

pub struct Z3Options {
    pub options: smithril_z3_sys::Z3_params,
    pub context: Rc<Z3Converter>,
}

impl PartialEq for Z3Options {
    fn eq(&self, other: &Self) -> bool {
        self.options.eq(&other.options)
    }
}

impl Eq for Z3Options {}

impl Hash for Z3Options {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.options.hash(state);
    }
}

impl From<(Rc<Z3Converter>, &Options)> for Z3Options {
    fn from(value: (Rc<Z3Converter>, &Options)) -> Self {
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
    pub fn new(conv: Rc<Z3Converter>) -> Self {
        let params = unsafe {
            let solver_parameters = smithril_z3_sys::Z3_mk_params(conv.context());
            smithril_z3_sys::Z3_params_inc_ref(conv.context(), solver_parameters);
            solver_parameters
        };
        Self {
            options: params,
            context: conv.clone(),
        }
    }
}
struct Z3Holder(smithril_z3_sys::Z3_context, smithril_z3_sys::Z3_solver);

unsafe impl Send for Z3Holder {}
unsafe impl Sync for Z3Holder {}

pub struct Z3Interrupter {
    holder: Z3Holder,
}

impl Z3Interrupter {
    fn check_error(&self) -> smithril_z3_sys::Z3_error_code {
        let error = unsafe { smithril_z3_sys::Z3_get_error_code(self.holder.0) };
        if error != smithril_z3_sys::Z3_OK {
            let error_msg = unsafe {
                CStr::from_ptr(smithril_z3_sys::Z3_get_error_msg(self.holder.0, error))
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
            smithril_z3_sys::Z3_solver_interrupt(self.holder.0, self.holder.1);
            self.check_error();
        }
    }
}

pub struct Z3Factory {
    contexts: HashSet<Rc<Z3Converter>>,
    solvers: HashSet<Rc<Z3Solver>>,
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
        unsafe { smithril_z3_sys::Z3_params_dec_ref(self.context.context(), self.options) };
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
                self.options,
                param_symbol,
                val,
            );
        }
    }

    fn get_produce_unsat_core(&self) -> bool {
        let res = unsafe {
            let param_str =
                smithril_z3_sys::Z3_params_to_string(self.context.context(), self.options);
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

impl GeneralFactory<Z3Sort, Z3Term, Z3Options, Z3Converter, Z3Solver, Z3Interrupter> for Z3Factory {
    fn new_context(&mut self) -> Rc<Z3Converter> {
        let context = Rc::new(Z3Converter::default());
        self.contexts.insert(context.clone());
        context
    }

    fn new_solver(&mut self, context: Rc<Z3Converter>) -> Rc<Z3Solver> {
        let solver = Rc::new(Z3Solver::new(context.clone(), &Options::default()));
        self.solvers.insert(solver.clone());
        solver
    }

    fn delete_context(&mut self, context: Rc<Z3Converter>) {
        self.contexts.remove(&context);
        assert_eq!(Rc::strong_count(&context), 1);
    }

    fn delete_solver(&mut self, solver: Rc<Z3Solver>) {
        self.solvers.remove(&solver);
        assert_eq!(Rc::strong_count(&solver), 1);
    }

    fn new_interrupter(&self, solver: Rc<Z3Solver>) -> Z3Interrupter {
        Z3Interrupter {
            holder: Z3Holder(solver.context.context(), solver.solver),
        }
    }

    fn new_solver_with_options(
        &mut self,
        context: Rc<Z3Converter>,
        options: &Options,
    ) -> Rc<Z3Solver> {
        let solver = Rc::new(Z3Solver::new(context, options));
        self.solvers.insert(solver.clone());
        solver
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Z3Term {
    pub term: smithril_z3_sys::Z3_ast,
}

impl Z3Term {
    pub fn new(context: &Z3Context, term: smithril_z3_sys::Z3_ast) -> Self {
        context.check_error();
        Self { term }
    }
}

pub struct Z3Sort {
    pub sort: smithril_z3_sys::Z3_sort,
}

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
    pub solver: smithril_z3_sys::Z3_solver,
    pub context: Rc<Z3Converter>,
    pub asserted_terms_map: Cell<HashMap<Z3Term, Term>>,
    pub unsat_map: Cell<HashMap<Z3Term, Z3Term>>,
}

impl PartialEq for Z3Solver {
    fn eq(&self, other: &Self) -> bool {
        self.options.eq(&other.options) && self.solver.eq(&other.solver)
    }
}

impl Eq for Z3Solver {}

impl Hash for Z3Solver {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.options.hash(state);
        self.solver.hash(state)
    }
}

impl Z3Solver {
    pub fn new(context: Rc<Z3Converter>, options: &Options) -> Self {
        let options = Z3Options::from((context.clone(), options));
        let solver = unsafe {
            let native_solver = smithril_z3_sys::Z3_mk_solver(context.context());
            smithril_z3_sys::Z3_solver_inc_ref(context.context(), native_solver);
            smithril_z3_sys::Z3_solver_set_params(
                context.context(),
                native_solver,
                options.options,
            );
            native_solver
        };

        Self {
            options,
            solver,
            context,
            asserted_terms_map: Cell::new(HashMap::new()),
            unsat_map: Cell::new(HashMap::new()),
        }
    }
}

pub struct Z3Converter {
    pub context: Z3Context,
}

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

unsafe impl Send for Z3Converter {}
unsafe impl Sync for Z3Converter {}

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
            smithril_z3_sys::Z3_solver_dec_ref(self.context.context(), self.solver);
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

impl GeneralUnsatCoreSolver<Z3Sort, Z3Term, Z3Converter> for Z3Solver {
    fn unsat_core(&self) -> Vec<Z3Term> {
        let context = self.context.as_ref();
        let u_core =
            unsafe { smithril_z3_sys::Z3_solver_get_unsat_core(context.context(), self.solver) };
        let mut res: Vec<Z3Term> = Vec::new();
        let cur_unsat_map = self.unsat_map.take();
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
}

impl GeneralSolver<Z3Sort, Z3Term, Z3Options, Z3Converter> for Z3Solver {
    fn assert(&self, term: &Z3Term) {
        if self.options.get_produce_unsat_core() {
            unsafe {
                let mut cur_unsat_map = self.unsat_map.take();
                let cur_str = "sym".to_owned() + cur_unsat_map.len().to_string().as_str();
                let track_term = self
                    .context
                    .mk_smt_symbol(cur_str.as_str(), &self.context.mk_bool_sort());
                smithril_z3_sys::Z3_solver_assert_and_track(
                    self.context.context(),
                    self.solver,
                    term.term,
                    track_term.term,
                );
                self.context.context.check_error();
                cur_unsat_map.insert(track_term, term.clone());
                self.unsat_map.set(cur_unsat_map);
            }
        } else {
            unsafe {
                smithril_z3_sys::Z3_solver_assert(self.context.context(), self.solver, term.term);
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
                smithril_z3_sys::Z3_solver_get_model(context.context(), self.solver),
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
            smithril_z3_sys::Z3_solver_reset(context.context(), self.solver);
            context.context.check_error();
        }
    }

    fn interrupt(&self) {
        let context = self.context.as_ref();
        unsafe {
            smithril_z3_sys::Z3_solver_interrupt(context.context(), self.solver);
            context.context.check_error();
        }
    }

    fn check_sat(&self) -> SolverResult {
        let context = self.context.as_ref();
        let res = unsafe { smithril_z3_sys::Z3_solver_check(context.context(), self.solver) };
        context.context.check_error();
        match res {
            smithril_z3_sys::Z3_L_TRUE => SolverResult::Sat,
            smithril_z3_sys::Z3_L_FALSE => SolverResult::Unsat,
            _ => SolverResult::Unknown,
        }
    }
}

impl GeneralConverter<Z3Sort, Z3Term> for Z3Converter {
    fn mk_bv_sort(&self, size: u64) -> Z3Sort {
        Z3Sort::new(&self.context, unsafe {
            smithril_z3_sys::Z3_mk_bv_sort(self.context(), size as u32)
        })
    }

    fn mk_bool_sort(&self) -> Z3Sort {
        Z3Sort::new(&self.context, unsafe {
            smithril_z3_sys::Z3_mk_bool_sort(self.context())
        })
    }

    fn mk_bv_value_uint64(&self, sort: &Z3Sort, val: u64) -> Z3Term {
        Z3Term::new(&self.context, unsafe {
            smithril_z3_sys::Z3_mk_unsigned_int64(self.context(), val, sort.sort)
        })
    }

    fn mk_bvnxor(&self, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
        self.mk_not(&self.mk_xor(term1, term2))
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

    fn mk_smt_symbol(&self, name: &str, sort: &Z3Sort) -> Z3Term {
        let name_cstr = CString::new(name).unwrap();
        let term = unsafe {
            let symbol = smithril_z3_sys::Z3_mk_string_symbol(self.context(), name_cstr.as_ptr());
            smithril_z3_sys::Z3_mk_const(self.context(), symbol, sort.sort)
        };
        Z3Term::new(&self.context, term)
    }

    fn mk_array_sort(&self, index: &Z3Sort, element: &Z3Sort) -> Z3Sort {
        let i = index.sort;
        let e = element.sort;
        Z3Sort::new(&self.context, unsafe {
            smithril_z3_sys::Z3_mk_array_sort(self.context(), i, e)
        })
    }

    create_converter_binary_function_z3!(mk_eq, Z3_mk_eq);
    create_converter_binary_function_z3!(mk_bvadd, Z3_mk_bvadd);
    create_converter_binary_function_z3!(mk_bvand, Z3_mk_bvand);
    create_converter_binary_function_z3!(mk_bvashr, Z3_mk_bvashr);
    create_converter_binary_function_z3!(mk_bvlshr, Z3_mk_bvlshr);
    create_converter_binary_function_z3!(mk_bvmul, Z3_mk_bvmul);
    create_converter_binary_function_z3!(mk_bvnand, Z3_mk_bvnand);
    create_converter_unary_function_z3!(mk_bvneg, Z3_mk_bvneg);
    create_converter_binary_function_z3!(mk_bvnor, Z3_mk_bvnor);
    create_converter_unary_function_z3!(mk_bvnot, Z3_mk_bvnot);
    create_converter_binary_function_z3!(mk_bvor, Z3_mk_bvor);
    create_converter_binary_function_z3!(mk_bvsdiv, Z3_mk_bvsdiv);
    create_converter_binary_function_z3!(mk_bvsge, Z3_mk_bvsge);
    create_converter_binary_function_z3!(mk_bvsgt, Z3_mk_bvsgt);
    create_converter_binary_function_z3!(mk_bvshl, Z3_mk_bvshl);
    create_converter_binary_function_z3!(mk_bvsle, Z3_mk_bvsle);
    create_converter_binary_function_z3!(mk_bvslt, Z3_mk_bvslt);
    create_converter_binary_function_z3!(mk_bvsmod, Z3_mk_bvsmod);
    create_converter_binary_function_z3!(mk_bvsub, Z3_mk_bvsub);
    create_converter_binary_function_z3!(mk_bvudiv, Z3_mk_bvudiv);
    create_converter_binary_function_z3!(mk_bvuge, Z3_mk_bvuge);
    create_converter_binary_function_z3!(mk_bvugt, Z3_mk_bvugt);
    create_converter_binary_function_z3!(mk_bvule, Z3_mk_bvule);
    create_converter_binary_function_z3!(mk_bvult, Z3_mk_bvult);
    create_converter_binary_function_z3!(mk_bvumod, Z3_mk_bvurem);
    create_converter_binary_function_z3!(mk_bvxor, Z3_mk_bvxor);
    create_converter_binary_function_z3_narg!(mk_neq, Z3_mk_distinct);
    create_converter_binary_function_z3_narg!(mk_and, Z3_mk_and);
    create_converter_binary_function_z3_narg!(mk_or, Z3_mk_or);
    create_converter_binary_function_z3!(mk_implies, Z3_mk_implies);
    create_converter_unary_function_z3!(mk_not, Z3_mk_not);
    create_converter_binary_function_z3!(mk_xor, Z3_mk_xor);
    create_converter_binary_function_z3!(mk_select, Z3_mk_select);
    create_converter_ternary_function_z3!(mk_store, Z3_mk_store);
}

impl UnsatCoreSolver for Z3Solver {
    fn unsat_core(&self) -> Vec<Term> {
        let u_core_z3 = GeneralUnsatCoreSolver::unsat_core(self);
        let mut u_core: Vec<Term> = Vec::new();
        for cur_term in u_core_z3 {
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

impl Solver for Z3Solver {
    fn assert(&self, term: &crate::generalized::Term) {
        let context = self.context.as_ref();
        let cur_z3_term = context.convert_term(term);
        GeneralSolver::assert(self, &cur_z3_term);
        let mut cur_asserted_terms_map = self.asserted_terms_map.take();
        cur_asserted_terms_map.insert(cur_z3_term, term.clone());
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
        }
    }

    fn reset(&self) {
        GeneralSolver::reset(self)
    }
}
