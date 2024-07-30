use crate::generalized::GenConstant;
use crate::generalized::GeneralConverter;
use crate::generalized::GeneralSolver;
use crate::generalized::GeneralSolver;
use crate::generalized::GeneralSort;
use crate::generalized::GeneralTerm;
use crate::generalized::GeneralUnsatCoreConverter;
use crate::generalized::GeneralUnsatCoreSolver;
use crate::generalized::SolverResult;
use crate::generalized::Sort;
use crate::generalized::Term;
use crate::generalized::UnsortedTerm;
use crate::utils;
use core::panic;
use std::borrow::Borrow;
use std::cell::Cell;
use std::collections::HashMap;
use std::ffi::CStr;
use std::ffi::CString;
use std::ptr;
use std::rc::Rc;

#[derive(PartialEq, Eq, Hash)]
pub struct Z3ContextInner {
    pub context: smithril_z3_sys::Z3_context,
}

impl Default for Z3ContextInner {
    fn default() -> Self {
        Z3ContextInner {
            context: unsafe {
                let cfg = smithril_z3_sys::Z3_mk_config();
                let ctx = smithril_z3_sys::Z3_mk_context_rc(cfg);
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
}

impl Z3ContextInner {
    pub fn new() -> Self {
        Self::default()
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

impl Drop for Z3ContextInner {
    fn drop(&mut self) {
        unsafe {
            smithril_z3_sys::Z3_del_context(self.context);
        };
    }
}
#[derive(PartialEq, Eq, Hash)]
pub struct Z3Term {
    pub context: Rc<Z3Context>,
    pub term: smithril_z3_sys::Z3_ast,
}

impl Z3Term {
    pub fn new(context: Rc<Z3Context>, term: smithril_z3_sys::Z3_ast) -> Self {
        unsafe {
            smithril_z3_sys::Z3_inc_ref(context.context(), term);
        }
        Self { term, context }
    }

    fn check_error(self) -> Self {
        self.context.check_error();
        self
    }
}

impl Drop for Z3Term {
    fn drop(&mut self) {
        unsafe {
            smithril_z3_sys::Z3_dec_ref(self.context.context(), self.term);
        };
    }
}

pub struct Z3Sort {
    pub context: Rc<Z3Context>,
    pub sort: smithril_z3_sys::Z3_sort,
}

impl Z3Sort {
    pub fn new(context: Rc<Z3Context>, sort: smithril_z3_sys::Z3_sort) -> Self {
        unsafe {
            smithril_z3_sys::Z3_inc_ref(context.context(), Self::to_ast(context.context(), sort));
        }
        Self { sort, context }
    }

    fn check_error(self) -> Self {
        self.context.check_error();
        self
    }

    fn to_ast(
        context: smithril_z3_sys::Z3_context,
        sort: smithril_z3_sys::Z3_sort,
    ) -> smithril_z3_sys::Z3_ast {
        unsafe { smithril_z3_sys::Z3_sort_to_ast(context, sort) }
    }
}

impl Drop for Z3Sort {
    fn drop(&mut self) {
        unsafe {
            smithril_z3_sys::Z3_dec_ref(
                self.context.context(),
                Self::to_ast(self.context.context(), self.sort),
            );
        };
    }
}

impl GeneralSort for Z3Sort {}

impl GeneralTerm for Z3Term {}

#[derive(PartialEq, Eq, Hash)]
pub enum Z3Context {
    Ref(Rc<Z3ContextInner>),
    Val(Z3ContextInner),
}

impl Default for Z3Context {
    fn default() -> Self {
        Z3Context::Val(Z3ContextInner::new())
    }
}

impl Z3Context {
    fn new(context: Rc<Z3ContextInner>) -> Self {
        Z3Context::Ref(context)
    }
    fn context(&self) -> smithril_z3_sys::Z3_context {
        match self {
            Z3Context::Ref(context) => context.context,
            Z3Context::Val(context) => context.context,
        }
    }
    fn check_error(&self) -> smithril_z3_sys::Z3_error_code {
        match self {
            Z3Context::Ref(context) => context.check_error(),
            Z3Context::Val(context) => context.check_error(),
        }
    }
}

pub struct Z3Converter {
    pub context: Rc<Z3Context>,
    pub params: smithril_z3_sys::Z3_params,
    pub solver: smithril_z3_sys::Z3_solver,
    pub asserted_terms_map: Cell<HashMap<Z3Term, Term>>,
}

impl Z3Converter {
    pub fn new(context: Rc<Z3ContextInner>) -> Self {
        let context = Rc::new(Z3Context::new(context));
        let params = unsafe {
            let solver_parameters = smithril_z3_sys::Z3_mk_params(context.context());
            smithril_z3_sys::Z3_params_inc_ref(context.context(), solver_parameters);
            solver_parameters
        };

        let solver = unsafe {
            let native_solver = smithril_z3_sys::Z3_mk_solver(context.context());
            smithril_z3_sys::Z3_solver_inc_ref(context.context(), native_solver);
            smithril_z3_sys::Z3_solver_set_params(context.context(), native_solver, params);
            native_solver
        };

        Self {
            context,
            params,
            solver,
            asserted_terms_map: Cell::new(HashMap::new()),
        }
    }
}

impl Default for Z3Converter {
    fn default() -> Self {
        let context = Rc::new(Z3Context::default());
        let params = unsafe {
            let solver_parameters = smithril_z3_sys::Z3_mk_params(context.context());
            smithril_z3_sys::Z3_params_inc_ref(context.context(), solver_parameters);
            solver_parameters
        };

        let solver = unsafe {
            let native_solver = smithril_z3_sys::Z3_mk_solver(context.context());
            smithril_z3_sys::Z3_solver_inc_ref(context.context(), native_solver);
            smithril_z3_sys::Z3_solver_set_params(context.context(), native_solver, params);
            native_solver
        };

        Self {
            context,
            params,
            solver,
            asserted_terms_map: Cell::new(HashMap::new()),
        }
    }
}

impl Drop for Z3Converter {
    fn drop(&mut self) {
        unsafe {
            smithril_z3_sys::Z3_solver_dec_ref(self.context.context(), self.solver);
            smithril_z3_sys::Z3_params_dec_ref(self.context.context(), self.params);
            smithril_z3_sys::Z3_params_dec_ref(self.context.context(), self.params);
        };
    }
}

impl Z3Converter {}

macro_rules! create_converter_binary_function_z3_narg {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
            Z3Term::new(self.context.clone(), unsafe {
                let args = vec![term1.term, term2.term];
                smithril_z3_sys::$z3_sys_func_name(self.context.context(), 2, args.as_ptr())
            })
            .check_error()
        }
    };
}

macro_rules! create_converter_unary_function_z3 {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, term: &Z3Term) -> Z3Term {
            Z3Term::new(self.context.clone(), unsafe {
                smithril_z3_sys::$z3_sys_func_name(self.context.context(), term.term)
            })
            .check_error()
        }
    };
}

macro_rules! create_converter_binary_function_z3 {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
            Z3Term::new(self.context.clone(), unsafe {
                smithril_z3_sys::$z3_sys_func_name(self.context.context(), term1.term, term2.term)
            })
            .check_error()
        }
    };
}

macro_rules! create_converter_ternary_function_z3 {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, term1: &Z3Term, term2: &Z3Term, term3: &Z3Term) -> Z3Term {
            Z3Term::new(self.context.clone(), unsafe {
                smithril_z3_sys::$z3_sys_func_name(
                    self.context.context(),
                    term1.term,
                    term2.term,
                    term3.term,
                )
            })
            .check_error()
        }
    };
}

impl GeneralUnsatCoreConverter<Z3Sort, Z3Term> for Z3Converter {
    fn unsat_core(&self) -> Vec<Z3Term> {
        let u_core = unsafe {
            smithril_z3_sys::Z3_solver_get_unsat_core(self.context.context(), self.solver)
        };
        let mut res: Vec<Z3Term> = Vec::new();
        let size = unsafe { smithril_z3_sys::Z3_ast_vector_size(self.context.context(), u_core) };
        for i in 0..size {
            let cur_item =
                unsafe { smithril_z3_sys::Z3_ast_vector_get(self.context.context(), u_core, i) };
            res.push(Z3Term {
                context: self.context.clone(),
                term: cur_item,
            })
        }
        res
    }
}

impl GeneralConverter<Z3Sort, Z3Term> for Z3Converter {
    fn assert(&self, term: &Z3Term) {
        unsafe {
            smithril_z3_sys::Z3_solver_assert(self.context.context(), self.solver, term.term);
            self.context.check_error();
        }
    }

    fn check_sat(&self) -> SolverResult {
        let res = unsafe { smithril_z3_sys::Z3_solver_check(self.context.context(), self.solver) };
        self.context.check_error();
        match res {
            smithril_z3_sys::Z3_L_TRUE => SolverResult::Sat,
            smithril_z3_sys::Z3_L_FALSE => SolverResult::Unsat,
            _ => SolverResult::Unknown,
        }
    }

    fn mk_bv_sort(&self, size: u64) -> Z3Sort {
        Z3Sort::new(self.context.clone(), unsafe {
            smithril_z3_sys::Z3_mk_bv_sort(self.context.context(), size as u32)
        })
        .check_error()
    }

    // fn eval(&self, term1: &Z3Term) -> Option<Z3Term> {
    //     let mut r: smithril_z3_sys::Z3_ast = ptr::null_mut();
    //     let model_completion = false;
    //     let t = term1.term;
    //     let status = unsafe {
    //         smithril_z3_sys::Z3_inc_ref(self.context.context(), t);
    //         let status = smithril_z3_sys::Z3_model_eval(
    //             self.context.context(),
    //             smithril_z3_sys::Z3_solver_get_model(self.context.context(), self.solver),
    //             t,
    //             model_completion,
    //             &mut r,
    //         );
    //         println!("{} bsbsbs", status);
    //         smithril_z3_sys::Z3_dec_ref(self.context.context(), t);
    //         status
    //     };
    //     if status {
    //         let res = Z3Term::new(self.context.clone(), r);
    //         Some(res)
    //     } else {
    //         None
    //     }
    // }

    fn mk_bool_sort(&self) -> Z3Sort {
        Z3Sort::new(self.context.clone(), unsafe {
            smithril_z3_sys::Z3_mk_bool_sort(self.context.context())
        })
        .check_error()
    }

    fn mk_bv_value_uint64(&self, sort: &Z3Sort, val: u64) -> Z3Term {
        Z3Term::new(self.context.clone(), unsafe {
            smithril_z3_sys::Z3_mk_unsigned_int64(self.context.context(), val, sort.sort)
        })
        .check_error()
    }

    fn mk_bvnxor(&self, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
        self.mk_not(&self.mk_xor(term1, term2))
    }

    fn mk_smt_bool(&self, val: bool) -> Z3Term {
        let term = unsafe {
            if val {
                smithril_z3_sys::Z3_mk_true(self.context.context())
            } else {
                smithril_z3_sys::Z3_mk_false(self.context.context())
            }
        };
        Z3Term::new(self.context.clone(), term).check_error()
    }

    fn mk_smt_symbol(&self, name: &str, sort: &Z3Sort) -> Z3Term {
        let name_cstr = CString::new(name).unwrap();
        let term = unsafe {
            let symbol =
                smithril_z3_sys::Z3_mk_string_symbol(self.context.context(), name_cstr.as_ptr());
            smithril_z3_sys::Z3_mk_const(self.context.context(), symbol, sort.sort)
        };
        Z3Term::new(self.context.clone(), term).check_error()
    }

    fn mk_array_sort(&self, index: &Z3Sort, element: &Z3Sort) -> Z3Sort {
        let i = index.sort;
        let e = element.sort;
        Z3Sort::new(self.context.clone(), unsafe {
            smithril_z3_sys::Z3_mk_array_sort(self.context.context(), i, e)
        })
        .check_error()
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

impl GeneralUnsatCoreSolver for Z3Converter {
    fn unsat_core(&self) -> Vec<Term> {
        let u_core_z3 = GeneralUnsatCoreConverter::unsat_core(self);
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

impl GeneralSolver for Z3Converter {
    fn assert(&self, term: &crate::generalized::Term) {
        let cur_z3_term = self.convert_term(term);
        GeneralConverter::assert(self, &cur_z3_term);
        let mut cur_asserted_terms_map = self.asserted_terms_map.take();
        cur_asserted_terms_map.insert(cur_z3_term, term.clone());
        self.asserted_terms_map.set(cur_asserted_terms_map);
    }

    fn check_sat(&self) -> SolverResult {
        GeneralConverter::check_sat(self)
    }

    // fn eval(&self, term: &Term) -> Option<Term> {
    //     let expr = GeneralConverter::eval(self, &self.convert_term(term))?;
    //     match term.sort {
    //         Sort::BvSort(_) => {
    //             let z3_string: *const i8 = unsafe {
    //                 smithril_z3_sys::Z3_get_numeral_binary_string(self.context.context(), expr.term)
    //             };
    //             let s = unsafe { CStr::from_ptr(z3_string).to_string_lossy().into_owned() };
    //             let bv_const = utils::binary2integer(s);
    //             let res = Term {
    //                 term: UnsortedTerm::Constant(GenConstant::Numeral(bv_const)),
    //                 sort: term.sort.clone(),
    //             };
    //             // mixa117 binary2integer (битовые операции в расте, сдвиги, только ансайнд случай)
    //             // mixa117 cstr помогает с consti8 -> string
    //             // mixa117 тест
    //             // mixa117 bin2int пренести в новый utils.rs
    //             Some(res)
    //         }
    //         Sort::BoolSort() => {
    //             let z3_lbool = unsafe {
    //                 smithril_z3_sys::Z3_get_bool_value(self.context.context(), expr.term)
    //             };
    //             match z3_lbool {
    //                 smithril_z3_sys::Z3_L_FALSE => {
    //                     let res = Term {
    //                         term: UnsortedTerm::Constant(GenConstant::Boolean(false)),
    //                         sort: term.sort.clone(),
    //                     };
    //                     Some(res)
    //                 }
    //                 smithril_z3_sys::Z3_L_TRUE => {
    //                     let res = Term {
    //                         term: UnsortedTerm::Constant(GenConstant::Boolean(true)),
    //                         sort: term.sort.clone(),
    //                     };
    //                     Some(res)
    //                 }
    //                 _ => {
    //                     panic!("Can't get boolean value from Z3")
    //                 }
    //             }
    //         }
    //         Sort::ArraySort(_, _) => panic!("Unexpected sort"),
    //     }
    // }
}
