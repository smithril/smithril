use crate::generalized::GeneralConverter;
use crate::generalized::GeneralSolver;
use crate::generalized::GeneralSort;
use crate::generalized::GeneralTerm;
use crate::generalized::SolverResult;
use core::panic;
use std::ffi::CStr;
use std::ffi::CString;

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
pub struct Z3Term<'a> {
    pub context: &'a Z3Context<'a>,
    pub term: smithril_z3_sys::Z3_ast,
}

impl<'a> Z3Term<'a> {
    pub fn new(context: &'a Z3Context<'a>, term: smithril_z3_sys::Z3_ast) -> Self {
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

impl<'a> Drop for Z3Term<'a> {
    fn drop(&mut self) {
        unsafe {
            smithril_z3_sys::Z3_dec_ref(self.context.context(), self.term);
        };
    }
}

pub struct Z3Sort<'a> {
    pub context: &'a Z3Context<'a>,
    pub sort: smithril_z3_sys::Z3_sort,
}

impl<'a> Z3Sort<'a> {
    pub fn new(context: &'a Z3Context, sort: smithril_z3_sys::Z3_sort) -> Self {
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

impl<'a> Drop for Z3Sort<'a> {
    fn drop(&mut self) {
        unsafe {
            smithril_z3_sys::Z3_dec_ref(
                self.context.context(),
                Self::to_ast(self.context.context(), self.sort),
            );
        };
    }
}

impl<'a> GeneralSort for Z3Sort<'a> {}

impl<'a> GeneralTerm for Z3Term<'a> {}

pub enum Z3Context<'a> {
    Ref(&'a Z3ContextInner),
    Val(Z3ContextInner),
}

impl<'a> Default for Z3Context<'a> {
    fn default() -> Self {
        Z3Context::Val(Z3ContextInner::new())
    }
}

impl<'a> Z3Context<'a> {
    fn new(context: &'a Z3ContextInner) -> Self {
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

pub struct Z3Converter<'ctx> {
    pub context: Z3Context<'ctx>,
    pub params: smithril_z3_sys::Z3_params,
    pub solver: smithril_z3_sys::Z3_solver,
}

impl<'ctx> Z3Converter<'ctx> {
    pub fn new(context: &'ctx Z3ContextInner) -> Self {
        let context = Z3Context::new(context);
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
        }
    }
}

impl<'ctx> Default for Z3Converter<'ctx> {
    fn default() -> Self {
        let context = Z3Context::default();
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
        }
    }
}

impl<'ctx> Drop for Z3Converter<'ctx> {
    fn drop(&mut self) {
        unsafe {
            smithril_z3_sys::Z3_solver_dec_ref(self.context.context(), self.solver);
            smithril_z3_sys::Z3_params_dec_ref(self.context.context(), self.params);
            smithril_z3_sys::Z3_params_dec_ref(self.context.context(), self.params);
        };
    }
}

impl<'ctx> Z3Converter<'ctx> {}

macro_rules! create_converter_binary_function_z3_narg {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
            Z3Term::new(&self.context, unsafe {
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
            Z3Term::new(&self.context, unsafe {
                smithril_z3_sys::$z3_sys_func_name(self.context.context(), term.term)
            })
            .check_error()
        }
    };
}

macro_rules! create_converter_binary_function_z3 {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
            Z3Term::new(&self.context, unsafe {
                smithril_z3_sys::$z3_sys_func_name(self.context.context(), term1.term, term2.term)
            })
            .check_error()
        }
    };
}

macro_rules! create_converter_ternary_function_z3 {
    ($func_name:ident, $z3_sys_func_name:ident) => {
        fn $func_name(&self, term1: &Z3Term, term2: &Z3Term, term3: &Z3Term) -> Z3Term {
            Z3Term::new(&self.context, unsafe {
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

impl<'ctx> GeneralConverter<'ctx, Z3Sort<'ctx>, Z3Term<'ctx>> for Z3Converter<'ctx> {
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

    fn mk_bv_sort(&'ctx self, size: u64) -> Z3Sort<'ctx> {
        Z3Sort::new(&self.context, unsafe {
            smithril_z3_sys::Z3_mk_bv_sort(self.context.context(), size as u32)
        })
        .check_error()
    }

    fn mk_bool_sort(&'ctx self) -> Z3Sort<'ctx> {
        Z3Sort::new(&self.context, unsafe {
            smithril_z3_sys::Z3_mk_bool_sort(self.context.context())
        })
        .check_error()
    }

    fn mk_bv_value_uint64(&self, sort: &Z3Sort, val: u64) -> Z3Term {
        Z3Term::new(&self.context, unsafe {
            smithril_z3_sys::Z3_mk_unsigned_int64(self.context.context(), val, sort.sort)
        })
        .check_error()
    }

    fn mk_bvnxor(&'ctx self, term1: &Z3Term<'ctx>, term2: &Z3Term<'ctx>) -> Z3Term<'ctx> {
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
        Z3Term::new(&self.context, term).check_error()
    }

    fn mk_smt_symbol(&'ctx self, name: &str, sort: &Z3Sort) -> Z3Term<'ctx> {
        let name_cstr = CString::new(name).unwrap();
        let term = unsafe {
            let symbol =
                smithril_z3_sys::Z3_mk_string_symbol(self.context.context(), name_cstr.as_ptr());
            smithril_z3_sys::Z3_mk_const(self.context.context(), symbol, sort.sort)
        };
        Z3Term::new(&self.context, term).check_error()
    }

    fn mk_array_sort(&'ctx self, index: &Z3Sort, element: &Z3Sort) -> Z3Sort<'ctx> {
        let i = index.sort;
        let e = element.sort;
        Z3Sort::new(&self.context, unsafe {
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

impl<'ctx> GeneralSolver for Z3Converter<'ctx> {
    fn assert(&self, term: &crate::generalized::Term) {
        GeneralConverter::assert(self, &self.convert_term(term));
    }

    fn check_sat(&self) -> SolverResult {
        GeneralConverter::check_sat(self)
    }
}