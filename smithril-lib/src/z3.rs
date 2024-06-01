use crate::generalized::GeneralConvertor;
use crate::generalized::GeneralSort;
use crate::generalized::GeneralTerm;
use crate::generalized::SolverResult;
use core::panic;
use std::ffi::CStr;
use std::ffi::CString;

pub struct Z3Context {
    pub context: smithril_z3_sys::Z3_context,
}

impl Z3Context {
    pub fn new() -> Z3Context {
        Z3Context {
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

impl Drop for Z3Context {
    fn drop(&mut self) {
        unsafe {
            smithril_z3_sys::Z3_del_context(self.context);
        };
    }
}
pub struct Z3Term<'a> {
    pub context: &'a Z3Context,
    pub term: smithril_z3_sys::Z3_ast,
}

impl<'a> Z3Term<'a> {
    pub fn new(context: &'a Z3Context, term: smithril_z3_sys::Z3_ast) -> Self {
        unsafe {
            smithril_z3_sys::Z3_inc_ref(context.context, term);
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
            smithril_z3_sys::Z3_dec_ref(self.context.context, self.term);
        };
    }
}

pub struct Z3Sort<'a> {
    pub context: &'a Z3Context,
    pub sort: smithril_z3_sys::Z3_sort,
}

impl<'a> Z3Sort<'a> {
    pub fn new(context: &'a Z3Context, sort: smithril_z3_sys::Z3_sort) -> Self {
        unsafe {
            smithril_z3_sys::Z3_inc_ref(context.context, Self::to_ast(context.context, sort));
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
                self.context.context,
                Self::to_ast(self.context.context, self.sort),
            );
        };
    }
}

impl<'a> GeneralSort for Z3Sort<'a> {}

impl<'a> GeneralTerm for Z3Term<'a> {}

pub struct Z3Convertor {
    pub context: Z3Context,
    pub params: smithril_z3_sys::Z3_params,
    pub solver: smithril_z3_sys::Z3_solver,
}

impl Z3Convertor {
    pub fn new() -> Self {
        let context = Z3Context::new();
        let params = unsafe {
            let solver_parameters = smithril_z3_sys::Z3_mk_params(context.context);
            smithril_z3_sys::Z3_params_inc_ref(context.context, solver_parameters);
            solver_parameters
        };

        let solver = unsafe {
            let native_solver = smithril_z3_sys::Z3_mk_solver(context.context);
            smithril_z3_sys::Z3_solver_inc_ref(context.context, native_solver);
            smithril_z3_sys::Z3_solver_set_params(context.context, native_solver, params);
            native_solver
        };

        Self {
            context,
            params,
            solver,
        }
    }
}

impl Default for Z3Convertor {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for Z3Convertor {
    fn drop(&mut self) {
        unsafe {
            smithril_z3_sys::Z3_solver_dec_ref(self.context.context, self.solver);
            smithril_z3_sys::Z3_params_dec_ref(self.context.context, self.params);
            smithril_z3_sys::Z3_params_dec_ref(self.context.context, self.params);
        };
    }
}

impl Z3Convertor {}

impl<'ctx> GeneralConvertor<'ctx, Z3Sort<'ctx>, Z3Term<'ctx>> for Z3Convertor {
    fn mk_smt_symbol(&'ctx self, name: &str, sort: &Z3Sort) -> Z3Term<'ctx> {
        let name_cstr = CString::new(name).unwrap();
        let term = unsafe {
            let symbol =
                smithril_z3_sys::Z3_mk_string_symbol(self.context.context, name_cstr.as_ptr());
            smithril_z3_sys::Z3_mk_const(self.context.context, symbol, sort.sort)
        };
        Z3Term::new(&self.context, term).check_error()
    }

    fn assert(&self, term: &Z3Term) {
        unsafe {
            smithril_z3_sys::Z3_solver_assert(self.context.context, self.solver, term.term);
            self.context.check_error();
        }
    }

    fn mk_eq(&self, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
        Z3Term::new(&self.context, unsafe {
            smithril_z3_sys::Z3_mk_eq(self.context.context, term1.term, term2.term)
        })
        .check_error()
    }

    fn check_sat(&self) -> SolverResult {
        let res = unsafe { smithril_z3_sys::Z3_solver_check(self.context.context, self.solver) };
        self.context.check_error();
        match res {
            smithril_z3_sys::Z3_L_TRUE => SolverResult::Sat,
            smithril_z3_sys::Z3_L_FALSE => SolverResult::Unsat,
            _ => SolverResult::Unknown,
        }
    }

    fn mk_bv_sort(&'ctx self, size: u64) -> Z3Sort<'ctx> {
        Z3Sort::new(&self.context, unsafe {
            smithril_z3_sys::Z3_mk_bv_sort(self.context.context, size as u32)
        })
        .check_error()
    }

    fn mk_bv_value_uint64(&self, sort: &Z3Sort, val: u64) -> Z3Term {
        Z3Term::new(&self.context, unsafe {
            smithril_z3_sys::Z3_mk_unsigned_int64(self.context.context, val, sort.sort)
        })
        .check_error()
    }

    fn mk_smt_bool(&self, val: bool) -> Z3Term {
        let term = unsafe {
            if val {
                smithril_z3_sys::Z3_mk_true(self.context.context)
            } else {
                smithril_z3_sys::Z3_mk_false(self.context.context)
            }
        };
        Z3Term::new(&self.context, term).check_error()
    }
}
