use crate::generalized::GeneralConvertor;
use crate::generalized::GeneralSort;
use crate::generalized::GeneralTerm;
use crate::generalized::SolverResult;
use core::panic;
use std::ffi::CStr;
use std::ffi::CString;

pub struct Z3Term {
    pub term: smithril_z3_sys::Z3_ast,
}

pub struct Z3Sort {
    pub sort: smithril_z3_sys::Z3_sort,
}

impl GeneralSort for Z3Sort {}

impl GeneralTerm for Z3Term {}

pub struct Z3Convertor {
    pub context: smithril_z3_sys::Z3_context,
    pub params: smithril_z3_sys::Z3_params,
    pub solver: smithril_z3_sys::Z3_solver,
}

impl Z3Convertor {
    pub fn new() -> Self {
        let context = unsafe {
            let cfg = smithril_z3_sys::Z3_mk_config();
            let ctx = smithril_z3_sys::Z3_mk_context(cfg);
            smithril_z3_sys::Z3_set_ast_print_mode(
                ctx,
                smithril_z3_sys::Z3_PRINT_SMTLIB2_COMPLIANT,
            );
            smithril_z3_sys::Z3_del_config(cfg);
            ctx
        };

        let params = unsafe {
            let solver_parameters = smithril_z3_sys::Z3_mk_params(context);
            smithril_z3_sys::Z3_params_inc_ref(context, solver_parameters);
            solver_parameters
        };

        let solver = unsafe {
            let native_solver = smithril_z3_sys::Z3_mk_solver(context);
            smithril_z3_sys::Z3_solver_inc_ref(context, native_solver);
            smithril_z3_sys::Z3_solver_set_params(context, native_solver, params);
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
            smithril_z3_sys::Z3_solver_dec_ref(self.context, self.solver);
            smithril_z3_sys::Z3_params_dec_ref(self.context, self.params);
            smithril_z3_sys::Z3_params_dec_ref(self.context, self.params);
        };
    }
}

impl Z3Convertor {
    unsafe fn check_error(&self) -> smithril_z3_sys::Z3_error_code {
        let error = smithril_z3_sys::Z3_get_error_code(self.context);
        if error != smithril_z3_sys::Z3_OK {
            let error_msg = CStr::from_ptr(smithril_z3_sys::Z3_get_error_msg(self.context, error))
                .to_str()
                .unwrap();
            panic!("{}", error_msg);
        }
        error
    }

    unsafe fn check_term(&self, term: smithril_z3_sys::Z3_ast) -> smithril_z3_sys::Z3_ast {
        self.check_error();
        term
    }
}

impl GeneralConvertor<Z3Sort, Z3Term> for Z3Convertor {
    fn mk_smt_symbol(&self, name: &str, sort: &Z3Sort) -> Z3Term {
        let name_cstr = CString::new(name).unwrap();
        let term = unsafe {
            let symbol = smithril_z3_sys::Z3_mk_string_symbol(self.context, name_cstr.as_ptr());
            self.check_term(smithril_z3_sys::Z3_mk_const(
                self.context,
                symbol,
                sort.sort,
            ))
        };
        Z3Term { term }
    }

    fn assert(&self, term: &Z3Term) {
        unsafe {
            smithril_z3_sys::Z3_solver_assert(self.context, self.solver, term.term);
            self.check_error();
        }
    }

    fn mk_eq(&self, term1: &Z3Term, term2: &Z3Term) -> Z3Term {
        Z3Term {
            term: unsafe {
                let res = smithril_z3_sys::Z3_mk_eq(self.context, term1.term, term2.term);
                self.check_error();
                res
            },
        }
    }

    fn check_sat(&self) -> SolverResult {
        let res = unsafe {
            let res = smithril_z3_sys::Z3_solver_check(self.context, self.solver);
            self.check_error();
            res
        };
        match res {
            smithril_z3_sys::Z3_L_TRUE => SolverResult::Sat,
            smithril_z3_sys::Z3_L_FALSE => SolverResult::Unsat,
            _ => SolverResult::Unknown,
        }
    }

    fn mk_bv_sort(&self, size: u64) -> Z3Sort {
        Z3Sort {
            sort: unsafe {
                let res = smithril_z3_sys::Z3_mk_bv_sort(self.context, size as u32);
                self.check_error();
                res
            },
        }
    }

    fn mk_bv_value_uint64(&self, sort: &Z3Sort, val: u64) -> Z3Term {
        Z3Term {
            term: unsafe {
                let res = smithril_z3_sys::Z3_mk_unsigned_int64(self.context, val, sort.sort);
                self.check_error();
                res
            },
        }
    }

    fn mk_smt_bool(&self, val: bool) -> Z3Term {
        let term = unsafe {
            if val {
                smithril_z3_sys::Z3_mk_true(self.context)
            } else {
                smithril_z3_sys::Z3_mk_false(self.context)
            }
        };
        Z3Term { term }
    }
}
