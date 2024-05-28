pub mod bitwuzla_sys;

use core::fmt;
use std::collections::BTreeMap;
use std::ffi::{c_char, CStr, CString};

pub struct BitwuzlaTerm {
    pub term: bitwuzla_sys::BitwuzlaTerm,
}

pub struct BitwuzlaSort {
    pub sort: bitwuzla_sys::BitwuzlaSort,
}

pub trait GeneralSort {}

pub trait GeneralTerm {}

impl GeneralSort for BitwuzlaSort {}

impl GeneralTerm for BitwuzlaTerm {}

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

pub trait GeneralConvertor<S: GeneralSort, T: GeneralTerm> {
    fn mk_smt_symbol(&self, name: &str, sort: &S) -> T;
    fn assert(&self, term: &T);
    fn mk_eq(&self, term1: &T, term2: &T) -> T;
    fn check_sat(&self) -> SolverResult;
    fn mk_bv_sort(&self, size: u64) -> S;
    fn mk_bv_value_uint64(&self, sort: &S, val: u64) -> T;
    fn mk_bv_zero(&self, sort: &S) -> T;
    fn mk_bv_one(&self, sort: &S) -> T;
    fn mk_bv_ones(&self, sort: &S) -> T;
    fn mk_true(&self) -> T;
    fn mk_false(&self) -> T;
    fn mk_term1(&self, arg0: &T) -> T;
    fn mk_term2(&self, arg0: &T, arg1: &T) -> T;
    fn mk_term3(&self, arg0: &T, arg1: &T, arg2: &T) -> T;
    fn mk_term(&self, argc: &u32, args: *mut T) -> T;
    // fn convert(&self, term: &Term, sort: &Sort) -> T;
}

pub trait GeneralOption {}

pub struct BitwuzlaConvertor {
    pub term_manager: *mut bitwuzla_sys::BitwuzlaTermManager,
    pub options: *mut bitwuzla_sys::BitwuzlaOptions,
    pub solver: *mut bitwuzla_sys::Bitwuzla,
}

impl BitwuzlaConvertor {
    pub fn new() -> Self {
        let term_manager = unsafe { bitwuzla_sys::bitwuzla_term_manager_new() };
        let options = unsafe { bitwuzla_sys::bitwuzla_options_new() };

        let cadical_cstr = CString::new("cadical").unwrap();
        unsafe {
            bitwuzla_sys::bitwuzla_set_option(
                options,
                bitwuzla_sys::BitwuzlaOption_BITWUZLA_OPT_PRODUCE_MODELS,
                1,
            );
            bitwuzla_sys::bitwuzla_set_option_mode(
                options,
                bitwuzla_sys::BitwuzlaOption_BITWUZLA_OPT_SAT_SOLVER,
                cadical_cstr.as_ptr() as *const i8,
            )
        };
        let solver = unsafe { bitwuzla_sys::bitwuzla_new(term_manager, options) };
        Self {
            term_manager,
            options,
            solver,
        }
    }
}

impl Default for BitwuzlaConvertor {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for BitwuzlaConvertor {
    fn drop(&mut self) {
        unsafe {
            bitwuzla_sys::bitwuzla_delete(self.solver);
            bitwuzla_sys::bitwuzla_options_delete(self.options);
            bitwuzla_sys::bitwuzla_term_manager_delete(self.term_manager);
        };
    }
}

impl GeneralConvertor<BitwuzlaSort, BitwuzlaTerm> for BitwuzlaConvertor {
    fn mk_smt_symbol(&self, name: &str, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        let name_cstr = CString::new(name).unwrap();
        let term = unsafe {
            bitwuzla_sys::bitwuzla_mk_const(
                self.term_manager,
                sort.sort,
                name_cstr.as_ptr() as *const i8,
            )
        };
        BitwuzlaTerm { term }
    }

    fn assert(&self, term: &BitwuzlaTerm) {
        unsafe { bitwuzla_sys::bitwuzla_assert(self.solver, term.term) }
    }

    fn mk_eq(&self, term1: &BitwuzlaTerm, term2: &BitwuzlaTerm) -> BitwuzlaTerm {
        let res = BitwuzlaTerm {
            term: unsafe {
                bitwuzla_sys::bitwuzla_mk_term2(
                    self.term_manager,
                    bitwuzla_sys::BitwuzlaKind_BITWUZLA_KIND_EQUAL,
                    term1.term,
                    term2.term,
                )
            },
        };
        res
    }

    fn check_sat(&self) -> SolverResult {
        let res = unsafe { bitwuzla_sys::bitwuzla_check_sat(self.solver) };
        match res {
            bitwuzla_sys::BitwuzlaResult_BITWUZLA_SAT => SolverResult::Sat,
            bitwuzla_sys::BitwuzlaResult_BITWUZLA_UNSAT => SolverResult::Unsat,
            _ => SolverResult::Unknown,
        }
    }

    fn mk_bv_sort(&self, size: u64) -> BitwuzlaSort {
        let res = BitwuzlaSort {
            sort: unsafe { bitwuzla_sys::bitwuzla_mk_bv_sort(self.term_manager, size) },
        };
        res
    }

    fn mk_bv_value_uint64(&self, sort: &BitwuzlaSort, val: u64) -> BitwuzlaTerm {
        let res = BitwuzlaTerm {
            term: unsafe {
                bitwuzla_sys::bitwuzla_mk_bv_value_uint64(self.term_manager, sort.sort, val)
            },
        };
        res
    }

    fn mk_bv_zero(&self, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        let res = BitwuzlaTerm {
            term: unsafe { bitwuzla_sys::bitwuzla_mk_bv_zero(self.term_manager, sort.sort) },
        };
        res
    }

    fn mk_bv_one(&self, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        let res = BitwuzlaTerm {
            term: unsafe { bitwuzla_sys::bitwuzla_mk_bv_one(self.term_manager, sort.sort) },
        };
        res
    }

    fn mk_bv_ones(&self, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        let res = BitwuzlaTerm {
            term: unsafe { bitwuzla_sys::bitwuzla_mk_bv_ones(self.term_manager, sort.sort) },
        };
        res
    }

    fn mk_true(&self) -> BitwuzlaTerm {
        let res = BitwuzlaTerm {
            term: unsafe { bitwuzla_sys::bitwuzla_mk_true(self.term_manager) },
        };
        res
    }

    fn mk_false(&self) -> BitwuzlaTerm {
        let res = BitwuzlaTerm {
            term: unsafe { bitwuzla_sys::bitwuzla_mk_false(self.term_manager) },
        };
        res
    }

    fn mk_term1(&self, arg0: &BitwuzlaTerm) -> BitwuzlaTerm {
        let res = BitwuzlaTerm {
            term: unsafe { bitwuzla_sys::bitwuzla_mk_term1(self.term_manager, 1, arg0.term) },
        };
        res
    }

    fn mk_term2(&self, arg0: &BitwuzlaTerm, arg1: &BitwuzlaTerm) -> BitwuzlaTerm {
        let res = BitwuzlaTerm {
            term: unsafe {
                bitwuzla_sys::bitwuzla_mk_term2(self.term_manager, 1, arg0.term, arg1.term)
            },
        };
        res
    }

    fn mk_term3(
        &self,
        arg0: &BitwuzlaTerm,
        arg1: &BitwuzlaTerm,
        arg2: &BitwuzlaTerm,
    ) -> BitwuzlaTerm {
        let res = BitwuzlaTerm {
            term: unsafe {
                bitwuzla_sys::bitwuzla_mk_term3(
                    self.term_manager,
                    4,
                    arg0.term,
                    arg1.term,
                    arg2.term,
                )
            },
        };
        res
    }

    fn mk_term(&self, argc: u32, args: *mut BitwuzlaTerm) -> BitwuzlaTerm {
        let cur_args: *mut BitwuzlaTerm;
        for i in 0..argc - 1 {
            unsafe { cur_args.add(args[i].term) };
            cur_args.
        }
        let res = BitwuzlaTerm {
            term: unsafe { bitwuzla_sys::bitwuzla_mk_term(self.term_manager, 1, argc, cur_args) },
        };
        res
    }
}
