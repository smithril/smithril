use crate::generalized::GeneralConvertor;
use crate::generalized::GeneralSort;
use crate::generalized::GeneralTerm;
use crate::generalized::SolverResult;
use std::ffi::CString;

pub struct BitwuzlaTerm {
    pub term: smitril_bitwuzla_sys::BitwuzlaTerm,
}

pub struct BitwuzlaSort {
    pub sort: smitril_bitwuzla_sys::BitwuzlaSort,
}

impl GeneralSort for BitwuzlaSort {}

impl GeneralTerm for BitwuzlaTerm {}

pub struct BitwuzlaConvertor {
    pub term_manager: *mut smitril_bitwuzla_sys::BitwuzlaTermManager,
    pub options: *mut smitril_bitwuzla_sys::BitwuzlaOptions,
    pub solver: *mut smitril_bitwuzla_sys::Bitwuzla,
}

impl BitwuzlaConvertor {
    pub fn new() -> Self {
        let term_manager = unsafe { smitril_bitwuzla_sys::bitwuzla_term_manager_new() };
        let options = unsafe { smitril_bitwuzla_sys::bitwuzla_options_new() };

        let cadical_cstr = CString::new("cadical").unwrap();
        unsafe {
            smitril_bitwuzla_sys::bitwuzla_set_option(
                options,
                smitril_bitwuzla_sys::BITWUZLA_OPT_PRODUCE_MODELS,
                1,
            );
            smitril_bitwuzla_sys::bitwuzla_set_option_mode(
                options,
                smitril_bitwuzla_sys::BITWUZLA_OPT_SAT_SOLVER,
                cadical_cstr.as_ptr(),
            )
        };
        let solver = unsafe { smitril_bitwuzla_sys::bitwuzla_new(term_manager, options) };
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
            smitril_bitwuzla_sys::bitwuzla_delete(self.solver);
            smitril_bitwuzla_sys::bitwuzla_options_delete(self.options);
            smitril_bitwuzla_sys::bitwuzla_term_manager_delete(self.term_manager);
        };
    }
}

impl BitwuzlaConvertor {}

impl GeneralConvertor<BitwuzlaSort, BitwuzlaTerm> for BitwuzlaConvertor {
    fn mk_smt_symbol(&self, name: &str, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        let name_cstr = CString::new(name).unwrap();
        let term = unsafe {
            smitril_bitwuzla_sys::bitwuzla_mk_const(
                self.term_manager,
                sort.sort,
                name_cstr.as_ptr(),
            )
        };
        BitwuzlaTerm { term }
    }

    fn assert(&self, term: &BitwuzlaTerm) {
        unsafe { smitril_bitwuzla_sys::bitwuzla_assert(self.solver, term.term) }
    }

    fn mk_eq(&self, term1: &BitwuzlaTerm, term2: &BitwuzlaTerm) -> BitwuzlaTerm {
        BitwuzlaTerm {
            term: unsafe {
                smitril_bitwuzla_sys::bitwuzla_mk_term2(
                    self.term_manager,
                    smitril_bitwuzla_sys::BITWUZLA_KIND_EQUAL,
                    term1.term,
                    term2.term,
                )
            },
        }
    }

    fn check_sat(&self) -> SolverResult {
        let res = unsafe { smitril_bitwuzla_sys::bitwuzla_check_sat(self.solver) };
        match res {
            smitril_bitwuzla_sys::BITWUZLA_SAT => SolverResult::Sat,
            smitril_bitwuzla_sys::BITWUZLA_UNSAT => SolverResult::Unsat,
            _ => SolverResult::Unknown,
        }
    }

    fn mk_bv_sort(&self, size: u64) -> BitwuzlaSort {
        BitwuzlaSort {
            sort: unsafe { smitril_bitwuzla_sys::bitwuzla_mk_bv_sort(self.term_manager, size) },
        }
    }

    fn mk_bv_value_uint64(&self, sort: &BitwuzlaSort, val: u64) -> BitwuzlaTerm {
        BitwuzlaTerm {
            term: unsafe {
                smitril_bitwuzla_sys::bitwuzla_mk_bv_value_uint64(self.term_manager, sort.sort, val)
            },
        }
    }

    fn mk_bv_zero(&self, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        BitwuzlaTerm {
            term: unsafe {
                smitril_bitwuzla_sys::bitwuzla_mk_bv_zero(self.term_manager, sort.sort)
            },
        }
    }

    fn mk_bv_one(&self, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        BitwuzlaTerm {
            term: unsafe { smitril_bitwuzla_sys::bitwuzla_mk_bv_one(self.term_manager, sort.sort) },
        }
    }

    fn mk_bv_ones(&self, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        BitwuzlaTerm {
            term: unsafe {
                smitril_bitwuzla_sys::bitwuzla_mk_bv_ones(self.term_manager, sort.sort)
            },
        }
    }

    fn mk_true(&self) -> BitwuzlaTerm {
        BitwuzlaTerm {
            term: unsafe { smitril_bitwuzla_sys::bitwuzla_mk_true(self.term_manager) },
        }
    }

    fn mk_false(&self) -> BitwuzlaTerm {
        BitwuzlaTerm {
            term: unsafe { smitril_bitwuzla_sys::bitwuzla_mk_false(self.term_manager) },
        }
    }
}
