use crate::generalized::GeneralConverter;
use crate::generalized::GeneralSort;
use crate::generalized::GeneralTerm;
use crate::generalized::SolverResult;
use std::cell::Cell;
use std::collections::HashMap;
use std::ffi::CString;

pub struct BitwuzlaTerm {
    pub term: smithril_bitwuzla_sys::BitwuzlaTerm,
}

pub struct BitwuzlaSort {
    pub sort: smithril_bitwuzla_sys::BitwuzlaSort,
}

impl GeneralSort for BitwuzlaSort {}

impl GeneralTerm for BitwuzlaTerm {}

pub struct BitwuzlaConverter {
    pub term_manager: *mut smithril_bitwuzla_sys::BitwuzlaTermManager,
    pub options: *mut smithril_bitwuzla_sys::BitwuzlaOptions,
    pub solver: *mut smithril_bitwuzla_sys::Bitwuzla,
    pub tmp: Cell<HashMap<String, BitwuzlaTerm>>,
}

impl BitwuzlaConverter {
    pub fn new() -> Self {
        let term_manager = unsafe { smithril_bitwuzla_sys::bitwuzla_term_manager_new() };
        let options = unsafe { smithril_bitwuzla_sys::bitwuzla_options_new() };

        let cadical_cstr = CString::new("cadical").unwrap();
        unsafe {
            smithril_bitwuzla_sys::bitwuzla_set_option(
                options,
                smithril_bitwuzla_sys::BITWUZLA_OPT_PRODUCE_MODELS,
                1,
            );
            smithril_bitwuzla_sys::bitwuzla_set_option_mode(
                options,
                smithril_bitwuzla_sys::BITWUZLA_OPT_SAT_SOLVER,
                cadical_cstr.as_ptr(),
            )
        };
        let solver = unsafe { smithril_bitwuzla_sys::bitwuzla_new(term_manager, options) };
        Self {
            term_manager,
            options,
            solver,
            tmp: Cell::new(HashMap::new()),
        }
    }
}

impl Default for BitwuzlaConverter {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for BitwuzlaConverter {
    fn drop(&mut self) {
        unsafe {
            smithril_bitwuzla_sys::bitwuzla_delete(self.solver);
            smithril_bitwuzla_sys::bitwuzla_options_delete(self.options);
            smithril_bitwuzla_sys::bitwuzla_term_manager_delete(self.term_manager);
        };
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
                        self.term_manager,
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
                        self.term_manager,
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
                        self.term_manager,
                        smithril_bitwuzla_sys::$bitwuzla_sys_kind_name,
                        term.term,
                    )
                },
            }
        }
    };
}

impl<'tm> GeneralConverter<'tm, BitwuzlaSort, BitwuzlaTerm> for BitwuzlaConverter {
    fn mk_smt_symbol(&'tm self, name: &str, sort: &BitwuzlaSort) -> BitwuzlaTerm {
        let mut sym_table = self.tmp.take();
        let term = if let Some(term2) = sym_table.get(name) {
            term2.term
        } else {
            let name_cstr = CString::new(name).unwrap();
            let term = unsafe {
                smithril_bitwuzla_sys::bitwuzla_mk_const(
                    self.term_manager,
                    sort.sort,
                    name_cstr.as_ptr(),
                )
            };
            let old_term = sym_table.insert(name.to_string(), BitwuzlaTerm { term });
            assert!(old_term.is_none());
            term
        };
        self.tmp.set(sym_table);
        BitwuzlaTerm { term }
    }

    fn assert(&self, term: &BitwuzlaTerm) {
        unsafe { smithril_bitwuzla_sys::bitwuzla_assert(self.solver, term.term) }
    }

    create_converter_binary_function_bitwuzla!(mk_eq, BITWUZLA_KIND_EQUAL);

    fn check_sat(&self) -> SolverResult {
        let res = unsafe { smithril_bitwuzla_sys::bitwuzla_check_sat(self.solver) };
        match res {
            smithril_bitwuzla_sys::BITWUZLA_SAT => SolverResult::Sat,
            smithril_bitwuzla_sys::BITWUZLA_UNSAT => SolverResult::Unsat,
            _ => SolverResult::Unknown,
        }
    }

    fn mk_bv_sort(&self, size: u64) -> BitwuzlaSort {
        BitwuzlaSort {
            sort: unsafe {
                smithril_bitwuzla_sys::bitwuzla_mk_bv_sort(self.term_manager, size as u64)
            },
        }
    }

    fn mk_bool_sort(&'tm self) -> BitwuzlaSort {
        BitwuzlaSort {
            sort: unsafe { smithril_bitwuzla_sys::bitwuzla_mk_bool_sort(self.term_manager) },
        }
    }

    fn mk_array_sort(&'tm self, index: &BitwuzlaSort, element: &BitwuzlaSort) -> BitwuzlaSort {
        let i = index.sort;
        let e = element.sort;
        BitwuzlaSort {
            sort: unsafe { smithril_bitwuzla_sys::bitwuzla_mk_array_sort(self.term_manager, i, e) },
        }
    }

    fn mk_bv_value_uint64(&self, sort: &BitwuzlaSort, val: u64) -> BitwuzlaTerm {
        BitwuzlaTerm {
            term: unsafe {
                smithril_bitwuzla_sys::bitwuzla_mk_bv_value_uint64(
                    self.term_manager,
                    sort.sort,
                    val,
                )
            },
        }
    }

    fn mk_smt_bool(&self, val: bool) -> BitwuzlaTerm {
        let term = unsafe {
            match val {
                true => smithril_bitwuzla_sys::bitwuzla_mk_true(self.term_manager),
                false => smithril_bitwuzla_sys::bitwuzla_mk_false(self.term_manager),
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
