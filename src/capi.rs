#![allow(clippy::missing_safety_doc)]

use std::{
    collections::{HashMap, HashSet},
    ffi::{c_char, c_void, CStr, CString},
    ptr::null,
    sync::{Arc, RwLock},
    time::Duration,
};

use crate::{
    generalized::Options,
    term::{self, Sort, SortKind, Term},
};
use crate::{
    generalized::{AsyncFactory, AsyncSolver},
    solver,
};
use duration_string::DurationString;

pub use crate::generalized::SolverResult;
pub use crate::term::RoundingMode;

use crate::converters::Converter;
use once_cell::sync::Lazy;
use tokio::runtime::{self, Runtime};

static RUNTIME: Lazy<Runtime> = Lazy::new(|| {
    runtime::Builder::new_multi_thread()
        .worker_threads(4)
        .enable_io()
        .build()
        .unwrap()
});

static FACTORY: Lazy<RwLock<solver::SmithrilFactory>> = Lazy::new(|| {
    RwLock::new({
        RUNTIME.block_on(solver::SmithrilFactory::new(vec![
            Converter::Z3,
            Converter::Bitwuzla,
        ]))
    })
});

type Terms = HashMap<Arc<solver::SmithrilContext>, HashSet<Arc<Term>>>;
type Sorts = HashMap<Arc<solver::SmithrilContext>, HashSet<Arc<Sort>>>;
type Symbols = HashMap<Arc<solver::SmithrilContext>, HashSet<String>>;

struct LockingOptions {
    options: RwLock<Options>,
}

impl PartialEq for LockingOptions {
    fn eq(&self, other: &Self) -> bool {
        *self.options.read().unwrap() == *other.options.read().unwrap()
    }
}

impl Eq for LockingOptions {}

static SOLVERS: Lazy<RwLock<HashSet<Arc<solver::SmithrilSolver>>>> =
    Lazy::new(|| RwLock::new(HashSet::new()));
static CONTEXTS: Lazy<RwLock<HashSet<Arc<solver::SmithrilContext>>>> =
    Lazy::new(|| RwLock::new(HashSet::new()));
static OPTIONS: Lazy<RwLock<Vec<Arc<LockingOptions>>>> = Lazy::new(|| RwLock::new(Vec::new()));
static TERMS: Lazy<RwLock<Terms>> = Lazy::new(|| RwLock::new(HashMap::new()));
static SORTS: Lazy<RwLock<Sorts>> = Lazy::new(|| RwLock::new(HashMap::new()));
static SYMBOLS: Lazy<RwLock<Symbols>> = Lazy::new(|| RwLock::new(HashMap::new()));
static LAST_EVALUATED_TERM: Lazy<RwLock<Arc<CString>>> = Lazy::new(|| RwLock::new(Arc::default()));
static LAST_UNSAT_CORE: Lazy<RwLock<Arc<Vec<Term>>>> = Lazy::new(|| RwLock::new(Arc::default()));
static FRESH_SYMBOLS_COUNT: Lazy<RwLock<u64>> = Lazy::new(|| RwLock::new(1));

#[repr(C)]
pub struct SmithrilSolver(*const c_void);

#[repr(C)]
pub struct SmithrilContext(*const c_void);

#[repr(C)]
pub struct SmithrilOptions(*const c_void);

#[repr(C)]
pub struct SmithrilSort(*const c_void);

#[repr(C)]
pub struct SmithrilTerm(*const c_void);

#[repr(C)]
pub struct SmithrilTermVector(*const c_void);

fn intern_sort(smithril_context: Arc<solver::SmithrilContext>, sort: Arc<Sort>) -> Arc<Sort> {
    let mut lock = SORTS.write().unwrap();
    let sorts = lock.entry(smithril_context.clone()).or_default();
    match sorts.get(&sort) {
        Some(sort) => sort.clone(),
        None => {
            sorts.insert(sort.clone());
            sort
        }
    }
}

fn intern_term(smithril_context: Arc<solver::SmithrilContext>, term: Arc<Term>) -> Arc<Term> {
    let mut lock = TERMS.write().unwrap();
    let terms = lock.entry(smithril_context.clone()).or_default();
    match terms.get(&term) {
        Some(term) => term.clone(),
        None => {
            terms.insert(term.clone());
            term
        }
    }
}

fn is_symbol_used(smithril_context: Arc<solver::SmithrilContext>, name: &str) -> bool {
    let mut lock = SYMBOLS.write().unwrap();
    let symbols = lock.entry(smithril_context.clone()).or_default();
    symbols.contains(name)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_get_sort(
    context: SmithrilContext,
    term: SmithrilTerm,
) -> SmithrilSort {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    let term = term.0 as *const Term;
    Arc::increment_strong_count(term);
    let smithril_term = Arc::from_raw(term);
    let sort = Arc::new(smithril_term.get_sort());
    let sort = intern_sort(smithril_context, sort);
    let sort = Arc::into_raw(sort);
    Arc::decrement_strong_count(sort);
    SmithrilSort(sort as *const c_void)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_get_sort_kind(sort: SmithrilSort) -> SortKind {
    let sort = sort.0 as *const Sort;
    Arc::increment_strong_count(sort);
    let smithril_sort = Arc::from_raw(sort);
    smithril_sort.get_kind()
}

#[no_mangle]
pub unsafe extern "C" fn smithril_get_bv_sort_size(sort: SmithrilSort) -> u64 {
    let sort = sort.0 as *const Sort;
    Arc::increment_strong_count(sort);
    let smithril_sort = Arc::from_raw(sort);
    smithril_sort.try_get_bv_sort_size().unwrap_or_default()
}

#[no_mangle]
pub unsafe extern "C" fn smithril_fp_get_bv_exp_size(term: SmithrilTerm) -> u64 {
    let term = term.0 as *const Term;
    Arc::increment_strong_count(term);
    let smithril_term = Arc::from_raw(term);
    smithril_term
        .sort
        .try_fp_get_bv_exp_size()
        .unwrap_or_default()
}

#[no_mangle]
pub unsafe extern "C" fn smithril_fp_get_bv_sig_size(term: SmithrilTerm) -> u64 {
    let term = term.0 as *const Term;
    Arc::increment_strong_count(term);
    let smithril_term = Arc::from_raw(term);
    smithril_term
        .sort
        .try_fp_get_bv_sig_size()
        .unwrap_or_default()
}

#[no_mangle]
pub unsafe extern "C" fn smithril_mk_bv_sort(context: SmithrilContext, size: u64) -> SmithrilSort {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    let sort = Arc::new(term::mk_bv_sort(size));
    let sort = intern_sort(smithril_context, sort);
    let sort = Arc::into_raw(sort);
    Arc::decrement_strong_count(sort);
    SmithrilSort(sort as *const c_void)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_mk_array_sort(
    context: SmithrilContext,
    index_sort: SmithrilSort,
    elem_sort: SmithrilSort,
) -> SmithrilSort {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    let index_sort = index_sort.0 as *const Sort;
    Arc::increment_strong_count(index_sort);
    let smithril_index_sort = Arc::from_raw(index_sort);
    let elem_sort = elem_sort.0 as *const Sort;
    Arc::increment_strong_count(elem_sort);
    let smithril_elem_sort = Arc::from_raw(elem_sort);
    let sort = Arc::new(term::mk_array_sort(
        &smithril_index_sort,
        &smithril_elem_sort,
    ));
    let sort = intern_sort(smithril_context, sort);
    let sort = Arc::into_raw(sort);
    Arc::decrement_strong_count(sort);
    SmithrilSort(sort as *const c_void)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_mk_bool_sort(context: SmithrilContext) -> SmithrilSort {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    let sort = Arc::new(term::mk_bool_sort());
    let sort = intern_sort(smithril_context, sort);
    let sort = Arc::into_raw(sort);
    Arc::decrement_strong_count(sort);
    SmithrilSort(sort as *const c_void)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_mk_bv_value_uint64(
    context: SmithrilContext,
    sort: SmithrilSort,
    val: u64,
) -> SmithrilTerm {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    let sort = sort.0 as *const Sort;
    Arc::increment_strong_count(sort);
    let smithril_sort = Arc::from_raw(sort);
    let term = Arc::new(term::mk_bv_value_uint64(val, &smithril_sort));
    let term = intern_term(smithril_context, term);
    let term = Arc::into_raw(term);
    Arc::decrement_strong_count(term);
    SmithrilTerm(term as *const c_void)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_mk_smt_bool(context: SmithrilContext, val: bool) -> SmithrilTerm {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    let term = Arc::new(term::mk_smt_bool(val));
    let term = intern_term(smithril_context, term);
    let term = Arc::into_raw(term);
    Arc::decrement_strong_count(term);
    SmithrilTerm(term as *const c_void)
}

pub unsafe fn smithril_mk_smt_symbol_inner(
    context: SmithrilContext,
    name: &str,
    sort: SmithrilSort,
) -> SmithrilTerm {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    {
        let mut lock = SYMBOLS.write().unwrap();
        let symbols = lock.entry(smithril_context.clone()).or_default();
        symbols.insert(name.to_string());
    }
    let sort = sort.0 as *const Sort;
    Arc::increment_strong_count(sort);
    let smithril_sort = Arc::from_raw(sort);
    let term = Arc::new(term::mk_smt_symbol(name, &smithril_sort));
    let term = intern_term(smithril_context, term);
    let term = Arc::into_raw(term);
    Arc::decrement_strong_count(term);
    SmithrilTerm(term as *const c_void)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_mk_smt_symbol(
    context: SmithrilContext,
    name: *const c_char,
    sort: SmithrilSort,
) -> SmithrilTerm {
    let name = unsafe { CStr::from_ptr(name).to_string_lossy().into_owned() };
    smithril_mk_smt_symbol_inner(context, &name, sort)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_mk_fresh_smt_symbol(
    context: SmithrilContext,
    sort: SmithrilSort,
) -> SmithrilTerm {
    let mut name = "fresh".to_string();
    {
        let context = context.0 as *const solver::SmithrilContext;
        Arc::increment_strong_count(context);
        let smithril_context = Arc::from_raw(context);
        let mut count = { *FRESH_SYMBOLS_COUNT.read().unwrap() };
        while is_symbol_used(smithril_context.clone(), &name) {
            name = format!("{}{}", name, count);
            count += 1;
        }
        *FRESH_SYMBOLS_COUNT.write().unwrap() = count;
    }
    smithril_mk_smt_symbol_inner(context, &name, sort)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_mk_smt_const_symbol(
    context: SmithrilContext,
    term: SmithrilTerm,
    sort: SmithrilSort,
) -> SmithrilTerm {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    let term = term.0 as *const Term;
    Arc::increment_strong_count(term);
    let smithril_term = Arc::from_raw(term);
    let sort = sort.0 as *const Sort;
    Arc::increment_strong_count(sort);
    let smithril_sort = Arc::from_raw(sort);
    let term = Arc::new(term::mk_smt_const_symbol(&smithril_term, &smithril_sort));
    let term = intern_term(smithril_context, term);
    let term = Arc::into_raw(term);
    Arc::decrement_strong_count(term);
    SmithrilTerm(term as *const c_void)
}

macro_rules! unary_function {
    ($smithril_func_name:ident, $func_name:ident) => {
        #[no_mangle]
        pub unsafe extern "C" fn $smithril_func_name(
            context: SmithrilContext,
            term1: SmithrilTerm,
        ) -> SmithrilTerm {
            let context = context.0 as *const solver::SmithrilContext;
            Arc::increment_strong_count(context);
            let smithril_context = Arc::from_raw(context);
            let term1 = term1.0 as *const Term;
            Arc::increment_strong_count(term1);
            let smithril_term1 = Arc::from_raw(term1);
            let term = Arc::new(term::$func_name(smithril_term1.as_ref()));
            let term = intern_term(smithril_context, term);
            let term = Arc::into_raw(term);
            Arc::decrement_strong_count(term);
            SmithrilTerm(term as *const c_void)
        }
    };
}

macro_rules! binary_function {
    ($smithril_func_name:ident, $func_name:ident) => {
        #[no_mangle]
        pub unsafe extern "C" fn $smithril_func_name(
            context: SmithrilContext,
            term1: SmithrilTerm,
            term2: SmithrilTerm,
        ) -> SmithrilTerm {
            let context = context.0 as *const solver::SmithrilContext;
            Arc::increment_strong_count(context);
            let smithril_context = Arc::from_raw(context);
            let term1 = term1.0 as *const Term;
            Arc::increment_strong_count(term1);
            let smithril_term1 = Arc::from_raw(term1);
            let term2 = term2.0 as *const Term;
            Arc::increment_strong_count(term2);
            let smithril_term2 = Arc::from_raw(term2);
            let term = Arc::new(term::$func_name(
                smithril_term1.as_ref(),
                smithril_term2.as_ref(),
            ));
            let term = intern_term(smithril_context, term);
            let term = Arc::into_raw(term);
            Arc::decrement_strong_count(term);
            SmithrilTerm(term as *const c_void)
        }
    };
}

macro_rules! ternary_function {
    ($smithril_func_name:ident, $func_name:ident) => {
        #[no_mangle]
        pub unsafe extern "C" fn $smithril_func_name(
            context: SmithrilContext,
            term1: SmithrilTerm,
            term2: SmithrilTerm,
            term3: SmithrilTerm,
        ) -> SmithrilTerm {
            let context = context.0 as *const solver::SmithrilContext;
            Arc::increment_strong_count(context);
            let smithril_context = Arc::from_raw(context);
            let term1 = term1.0 as *const Term;
            Arc::increment_strong_count(term1);
            let smithril_term1 = Arc::from_raw(term1);
            let term2 = term2.0 as *const Term;
            Arc::increment_strong_count(term2);
            let smithril_term2 = Arc::from_raw(term2);
            let term3 = term3.0 as *const Term;
            Arc::increment_strong_count(term3);
            let smithril_term3 = Arc::from_raw(term3);
            let term = Arc::new(term::$func_name(
                smithril_term1.as_ref(),
                smithril_term2.as_ref(),
                smithril_term3.as_ref(),
            ));
            let term = intern_term(smithril_context, term);
            let term = Arc::into_raw(term);
            Arc::decrement_strong_count(term);
            SmithrilTerm(term as *const c_void)
        }
    };
}

macro_rules! rm_unary_function {
    ($smithril_func_name:ident, $func_name:ident) => {
        #[no_mangle]
        pub unsafe extern "C" fn $smithril_func_name(
            context: SmithrilContext,
            r_mode: RoundingMode,
            term1: SmithrilTerm,
        ) -> SmithrilTerm {
            let context = context.0 as *const solver::SmithrilContext;
            Arc::increment_strong_count(context);
            let smithril_context = Arc::from_raw(context);
            let term1 = term1.0 as *const Term;
            Arc::increment_strong_count(term1);
            let smithril_term1 = Arc::from_raw(term1);
            let term = Arc::new(term::$func_name(&r_mode, smithril_term1.as_ref()));
            let term = intern_term(smithril_context, term);
            let term = Arc::into_raw(term);
            Arc::decrement_strong_count(term);
            SmithrilTerm(term as *const c_void)
        }
    };
}

macro_rules! rm_binary_function {
    ($smithril_func_name:ident, $func_name:ident) => {
        #[no_mangle]
        pub unsafe extern "C" fn $smithril_func_name(
            context: SmithrilContext,
            r_mode: RoundingMode,
            term1: SmithrilTerm,
            term2: SmithrilTerm,
        ) -> SmithrilTerm {
            let context = context.0 as *const solver::SmithrilContext;
            Arc::increment_strong_count(context);
            let smithril_context = Arc::from_raw(context);
            let term1 = term1.0 as *const Term;
            Arc::increment_strong_count(term1);
            let smithril_term1 = Arc::from_raw(term1);
            let term2 = term2.0 as *const Term;
            Arc::increment_strong_count(term2);
            let smithril_term2 = Arc::from_raw(term2);
            let term = Arc::new(term::$func_name(
                &r_mode,
                smithril_term1.as_ref(),
                smithril_term2.as_ref(),
            ));
            let term = intern_term(smithril_context, term);
            let term = Arc::into_raw(term);
            Arc::decrement_strong_count(term);
            SmithrilTerm(term as *const c_void)
        }
    };
}

macro_rules! fp_to_function {
    ($smithril_func_name:ident, $func_name:ident) => {
        #[no_mangle]
        pub unsafe extern "C" fn $smithril_func_name(
            context: SmithrilContext,
            r_mode: RoundingMode,
            term1: SmithrilTerm,
            w: u64,
        ) -> SmithrilTerm {
            let context = context.0 as *const solver::SmithrilContext;
            Arc::increment_strong_count(context);
            let smithril_context = Arc::from_raw(context);
            let term1 = term1.0 as *const Term;
            Arc::increment_strong_count(term1);
            let smithril_term1 = Arc::from_raw(term1);
            let term = Arc::new(term::$func_name(&r_mode, smithril_term1.as_ref(), w));
            let term = intern_term(smithril_context, term);
            let term = Arc::into_raw(term);
            Arc::decrement_strong_count(term);
            SmithrilTerm(term as *const c_void)
        }
    };
}

macro_rules! fp_to_fp_function {
    ($smithril_func_name:ident, $func_name:ident) => {
        #[no_mangle]
        pub unsafe extern "C" fn $smithril_func_name(
            context: SmithrilContext,
            r_mode: RoundingMode,
            term1: SmithrilTerm,
            ew: u64,
            sw: u64,
        ) -> SmithrilTerm {
            let context = context.0 as *const solver::SmithrilContext;
            Arc::increment_strong_count(context);
            let smithril_context = Arc::from_raw(context);
            let term1 = term1.0 as *const Term;
            Arc::increment_strong_count(term1);
            let smithril_term1 = Arc::from_raw(term1);
            let term = Arc::new(term::$func_name(&r_mode, smithril_term1.as_ref(), ew, sw));
            let term = intern_term(smithril_context, term);
            let term = Arc::into_raw(term);
            Arc::decrement_strong_count(term);
            SmithrilTerm(term as *const c_void)
        }
    };
}

binary_function!(smithril_mk_and, mk_and);
binary_function!(smithril_mk_bvadd, mk_bv_add);
binary_function!(smithril_mk_or, mk_or);
binary_function!(smithril_mk_eq, mk_eq);
binary_function!(smithril_mk_implies, mk_implies);
binary_function!(smithril_mk_neq, mk_neq);
binary_function!(smithril_mk_xor, mk_xor);
binary_function!(smithril_mk_iff, mk_iff);
binary_function!(smithril_mk_bvand, mk_bv_and);
binary_function!(smithril_mk_bvashr, mk_bv_ashr);
binary_function!(smithril_mk_bvlshr, mk_bv_lshr);
binary_function!(smithril_mk_bvmul, mk_bv_mul);
binary_function!(smithril_mk_bvnand, mk_bv_nand);
unary_function!(smithril_mk_bvneg, mk_bv_neg);
binary_function!(smithril_mk_bvnor, mk_bv_nor);
unary_function!(smithril_mk_bvnot, mk_bv_not);
binary_function!(smithril_mk_bvnxor, mk_bv_nxor);
binary_function!(smithril_mk_bvor, mk_bv_or);
binary_function!(smithril_mk_bvsdiv, mk_bv_sdiv);
binary_function!(smithril_mk_bvsge, mk_bv_sge);
binary_function!(smithril_mk_bvsgt, mk_bv_sgt);
binary_function!(smithril_mk_bvshl, mk_bv_shl);
binary_function!(smithril_mk_bvsle, mk_bv_sle);
binary_function!(smithril_mk_bvslt, mk_bv_slt);
binary_function!(smithril_mk_bvsmod, mk_bv_smod);
binary_function!(smithril_mk_bvsub, mk_bv_sub);
binary_function!(smithril_mk_bvudiv, mk_bv_udiv);
binary_function!(smithril_mk_bvuge, mk_bv_uge);
binary_function!(smithril_mk_bvugt, mk_bv_ugt);
binary_function!(smithril_mk_bvule, mk_bv_ule);
binary_function!(smithril_mk_bvult, mk_bv_ult);
binary_function!(smithril_mk_bvsrem, mk_bv_srem);
binary_function!(smithril_mk_bvurem, mk_bv_urem);
binary_function!(smithril_mk_bvxor, mk_bv_xor);
binary_function!(smithril_mk_concat, mk_concat);
unary_function!(smithril_mk_not, mk_not);
binary_function!(smithril_mk_select, mk_select);

unary_function!(smithril_fp_is_nan, fp_is_nan);
unary_function!(smithril_fp_is_inf, fp_is_inf);
unary_function!(smithril_fp_is_normal, fp_is_normal);
unary_function!(smithril_fp_is_subnormal, fp_is_subnormal);
unary_function!(smithril_fp_is_zero, fp_is_zero);
unary_function!(smithril_fp_is_pos, fp_is_pos);
binary_function!(smithril_mk_fp_eq, mk_fp_eq);

binary_function!(smithril_mk_fp_rem, mk_fp_rem);
binary_function!(smithril_mk_fp_min, mk_fp_min);
binary_function!(smithril_mk_fp_max, mk_fp_max);
binary_function!(smithril_mk_fp_lt, mk_fp_lt);
binary_function!(smithril_mk_fp_leq, mk_fp_leq);
binary_function!(smithril_mk_fp_gt, mk_fp_gt);
binary_function!(smithril_mk_fp_geq, mk_fp_geq);
rm_binary_function!(smithril_mk_fp_add, mk_fp_add);
rm_binary_function!(smithril_mk_fp_sub, mk_fp_sub);
rm_binary_function!(smithril_mk_fp_mul, mk_fp_mul);
rm_binary_function!(smithril_mk_fp_div, mk_fp_div);

rm_unary_function!(smithril_mk_fp_sqrt, mk_fp_sqrt);
rm_unary_function!(smithril_mk_fp_rti, mk_fp_rti);
unary_function!(smithril_mk_fp_abs, mk_fp_abs);
unary_function!(smithril_mk_fp_neg, mk_fp_neg);

fp_to_fp_function!(smithril_mk_fp_to_fp_from_sbv, mk_fp_to_fp_from_sbv);
fp_to_fp_function!(smithril_mk_fp_to_fp_from_fp, mk_fp_to_fp_from_fp);
fp_to_fp_function!(smithril_mk_fp_to_fp_from_ubv, mk_fp_to_fp_from_ubv);
fp_to_function!(smithril_mk_fp_to_sbv, mk_fp_to_sbv);
fp_to_function!(smithril_mk_fp_to_ubv, mk_fp_to_ubv);

#[no_mangle]
pub unsafe extern "C" fn smithril_mk_fp_to_fp_from_bv(
    context: SmithrilContext,
    term1: SmithrilTerm,
    ew: u64,
    sw: u64,
) -> SmithrilTerm {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    let term1 = term1.0 as *const Term;
    Arc::increment_strong_count(term1);
    let smithril_term1 = Arc::from_raw(term1);
    let term = Arc::new(term::mk_fp_to_fp_from_bv(smithril_term1.as_ref(), ew, sw));
    let term = intern_term(smithril_context, term);
    let term = Arc::into_raw(term);
    Arc::decrement_strong_count(term);
    SmithrilTerm(term as *const c_void)
}

ternary_function!(smithril_mk_store, mk_store);
ternary_function!(smithril_mk_ite, mk_ite);
ternary_function!(smithril_mk_fp, mk_fp);

#[no_mangle]
pub unsafe extern "C" fn smithril_mk_extract(
    context: SmithrilContext,
    high: u64,
    low: u64,
    term: SmithrilTerm,
) -> SmithrilTerm {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    let term = term.0 as *const Term;
    Arc::increment_strong_count(term);
    let smithril_term = Arc::from_raw(term);
    let term = Arc::new(term::mk_extract(high, low, smithril_term.as_ref()));
    let term = intern_term(smithril_context, term);
    let term = Arc::into_raw(term);
    Arc::decrement_strong_count(term);
    SmithrilTerm(term as *const c_void)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_mk_sign_extend(
    context: SmithrilContext,
    size: u64,
    term: SmithrilTerm,
) -> SmithrilTerm {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    let term = term.0 as *const Term;
    Arc::increment_strong_count(term);
    let smithril_term = Arc::from_raw(term);
    let term = Arc::new(term::mk_sing_extend(size, smithril_term.as_ref()));
    let term = intern_term(smithril_context, term);
    let term = Arc::into_raw(term);
    Arc::decrement_strong_count(term);
    SmithrilTerm(term as *const c_void)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_mk_zero_extend(
    context: SmithrilContext,
    size: u64,
    term: SmithrilTerm,
) -> SmithrilTerm {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    let term = term.0 as *const Term;
    Arc::increment_strong_count(term);
    let smithril_term = Arc::from_raw(term);
    let term = Arc::new(term::mk_zero_extend(size, smithril_term.as_ref()));
    let term = intern_term(smithril_context, term);
    let term = Arc::into_raw(term);
    Arc::decrement_strong_count(term);
    SmithrilTerm(term as *const c_void)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_new_options() -> SmithrilOptions {
    let options = Arc::new(LockingOptions {
        options: RwLock::new(Options::default()),
    });
    OPTIONS.write().unwrap().push(options.clone());
    let options = Arc::into_raw(options);
    Arc::decrement_strong_count(options);
    SmithrilOptions(options as *const c_void)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_new_context() -> SmithrilContext {
    let smithril_context = RUNTIME.block_on(FACTORY.write().unwrap().new_context());
    CONTEXTS.write().unwrap().insert(smithril_context.clone());
    let context = Arc::into_raw(smithril_context);
    Arc::decrement_strong_count(context);
    SmithrilContext(context as *const c_void)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_new_solver(
    context: SmithrilContext,
    options: SmithrilOptions,
) -> SmithrilSolver {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    let options = options.0 as *const LockingOptions;
    Arc::increment_strong_count(options);
    let smithril_options = Arc::from_raw(options);
    let options = smithril_options.options.read().unwrap();
    let smithril_solver = RUNTIME.block_on(
        FACTORY
            .write()
            .unwrap()
            .new_solver(smithril_context, &options),
    );
    SOLVERS.write().unwrap().insert(smithril_solver.clone());
    let solver = Arc::into_raw(smithril_solver);
    Arc::decrement_strong_count(solver);
    SmithrilSolver(solver as *const c_void)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_check_sat(solver: SmithrilSolver) -> SolverResult {
    let solver = solver.0 as *const solver::SmithrilSolver;
    Arc::increment_strong_count(solver);
    let smithril_solver = Arc::from_raw(solver);
    RUNTIME.block_on(smithril_solver.check_sat())
}

#[no_mangle]
pub unsafe extern "C" fn smithril_reset(solver: SmithrilSolver) {
    let solver = solver.0 as *const solver::SmithrilSolver;
    Arc::increment_strong_count(solver);
    let smithril_solver = Arc::from_raw(solver);
    RUNTIME.block_on(smithril_solver.reset())
}

#[no_mangle]
pub unsafe extern "C" fn smithril_push(solver: SmithrilSolver) {
    let solver = solver.0 as *const solver::SmithrilSolver;
    Arc::increment_strong_count(solver);
    let smithril_solver = Arc::from_raw(solver);
    RUNTIME.block_on(smithril_solver.push())
}

#[no_mangle]
pub unsafe extern "C" fn smithril_pop(solver: SmithrilSolver, size: u64) {
    let solver = solver.0 as *const solver::SmithrilSolver;
    Arc::increment_strong_count(solver);
    let smithril_solver = Arc::from_raw(solver);
    RUNTIME.block_on(smithril_solver.pop(size))
}

#[no_mangle]
pub unsafe extern "C" fn smithril_assert(solver: SmithrilSolver, term: SmithrilTerm) {
    let solver = solver.0 as *const solver::SmithrilSolver;
    Arc::increment_strong_count(solver);
    let smithril_solver = Arc::from_raw(solver);
    let term = term.0 as *const Term;
    Arc::increment_strong_count(term);
    let smithril_term = Arc::from_raw(term);
    RUNTIME.block_on(smithril_solver.assert(&smithril_term))
}

#[no_mangle]
pub unsafe extern "C" fn smithril_eval(
    solver: SmithrilSolver,
    term: SmithrilTerm,
) -> *const c_char {
    let solver = solver.0 as *const solver::SmithrilSolver;
    Arc::increment_strong_count(solver);
    let smithril_solver = Arc::from_raw(solver);
    let term = term.0 as *const Term;
    Arc::increment_strong_count(term);
    let smithril_term = Arc::from_raw(term);
    RUNTIME
        .block_on(smithril_solver.eval(&smithril_term))
        .map(|term| {
            let constant = term::try_constant_to_string(&term).unwrap();
            let constant = Arc::new(CString::new(constant).unwrap());
            *LAST_EVALUATED_TERM.write().unwrap() = constant.clone();
            let constant: *const c_char = constant.as_ptr();
            constant
        })
        .unwrap_or_else(|| null())
}

#[no_mangle]
pub unsafe extern "C" fn smithril_unsat_core(solver: SmithrilSolver) -> SmithrilTermVector {
    let solver = solver.0 as *const solver::SmithrilSolver;
    Arc::increment_strong_count(solver);
    let smithril_solver = Arc::from_raw(solver);
    let unsat_core = RUNTIME.block_on(smithril_solver.unsat_core());
    let unsat_core = Arc::new(unsat_core);
    *LAST_UNSAT_CORE.write().unwrap() = unsat_core.clone();
    let unsat_core = Arc::into_raw(unsat_core);
    Arc::decrement_strong_count(unsat_core);
    SmithrilTermVector(unsat_core as *const c_void)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_unsat_core_size(unsat_core: SmithrilTermVector) -> u64 {
    let unsat_core = unsat_core.0 as *const Vec<Term>;
    Arc::increment_strong_count(unsat_core);
    let unsat_core = Arc::from_raw(unsat_core);
    unsat_core.len() as u64
}

#[no_mangle]
pub unsafe extern "C" fn smithril_unsat_core_get(
    context: SmithrilContext,
    unsat_core: SmithrilTermVector,
    index: u64,
) -> SmithrilTerm {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    let unsat_core = unsat_core.0 as *const Vec<Term>;
    Arc::increment_strong_count(unsat_core);
    let unsat_core = Arc::from_raw(unsat_core);
    let term = unsat_core.get(index as usize).unwrap().clone();
    let term = Arc::new(term);
    let term = intern_term(smithril_context, term);
    let term = Arc::into_raw(term);
    Arc::decrement_strong_count(term);
    SmithrilTerm(term as *const c_void)
}

#[no_mangle]
pub unsafe extern "C" fn smithril_delete_options(options: SmithrilOptions) {
    let options = options.0 as *const LockingOptions;
    Arc::increment_strong_count(options);
    let smithril_options = Arc::from_raw(options);
    OPTIONS
        .write()
        .unwrap()
        .retain(|value| !Arc::ptr_eq(value, &smithril_options));
}

#[no_mangle]
pub unsafe extern "C" fn smithril_set_timeout(options: SmithrilOptions, timeout: *const c_char) {
    let timeout = unsafe { CStr::from_ptr(timeout).to_string_lossy().into_owned() };
    let timeout: Duration = DurationString::try_from(timeout).unwrap().into();
    let options = options.0 as *const LockingOptions;
    Arc::increment_strong_count(options);
    let smithril_options = Arc::from_raw(options);
    smithril_options
        .options
        .write()
        .unwrap()
        .set_external_timeout(Some(timeout));
}

#[no_mangle]
pub unsafe extern "C" fn smithril_set_produce_unsat_core(options: SmithrilOptions, val: bool) {
    let options = options.0 as *const LockingOptions;
    Arc::increment_strong_count(options);
    let smithril_options = Arc::from_raw(options);
    smithril_options
        .options
        .write()
        .unwrap()
        .set_produce_unsat_core(val);
}

#[no_mangle]
pub unsafe extern "C" fn smithril_delete_context(context: SmithrilContext) {
    let context = context.0 as *const solver::SmithrilContext;
    Arc::increment_strong_count(context);
    let smithril_context = Arc::from_raw(context);
    TERMS.write().unwrap().remove(&smithril_context).unwrap();
    SORTS.write().unwrap().remove(&smithril_context).unwrap();
    CONTEXTS.write().unwrap().remove(&smithril_context);
    RUNTIME.block_on(FACTORY.write().unwrap().delete_context(smithril_context));
}

#[no_mangle]
pub unsafe extern "C" fn smithril_delete_solver(solver: SmithrilSolver) {
    let solver = solver.0 as *const solver::SmithrilSolver;
    Arc::increment_strong_count(solver);
    let smithril_solver = Arc::from_raw(solver);
    SOLVERS.write().unwrap().remove(&smithril_solver);
    RUNTIME.block_on(FACTORY.write().unwrap().delete_solver(smithril_solver));
}
