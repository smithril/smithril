mod generalized;

use generalized::{bitwuzla_sys, BitwuzlaConvertor};
use std::ffi::{c_char, CStr, CString};

use crate::generalized::{BitwuzlaSort, BitwuzlaTerm, GeneralConvertor};

fn main() {
    let bc = BitwuzlaConvertor::new();

    let mut sortbv4 = bc.mk_bv_sort(4);

    let mut sortbv3 = bc.mk_bv_sort(3);

    //let bsortbv4 = sortbv4; //BitwuzlaSort { sort: sortbv4.sort };

    let mut x = bc.mk_smt_symbol("x", &sortbv4);

    let mut y = bc.mk_bv_value_uint64(&sortbv3, 2);

    let mut t = bc.mk_eq(&x, &y);

    bc.assert(&t);

    let mut result = bc.check_sat();

    println!("Expect: sat");

    println!("Bitwuzla: {}", result);
}
