mod bitwuzla;
pub mod generalized;
mod z3;

#[cfg(test)]
mod tests {
    use crate::bitwuzla::BitwuzlaConverter;
    use crate::generalized::{GeneralConverter, SolverResult};
    use crate::z3::Z3Converter;

    #[test]
    fn bitwuzla_sat_works() {
        let bc = BitwuzlaConverter::new();

        let sortbv3 = bc.mk_bv_sort(3);

        let x = bc.mk_smt_symbol("x", &sortbv3);

        let y = bc.mk_bv_value_uint64(&sortbv3, 2);

        let t = bc.mk_eq(&x, &y);

        bc.assert(&t);

        let result = bc.check_sat();
        assert_eq!(SolverResult::Sat, result);
    }

    #[test]
    fn z3_sat_works() {
        let zc = Z3Converter::new();

        let sortbv3 = zc.mk_bv_sort(3);

        let x = zc.mk_smt_symbol("x", &sortbv3);

        let y = zc.mk_bv_value_uint64(&sortbv3, 2);

        let t = zc.mk_eq(&x, &y);

        zc.assert(&t);

        let result = zc.check_sat();
        assert_eq!(SolverResult::Sat, result);
    }
}
