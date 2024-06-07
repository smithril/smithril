mod bitwuzla;
pub mod generalized;
mod z3;

#[cfg(test)]
mod tests {
    use crate::bitwuzla::BitwuzlaConverter;
    use crate::generalized::{GeneralConverter, GeneralSort, GeneralTerm, SolverResult};
    use crate::z3::Z3Converter;

    fn generalized_sat_works<'a, C, S, T>(converter: &'a C)
    where
        C: GeneralConverter<'a, S, T>,
        S: GeneralSort,
        S: 'a,
        T: GeneralTerm,
        T: 'a,
    {
        let sortbv3 = converter.mk_bv_sort(3);
        let x = converter.mk_smt_symbol("x", &sortbv3);
        let y = converter.mk_bv_value_uint64(&sortbv3, 2);
        let t = converter.mk_eq(&x, &y);

        converter.assert(&t);

        let result = converter.check_sat();
        assert_eq!(SolverResult::Sat, result);
    }

    fn generalized_unsat_works<'a, C, S, T>(converter: &'a C)
    where
        C: GeneralConverter<'a, S, T>,
        S: GeneralSort,
        S: 'a,
        T: GeneralTerm,
        T: 'a,
    {
        let sortbv3 = converter.mk_bv_sort(3);
        let x = converter.mk_smt_symbol("x", &sortbv3);
        let y = converter.mk_bv_value_uint64(&sortbv3, 2);
        let t = converter.mk_eq(&x, &y);
        let n = converter.mk_not(&t);
        let u = converter.mk_and(&t, &n);

        converter.assert(&u);

        let result = converter.check_sat();
        assert_eq!(SolverResult::Unsat, result);
    }

    #[test]
    fn bitwuzla_sat_works() {
        let bc = BitwuzlaConverter::new();
        generalized_sat_works(&bc);
    }

    #[test]
    fn z3_sat_works() {
        let zc = Z3Converter::new();
        generalized_sat_works(&zc);
    }

    #[test]
    fn bitwuzla_unsat_works() {
        let bc = BitwuzlaConverter::new();
        generalized_unsat_works(&bc);
    }

    #[test]
    fn z3_unsat_works() {
        let zc = Z3Converter::new();
        generalized_unsat_works(&zc);
    }
}
