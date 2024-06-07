mod bitwuzla;
pub mod generalized;
mod z3;

pub mod converters {
    use crate::{
        bitwuzla::BitwuzlaConverter,
        z3::{Z3ContextInner, Z3Converter},
    };

    pub fn mk_bitwulza() -> BitwuzlaConverter {
        BitwuzlaConverter::default()
    }

    pub fn mk_z3_context() -> Z3ContextInner {
        Z3ContextInner::default()
    }

    pub fn mk_z3() -> Z3Converter<'static> {
        Z3Converter::default()
    }

    pub fn mk_z3_with_context(context: &Z3ContextInner) -> Z3Converter<'_> {
        Z3Converter::new(context)
    }
}

#[cfg(test)]
mod tests {
    use crate::converters;
    use crate::generalized::{GeneralConverter, GeneralSort, GeneralTerm, SolverResult};

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
        let bc = converters::mk_bitwulza();
        generalized_sat_works(&bc);
    }

    #[test]
    fn z3_sat_works() {
        let zc = converters::mk_z3();
        generalized_sat_works(&zc);
    }

    #[test]
    fn bitwuzla_unsat_works() {
        let bc = converters::mk_bitwulza();
        generalized_unsat_works(&bc);
    }

    #[test]
    fn z3_unsat_works() {
        let zc = converters::mk_z3();
        generalized_unsat_works(&zc);
    }

    #[test]
    fn z3_shared_context() {
        let ct = converters::mk_z3_context();
        let zc = converters::mk_z3_with_context(&ct);
        generalized_unsat_works(&zc);
        let zc = converters::mk_z3_with_context(&ct);
        generalized_sat_works(&zc);
    }
}
