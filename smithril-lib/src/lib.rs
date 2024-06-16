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
    use crate::generalized::{
        GeneralConverter, GeneralSort, GeneralTerm, SolverResult, Sort, Term, UnsortedTerm,
    };

    fn generalized_sat_works<'a, C, S, T>(converter: &'a C)
    where
        C: GeneralConverter<'a, S, T>,
        S: GeneralSort,
        S: 'a,
        T: GeneralTerm,
        T: 'a,
    {
        let x = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Symbol("x".to_string())),
            sort: Sort::BvSort(3),
        };
        let y = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Numeral(2)),
            sort: Sort::BvSort(3),
        };
        let t = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::Eq,
                x,
                y,
            ))),
            sort: Sort::BoolSort(),
        };
        converter.assert(&converter.convert_term(&t));
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
        let x = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Symbol("x".to_string())),
            sort: Sort::BvSort(3),
        };
        let y = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Numeral(2)),
            sort: Sort::BvSort(3),
        };
        let t = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::Eq,
                x,
                y,
            ))),
            sort: Sort::BoolSort(),
        };
        let n = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Uno(
                crate::generalized::UnoOperationKind::Not,
                t.clone(),
            ))),
            sort: Sort::BoolSort(),
        };
        let u = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::And,
                t,
                n,
            ))),
            sort: Sort::BoolSort(),
        };
        converter.assert(&converter.convert_term(&u));
        let result = converter.check_sat();
        assert_eq!(SolverResult::Unsat, result);
    }

    fn generalized_array_sat_works<'a, C, S, T>(converter: &'a C)
    where
        C: GeneralConverter<'a, S, T>,
        S: GeneralSort,
        S: 'a,
        T: GeneralTerm,
        T: 'a,
    {
        let s = Sort::BvSort(3);
        let boxs = Box::new(s.clone());
        let arr = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Symbol(
                "arr".to_string(),
            )),
            sort: Sort::ArraySort(boxs.clone(), boxs.clone()),
        };
        let i = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Symbol("i".to_string())),
            sort: s.clone(),
        };
        let j = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Symbol("j".to_string())),
            sort: s.clone(),
        };
        let select_i = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::Select,
                arr.clone(),
                i,
            ))),
            sort: s.clone(),
        };
        let select_j = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::Select,
                arr.clone(),
                j,
            ))),
            sort: s.clone(),
        };
        let eq = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::Eq,
                select_i,
                select_j,
            ))),
            sort: Sort::BoolSort(),
        };
        converter.assert(&converter.convert_term(&eq));
        let result = converter.check_sat();
        assert_eq!(SolverResult::Sat, result);
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

    #[test]
    fn bitwuzla_array_sat_works() {
        let bc = converters::mk_bitwulza();
        generalized_array_sat_works(&bc);
    }
}
