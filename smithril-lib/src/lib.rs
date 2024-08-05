mod bitwuzla;
pub mod generalized;
mod utils;
mod z3;

pub mod converters {
    use std::rc::Rc;

    use serde::{Deserialize, Serialize};
    #[derive(PartialEq, Serialize, Deserialize, Debug, Clone)]
    pub enum ClientMessageType {
        Converter(ConverterType),
        Assert(SolverQuery),
        CheckSat(),
    }

    #[derive(PartialEq, Serialize, Deserialize, Debug, Clone)]
    pub enum ServerMessageType {
        Result(SolverResult),
        Txt(String),
        Term(Term),
    }

    #[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
    pub enum ConverterType {
        Bitwuzla,
        Z3,
    }

    #[derive(PartialEq, Eq, Serialize, Deserialize, Debug, Clone)]
    pub struct SolverQuery {
        pub query: Term,
    }

    use crate::{
        bitwuzla::BitwuzlaConverter,
        generalized::{SolverResult, Term},
        z3::{Z3ContextInner, Z3Converter},
    };

    pub fn mk_bitwulza() -> BitwuzlaConverter {
        BitwuzlaConverter::default()
    }

    pub fn mk_z3_context() -> Z3ContextInner {
        Z3ContextInner::default()
    }

    pub fn mk_z3() -> Z3Converter {
        Z3Converter::default()
    }

    pub fn mk_z3_with_context(context: Rc<Z3ContextInner>) -> Z3Converter {
        Z3Converter::new(context)
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::converters;
    use crate::generalized::{
        GeneralConverter, GeneralSolver, GeneralSort, GeneralTerm, GeneralUnsatCoreSolver,
        SolverResult, Sort, Term, UnsortedTerm,
    };

    fn generalized_solvers_sat(solver: &dyn GeneralSolver) {
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
        solver.assert(&t);
        let result = solver.check_sat();
        assert_eq!(SolverResult::Sat, result);
    }

    fn generalized_solvers_unsat(solver: &dyn GeneralSolver) {
        let x = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Symbol("x".to_string())),
            sort: Sort::BvSort(3),
        };
        let y = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Numeral(2)),
            sort: Sort::BvSort(3),
        };
        let eq = Term {
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
                eq.clone(),
            ))),
            sort: Sort::BoolSort(),
        };
        solver.assert(&eq);
        solver.assert(&n);
        let result = solver.check_sat();
        assert_eq!(SolverResult::Unsat, result);
    }

    fn generalized_sat_works<C, S, T>(converter: &C)
    where
        C: GeneralConverter<S, T>,
        S: GeneralSort,
        T: GeneralTerm,
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

    fn generalized_unsat_works<C, S, T>(converter: &C)
    where
        C: GeneralConverter<S, T>,
        S: GeneralSort,
        T: GeneralTerm,
    {
        let x = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Symbol("x".to_string())),
            sort: Sort::BvSort(3),
        };
        let y = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Numeral(2)),
            sort: Sort::BvSort(3),
        };
        let eq = Term {
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
                eq.clone(),
            ))),
            sort: Sort::BoolSort(),
        };
        let u = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::And,
                eq,
                n,
            ))),
            sort: Sort::BoolSort(),
        };
        converter.assert(&converter.convert_term(&u));
        let result = converter.check_sat();
        assert_eq!(SolverResult::Unsat, result);
    }

    fn generalized_array_sat_works<C, S, T>(converter: &C)
    where
        C: GeneralConverter<S, T>,
        S: GeneralSort,
        T: GeneralTerm,
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

    fn generalized_array_unsat_works<C, S, T>(converter: &C)
    where
        C: GeneralConverter<S, T>,
        S: GeneralSort,
        T: GeneralTerm,
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
                i.clone(),
            ))),
            sort: s.clone(),
        };
        let select_j = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::Select,
                arr.clone(),
                j.clone(),
            ))),
            sort: s.clone(),
        };
        let eq_select = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::Eq,
                select_i,
                select_j,
            ))),
            sort: Sort::BoolSort(),
        };
        let eq_indexes = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::Eq,
                i,
                j,
            ))),
            sort: Sort::BoolSort(),
        };
        let n_eq_select = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Uno(
                crate::generalized::UnoOperationKind::Not,
                eq_select.clone(),
            ))),
            sort: Sort::BoolSort(),
        };
        let res = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::And,
                eq_indexes,
                n_eq_select,
            ))),
            sort: Sort::BoolSort(),
        };
        converter.assert(&converter.convert_term(&res));
        let result = converter.check_sat();
        assert_eq!(SolverResult::Unsat, result);
    }

    fn bv_test<C, S, T>(converter: &C)
    where
        C: GeneralConverter<S, T>,
        S: GeneralSort,
        T: GeneralTerm,
    {
        let x = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Symbol("x".to_string())),
            sort: Sort::BvSort(3),
        };
        let y = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Numeral(2)),
            sort: Sort::BvSort(3),
        };
        let bvor1 = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::BvOr,
                x.clone(),
                y.clone(),
            ))),
            sort: Sort::BoolSort(),
        };
        let bvor2 = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::BvOr,
                y,
                x,
            ))),
            sort: Sort::BoolSort(),
        };
        let eq = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::Eq,
                bvor1,
                bvor2,
            ))),
            sort: Sort::BoolSort(),
        };
        converter.assert(&converter.convert_term(&eq));
        let result = converter.check_sat();
        assert_eq!(SolverResult::Sat, result);
    }

    fn generalized_eval_works(solver: &mut dyn GeneralSolver) {
        let x = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Symbol("x".to_string())),
            sort: Sort::BvSort(5),
        };
        let y = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Symbol("y".to_string())),
            sort: Sort::BvSort(5),
        };
        let num5 = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Numeral(5)),
            sort: Sort::BvSort(5),
        };
        let num10 = Term {
            term: UnsortedTerm::Constant(crate::generalized::GenConstant::Numeral(10)),
            sort: Sort::BvSort(5),
        };
        let eq_x = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::Eq,
                x.clone(),
                num5.clone(),
            ))),
            sort: Sort::BoolSort(),
        };
        let eq_y = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::Eq,
                y.clone(),
                num10.clone(),
            ))),
            sort: Sort::BoolSort(),
        };
        let t = Term {
            term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
                crate::generalized::DuoOperationKind::And,
                eq_x.clone(),
                eq_y.clone(),
            ))),
            sort: Sort::BoolSort(),
        };
        solver.assert(&t);
        let res = solver.check_sat();
        assert_eq!(res, SolverResult::Sat);
        let eval_x = solver.eval(&x);
        let eval_y = solver.eval(&y);
        assert_eq!(eval_x.clone().unwrap(), num5);
        assert_eq!(eval_y.clone().unwrap(), num10);
    }

    fn generalized_unsat_core_works<S: GeneralSolver + GeneralUnsatCoreSolver>(solver: &mut S) {
        generalized_solvers_unsat(solver);
        let u_core = solver.unsat_core();
        assert_eq!(u_core.len(), 2);
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
        let ct = Rc::new(converters::mk_z3_context());
        let zc = converters::mk_z3_with_context(ct.clone());
        generalized_unsat_works(&zc);
        let zc = converters::mk_z3_with_context(ct);
        generalized_sat_works(&zc);
    }

    #[test]
    fn bitwuzla_array_sat_works() {
        let bc = converters::mk_bitwulza();
        generalized_array_sat_works(&bc);
    }

    #[test]
    fn bitwuzla_array_unsat_works() {
        let bc = converters::mk_bitwulza();
        generalized_array_unsat_works(&bc);
    }

    #[test]
    fn bitwuzla_bv_test() {
        let bc = converters::mk_bitwulza();
        bv_test(&bc);
    }

    #[test]
    fn z3_array_sat_works() {
        let zc = converters::mk_z3();
        generalized_array_sat_works(&zc);
    }

    #[test]
    fn z3_array_unsat_works() {
        let zc = converters::mk_z3();
        generalized_array_unsat_works(&zc);
    }

    #[test]
    fn general_solver_checksat_test() {
        let mut solver: Box<dyn GeneralSolver> = Box::new(converters::mk_bitwulza());
        generalized_solvers_sat(solver.as_mut());
        solver = Box::new(converters::mk_z3());
        generalized_solvers_sat(solver.as_mut());
    }

    #[test]
    fn z3_eval_works() {
        let mut zc = converters::mk_z3();
        generalized_eval_works(&mut zc);
    }

    #[test]
    fn bitwuzla_eval_works() {
        let mut bc = converters::mk_bitwulza();
        generalized_eval_works(&mut bc);
    }

    #[test]
    fn bitwuzla_unsat_core_works() {
        let mut bc = converters::mk_bitwulza();
        generalized_unsat_core_works(&mut bc);
    }

    #[test]
    fn z3_unsat_core_works() {
        let mut zc = converters::mk_z3();
        generalized_unsat_core_works(&mut zc);
    }
}
