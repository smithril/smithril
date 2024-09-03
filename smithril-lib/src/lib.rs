mod bitwuzla;
pub mod generalized;
pub mod solver;
mod utils;
mod z3;

pub mod converters {
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
    pub enum Converter {
        Bitwuzla,
        Z3,
    }

    #[derive(PartialEq, Eq, Serialize, Deserialize, Debug, Clone)]
    pub struct SolverQuery {
        pub query: Term,
    }

    use crate::{bitwuzla::BitwuzlaFactory, generalized::Term, z3::Z3Factory};

    pub fn mk_bitwuzla_factory() -> BitwuzlaFactory {
        BitwuzlaFactory::default()
    }

    pub fn mk_z3_factory() -> Z3Factory {
        Z3Factory::default()
    }
}

#[cfg(test)]
mod tests {

    use crate::bitwuzla::BitwuzlaFactory;
    use crate::generalized::{
        GeneralConverter, GeneralFactory, GeneralOptions, GeneralSolver, GeneralSort, GeneralTerm,
        Options, Solver, SolverResult, Sort, Term, UnsatCoreSolver, UnsortedTerm,
    };
    use crate::z3::Z3Factory;

    fn solver_sat_works<SL: Solver>(solver: &SL) {
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

    fn solver_unsat_works(solver: &dyn Solver) {
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

    fn generalized_sat_works<C, SL, S, T, O>(converter: &C, solver: &SL)
    where
        C: GeneralConverter<S, T>,
        SL: GeneralSolver<S, T, O, C>,
        S: GeneralSort,
        T: GeneralTerm,
        O: GeneralOptions,
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
        solver.assert(&converter.convert_term(&t));
        let result = solver.check_sat();
        assert_eq!(SolverResult::Sat, result);
    }

    fn generalized_unsat_works<C, SL, S, T, O>(converter: &C, solver: &SL)
    where
        C: GeneralConverter<S, T>,
        SL: GeneralSolver<S, T, O, C>,
        S: GeneralSort,
        T: GeneralTerm,
        O: GeneralOptions,
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
        solver.assert(&converter.convert_term(&u));
        let result = solver.check_sat();
        assert_eq!(SolverResult::Unsat, result);
    }

    fn generalized_array_sat_works<C, SL, S, T, O>(converter: &C, solver: &SL)
    where
        C: GeneralConverter<S, T>,
        SL: GeneralSolver<S, T, O, C>,
        S: GeneralSort,
        T: GeneralTerm,
        O: GeneralOptions,
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

        solver.assert(&converter.convert_term(&eq));

        let result = solver.check_sat();
        assert_eq!(SolverResult::Sat, result);
    }

    fn generalized_array_unsat_works<C, SL, S, T, O>(converter: &C, solver: &SL)
    where
        C: GeneralConverter<S, T>,
        SL: GeneralSolver<S, T, O, C>,
        S: GeneralSort,
        T: GeneralTerm,
        O: GeneralOptions,
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
        solver.assert(&converter.convert_term(&res));
        let result = solver.check_sat();
        assert_eq!(SolverResult::Unsat, result);
    }

    fn generalized_bv_op_sat_works<C, SL, S, T, O>(converter: &C, solver: &SL)
    where
        C: GeneralConverter<S, T>,
        SL: GeneralSolver<S, T, O, C>,
        S: GeneralSort,
        T: GeneralTerm,
        O: GeneralOptions,
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
        solver.assert(&converter.convert_term(&eq));
        let result = solver.check_sat();
        assert_eq!(SolverResult::Sat, result);
    }

    fn solver_eval_works(solver: &dyn Solver) {
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

    fn solver_unsat_core_works<S: Solver + UnsatCoreSolver>(solver: &S) {
        solver_unsat_works(solver);
        let u_core = solver.unsat_core();
        assert_eq!(u_core.len(), 2);
    }

    #[test]
    fn bitwuzla_sat_works() {
        let mut factory = BitwuzlaFactory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_sat_works(context.as_ref(), solver.as_ref());
    }

    #[test]
    fn z3_sat_works() {
        let mut factory = Z3Factory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_sat_works(context.as_ref(), solver.as_ref());
    }

    #[test]
    fn bitwuzla_unsat_works() {
        let mut factory = BitwuzlaFactory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_unsat_works(context.as_ref(), solver.as_ref());
    }

    #[test]
    fn z3_unsat_works() {
        let mut factory = Z3Factory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_unsat_works(context.as_ref(), solver.as_ref());
    }

    #[test]
    fn z3_shared_context() {
        let mut factory = Z3Factory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_unsat_works(context.as_ref(), solver.as_ref());
        let solver = factory.new_default_solver(context.clone());
        generalized_sat_works(context.as_ref(), solver.as_ref());
    }

    #[test]
    fn bitwuzla_array_sat_works() {
        let mut factory = Z3Factory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_array_sat_works(context.as_ref(), solver.as_ref());
    }

    #[test]
    fn bitwuzla_array_unsat_works() {
        let mut factory = BitwuzlaFactory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_array_sat_works(context.as_ref(), solver.as_ref());
    }

    #[test]
    fn bitwuzla_bv_op_sat_works() {
        let mut factory = BitwuzlaFactory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_bv_op_sat_works(context.as_ref(), solver.as_ref());
    }

    #[test]
    fn z3_bv_op_sat_works() {
        let mut factory = Z3Factory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_bv_op_sat_works(context.as_ref(), solver.as_ref());
    }

    #[test]
    fn z3_array_sat_works() {
        let mut factory = Z3Factory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_array_sat_works(context.as_ref(), solver.as_ref());
    }

    #[test]
    fn z3_array_unsat_works() {
        let mut factory = Z3Factory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_array_unsat_works(context.as_ref(), solver.as_ref());
    }

    #[test]
    fn z3_solver_sat_works() {
        let mut factory = Z3Factory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        solver_sat_works(solver.as_ref());
    }

    #[test]
    fn z3_solver_eval_works() {
        let mut factory = Z3Factory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        solver_eval_works(solver.as_ref());
    }

    #[test]
    fn bitwuzla_eval_works() {
        let mut factory = BitwuzlaFactory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        solver_eval_works(solver.as_ref());
    }

    #[test]
    fn bitwuzla_solver_unsat_core_works() {
        let mut factory = BitwuzlaFactory::default();
        let context = factory.new_context();
        let mut options = Options::default();
        options.set_produce_unsat_core(true);
        let solver = factory.new_solver(context, &options);
        solver_unsat_core_works(solver.as_ref());
    }

    #[test]
    fn z3_solver_unsat_core_works() {
        let mut factory = Z3Factory::default();
        let context = factory.new_context();
        let mut options = Options::default();
        options.set_produce_unsat_core(true);
        let solver = factory.new_solver(context, &options);
        solver_unsat_core_works(solver.as_ref());
    }
}
