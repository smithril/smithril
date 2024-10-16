mod bitwuzla;
mod dummy;
pub mod generalized;
pub mod solver;
pub mod term;
mod utils;
mod z3;

pub mod converters {
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
    pub enum Converter {
        Bitwuzla,
        Z3,
        Dummy,
    }

    #[derive(PartialEq, Eq, Serialize, Deserialize, Debug, Clone)]
    pub struct SolverQuery {
        pub query: Term,
    }

    use crate::{bitwuzla::BitwuzlaFactory, dummy::DummyFactory, term::Term, z3::Z3Factory};

    pub fn mk_bitwuzla_factory() -> BitwuzlaFactory {
        BitwuzlaFactory::default()
    }

    pub fn mk_z3_factory() -> Z3Factory {
        Z3Factory::default()
    }

    pub fn mk_dummy_factory() -> DummyFactory {
        DummyFactory::default()
    }
}

mod capi;

#[cfg(test)]
mod tests {

    use crate::bitwuzla::BitwuzlaFactory;
    use crate::generalized::{
        Factory, GeneralConverter, GeneralFpConverter, GeneralOptions, GeneralSolver, GeneralSort,
        GeneralTerm, Options, Solver, SolverResult,
    };
    use crate::term::{self, RoundingMode, Sort, Term, UnsortedTerm};
    use crate::z3::Z3Factory;

    fn solver_sat_works<SL: Solver>(solver: &SL) {
        let bv_sort = term::mk_bv_sort(3);
        let x = term::mk_smt_symbol("x", &bv_sort);
        let y = term::mk_bv_value_uint64(2, &bv_sort);
        let t = term::mk_eq(&x, &y);
        solver.assert(&t);
        let result = solver.check_sat();
        assert_eq!(SolverResult::Sat, result);
    }

    fn solver_unsat_works(solver: &dyn Solver) {
        let bv_sort = term::mk_bv_sort(3);
        let x = term::mk_smt_symbol("x", &bv_sort);
        let y = term::mk_bv_value_uint64(2, &bv_sort);
        let eq = term::mk_eq(&x, &y);
        let n = term::mk_not(&eq);
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
        let bv_sort = term::mk_bv_sort(3);
        let x = term::mk_smt_symbol("x", &bv_sort);
        let y = term::mk_bv_value_uint64(2, &bv_sort);
        let t = term::mk_eq(&x, &y);
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
        let bv_sort = term::mk_bv_sort(3);
        let x = term::mk_smt_symbol("x", &bv_sort);
        let y = term::mk_bv_value_uint64(2, &bv_sort);
        let eq = term::mk_eq(&x, &y);
        let n = term::mk_not(&eq);
        let u = term::mk_and(&eq, &n);
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
        let s = term::mk_bv_sort(3);
        let array_sort = term::mk_array_sort(&s, &s);
        let arr = term::mk_smt_symbol("arr", &array_sort);
        let i = term::mk_smt_symbol("i", &s);
        let j = term::mk_smt_symbol("j", &s);
        let select_i = term::mk_select(&arr, &i);
        let select_j = term::mk_select(&arr, &j);
        let eq = term::mk_eq(&select_i, &select_j);

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
        let s = term::mk_bv_sort(3);
        let array_sort = term::mk_array_sort(&s, &s);
        let arr = term::mk_smt_symbol("arr", &array_sort);
        let i = term::mk_smt_symbol("i", &s);
        let j = term::mk_smt_symbol("j", &s);
        let select_i = term::mk_select(&arr, &i);
        let select_j = term::mk_select(&arr, &j);
        let eq_select = term::mk_eq(&select_i, &select_j);
        let eq_indexes = term::mk_eq(&i, &j);
        let n_eq_select = term::mk_not(&eq_select);
        let res = term::mk_and(&eq_indexes, &n_eq_select);
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
        let bv_sort = term::mk_bv_sort(3);
        let x = term::mk_smt_symbol("x", &bv_sort);
        let y = term::mk_bv_value_uint64(2, &bv_sort);
        let bvor1 = term::mk_bv_or(&x, &y);
        let bvor2 = term::mk_bv_or(&y, &x);
        let eq = term::mk_eq(&bvor1, &bvor2);
        solver.assert(&converter.convert_term(&eq));
        let result = solver.check_sat();
        assert_eq!(SolverResult::Sat, result);
    }

    fn solver_eval_works(solver: &dyn Solver) {
        let bv_sort = term::mk_bv_sort(5);
        let x = term::mk_smt_symbol("x", &bv_sort);
        let y = term::mk_smt_symbol("y", &bv_sort);
        let num5 = term::mk_bv_value_uint64(5, &bv_sort);
        let num10 = term::mk_bv_value_uint64(10, &bv_sort);
        let eq_x = term::mk_eq(&x, &num5);
        let eq_y = term::mk_eq(&y, &num10);
        let t = term::mk_and(&eq_x, &eq_y);
        solver.assert(&t);
        let res = solver.check_sat();
        assert_eq!(res, SolverResult::Sat);
        let eval_x = solver.eval(&x);
        let eval_y = solver.eval(&y);
        assert_eq!(eval_x.clone().unwrap(), num5);
        assert_eq!(eval_y.clone().unwrap(), num10);
    }

    fn solver_unsat_core_works<S: Solver>(solver: &S) {
        solver_unsat_works(solver);
        let u_core = solver.unsat_core();
        assert_eq!(u_core.len(), 2);
    }

    fn generalized_solver_fp_works<C, SL, S, T, O>(converter: &C, solver: &SL)
    where
        C: GeneralConverter<S, T>,
        SL: GeneralSolver<S, T, O, C>,
        S: GeneralSort,
        T: GeneralTerm,
        O: GeneralOptions,
    {
        let x1 = Term {
            term: UnsortedTerm::Constant(term::GenConstant::Numeral(0)),
            sort: Sort::BvSort(1),
        };
        let x2 = Term {
            term: UnsortedTerm::Constant(term::GenConstant::Numeral(2)),
            sort: Sort::BvSort(5),
        };
        let x3 = Term {
            term: UnsortedTerm::Constant(term::GenConstant::Numeral(5)),
            sort: Sort::BvSort(5),
        };
        let y1 = Term {
            term: UnsortedTerm::Constant(term::GenConstant::Numeral(0)),
            sort: Sort::BvSort(1),
        };
        let y2 = Term {
            term: UnsortedTerm::Constant(term::GenConstant::Numeral(3)),
            sort: Sort::BvSort(5),
        };
        let y3 = Term {
            term: UnsortedTerm::Constant(term::GenConstant::Numeral(3)),
            sort: Sort::BvSort(5),
        };
        let x = Term {
            term: UnsortedTerm::Operation(Box::new(term::GenOperation::Trio(
                term::TrioOperationKind::Fp,
                x1,
                x2,
                x3,
            ))),
            sort: Sort::FpSort(5, 5),
        };
        let y = Term {
            term: UnsortedTerm::Operation(Box::new(term::GenOperation::Trio(
                term::TrioOperationKind::Fp,
                y1,
                y2,
                y3,
            ))),
            sort: Sort::FpSort(5, 5),
        };
        let xy = Term {
            term: UnsortedTerm::Operation(Box::new(term::GenOperation::FpDuo(
                term::FpDuoOperationKind::FpAdd,
                RoundingMode::RNA,
                x.clone(),
                y.clone(),
            ))),
            sort: Sort::FpSort(10, 10),
        };
        let yx = Term {
            term: UnsortedTerm::Operation(Box::new(term::GenOperation::FpDuo(
                term::FpDuoOperationKind::FpAdd,
                RoundingMode::RNA,
                y.clone(),
                x.clone(),
            ))),
            sort: Sort::FpSort(10, 10),
        };
        let t = Term {
            term: UnsortedTerm::Operation(Box::new(term::GenOperation::Duo(
                term::DuoOperationKind::FpEq,
                xy,
                yx,
            ))),
            sort: Sort::BoolSort(),
        };
        solver.assert(&converter.convert_term(&t));
        let result = solver.check_sat();
        assert_eq!(SolverResult::Sat, result);
    }

    fn generalized_solver_fp_unsat_works<C, SL, S, T, O>(converter: &C, solver: &SL)
    where
        C: GeneralConverter<S, T>,
        SL: GeneralSolver<S, T, O, C>,
        S: GeneralSort,
        T: GeneralTerm,
        O: GeneralOptions,
    {
        let x1 = Term {
            term: UnsortedTerm::Constant(term::GenConstant::Numeral(0)),
            sort: Sort::BvSort(1),
        };
        let x2 = Term {
            term: UnsortedTerm::Constant(term::GenConstant::Numeral(2)),
            sort: Sort::BvSort(10),
        };
        let x3 = Term {
            term: UnsortedTerm::Constant(term::GenConstant::Numeral(5)),
            sort: Sort::BvSort(10),
        };
        let x = Term {
            term: UnsortedTerm::Operation(Box::new(term::GenOperation::Trio(
                term::TrioOperationKind::Fp,
                x1,
                x2,
                x3,
            ))),
            sort: Sort::FpSort(10, 10),
        };
        let sqrtx_rna = Term {
            term: UnsortedTerm::Operation(Box::new(term::GenOperation::FpUno(
                term::FpUnoOperationKind::FpSqrt,
                RoundingMode::RNA,
                x.clone(),
            ))),
            sort: Sort::FpSort(10, 10),
        };
        let sqrtx_rtz = Term {
            term: UnsortedTerm::Operation(Box::new(term::GenOperation::FpUno(
                term::FpUnoOperationKind::FpSqrt,
                RoundingMode::RTZ,
                x.clone(),
            ))),
            sort: Sort::FpSort(10, 10),
        };
        let t = Term {
            term: UnsortedTerm::Operation(Box::new(term::GenOperation::Duo(
                term::DuoOperationKind::FpEq,
                sqrtx_rna,
                sqrtx_rtz,
            ))),
            sort: Sort::BoolSort(),
        };
        solver.assert(&converter.convert_term(&t));
        let result = solver.check_sat();
        assert_eq!(SolverResult::Unsat, result);
    }

    fn generalized_generate_fp_ieee<FP, S, T>(
        converter: &FP,
    ) -> crate::generalized::FloatingPointAsBinary
    where
        FP: GeneralFpConverter<S, T>,
        S: GeneralSort,
        T: GeneralTerm,
    {
        let x1 = Term {
            term: UnsortedTerm::Constant(term::GenConstant::Numeral(0)),
            sort: Sort::BvSort(1),
        };
        let x2 = Term {
            term: UnsortedTerm::Constant(term::GenConstant::Numeral(2)),
            sort: Sort::BvSort(10),
        };
        let x3 = Term {
            term: UnsortedTerm::Constant(term::GenConstant::Numeral(5)),
            sort: Sort::BvSort(10),
        };
        let x = Term {
            term: UnsortedTerm::Operation(Box::new(term::GenOperation::Trio(
                term::TrioOperationKind::Fp,
                x1,
                x2,
                x3,
            ))),
            sort: Sort::FpSort(10, 10),
        };

        converter.fp_get_values_ieee(&converter.convert_term(&x))
    }

    #[test]
    fn ieee_works() {
        let mut factory = BitwuzlaFactory::default();
        let context = factory.new_context();
        let x = generalized_generate_fp_ieee(context.as_ref());
        let mut factory = Z3Factory::default();
        let context = factory.new_context();
        let y = generalized_generate_fp_ieee(context.as_ref());
        assert_eq!(x, y);
    }

    #[test]
    fn bitwuzla_fp_works() {
        let mut factory = BitwuzlaFactory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_solver_fp_works(context.as_ref(), solver.as_ref());
    }

    #[test]
    fn z3_fp_works() {
        let mut factory = Z3Factory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_solver_fp_works(context.as_ref(), solver.as_ref());
    }

    #[test]
    fn bitwuzla_fp_unsat_works() {
        let mut factory = BitwuzlaFactory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_solver_fp_unsat_works(context.as_ref(), solver.as_ref());
    }

    #[test]
    fn z3_fp_unsat_works() {
        let mut factory = Z3Factory::default();
        let context = factory.new_context();
        let solver = factory.new_default_solver(context.clone());
        generalized_solver_fp_unsat_works(context.as_ref(), solver.as_ref());
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
