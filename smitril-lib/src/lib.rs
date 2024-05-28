mod bitwuzla;
pub mod generalized;

#[cfg(test)]
mod tests {
    use crate::bitwuzla::BitwuzlaConvertor;
    use crate::generalized::{GeneralConvertor, SolverResult};

    #[test]
    fn it_works() {
        let bc = BitwuzlaConvertor::new();

        let sortbv3 = bc.mk_bv_sort(3);

        let x = bc.mk_smt_symbol("x", &sortbv3);

        let y = bc.mk_bv_value_uint64(&sortbv3, 2);

        let t = bc.mk_eq(&x, &y);

        bc.assert(&t);

        let result = bc.check_sat();
        assert_eq!(SolverResult::Sat, result);

        println!("Expect: sat");

        println!("Bitwuzla: {}", result);
    }
}
