use smithril_lib::{
    converters::{self, Converter},
    generalized::{GeneralConverter, GeneralSort, GeneralTerm, SolverQuery, SolverResult},
};
use std::io::{self, BufRead, Write};

fn main() {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut stdout = stdout.lock();

    let converter_line = stdin
        .lock()
        .lines()
        .next()
        .expect("Failed to read converter")
        .unwrap();
    let converter: Converter =
        serde_json::from_str(&converter_line).expect("Failed to parse converter");

    match converter {
        Converter::Bitwuzla => {
            writeln!(stdout, "Bitwuzla converter has set up").unwrap();
            stdout.flush().unwrap();
        }
        Converter::Z3 => {
            writeln!(stdout, "Z3 converter has set up").unwrap();
            stdout.flush().unwrap();
        }
    }

    for line in stdin.lock().lines() {
        let input: SolverQuery = serde_json::from_str(&line.unwrap()).unwrap();
        let output = match converter {
            Converter::Bitwuzla => {
                let bc = converters::mk_bitwulza();
                solve_problem(&bc, input)
            }
            Converter::Z3 => {
                let bc = converters::mk_z3();
                solve_problem(&bc, input)
            }
        };
        let output_json = serde_json::to_string(&output).unwrap();
        writeln!(stdout, "{}", output_json).unwrap();
        stdout.flush().unwrap();
    }
}

fn solve_problem<'a, C, S, T>(converter: &'a C, input: SolverQuery) -> SolverResult
where
    C: GeneralConverter<'a, S, T>,
    S: GeneralSort,
    S: 'a,
    T: GeneralTerm,
    T: 'a,
{
    converter.assert(&converter.convert_term(&input.query));
    converter.check_sat()
}
