use smithril_lib::{
    converters::Converter,
    generalized::{SolverQuery, SolverResult},
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
        let output = solve_problem(input);
        let output_json = serde_json::to_string(&output).unwrap();
        writeln!(stdout, "{}", output_json).unwrap();
        stdout.flush().unwrap();
    }
}

fn solve_problem(input: SolverQuery) -> SolverResult {
    match input.query.as_str() {
        "sat" => SolverResult::Sat,
        "unsat" => SolverResult::Unsat,
        _ => SolverResult::Unknown,
    }
}
