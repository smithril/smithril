use core::panic;
use std::path::PathBuf;
use std::process::Stdio;

use smithril_lib::converters::Converter;
use smithril_lib::generalized::{self, SolverQuery, SolverResult, Sort, Term, UnsortedTerm};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tokio::process::{Child, Command};
use tokio::sync::mpsc::{self, Receiver, Sender};

struct SolverProcess {
    process: Child,
    stdin: Sender<String>,
    stdout: Receiver<String>,
}

impl SolverProcess {
    async fn new(solver_path: &str) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let mut process = Command::new(solver_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;

        let stdin = process.stdin.take().expect("Failed to open stdin");
        let stdout = process.stdout.take().expect("Failed to open stdout");

        let (stdin_tx, mut stdin_rx): (Sender<String>, Receiver<String>) = mpsc::channel(1);
        let (stdout_tx, stdout_rx): (Sender<String>, Receiver<String>) = mpsc::channel(1);

        tokio::spawn(async move {
            let mut stdin = stdin;
            while let Some(input) = stdin_rx.recv().await {
                if stdin.write_all(input.as_bytes()).await.is_err() {
                    break;
                }
                if stdin.flush().await.is_err() {
                    break;
                }
            }
        });

        tokio::spawn(async move {
            let mut reader = BufReader::new(stdout);
            let mut buffer = String::new();
            while reader.read_line(&mut buffer).await.is_ok() {
                if stdout_tx.send(buffer.clone()).await.is_err() {
                    break;
                }
                buffer.clear();
            }
        });

        Ok(SolverProcess {
            process,
            stdin: stdin_tx,
            stdout: stdout_rx,
        })
    }

    async fn setup(
        &mut self,
        converter: Converter,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        // Serialize input to JSON
        let input_json = serde_json::to_string(&converter)? + "\n";

        // Send input to the solver's stdin
        self.stdin.send(input_json).await?;

        // Receive output from the solver's stdout
        let output_response = self
            .stdout
            .recv()
            .await
            .ok_or("Failed to read from stdout")?;

        println!("{}", output_response);
        Ok(())
    }

    async fn query(
        &mut self,
        input: &SolverQuery,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        // Serialize input to JSON
        let input_json = serde_json::to_string(input)? + "\n";

        // Send input to the solver's stdin
        self.stdin.send(input_json).await?;

        // Receive output from the solver's stdout
        let output_json = self
            .stdout
            .recv()
            .await
            .ok_or("Failed to read from stdout")?;

        // Deserialize output from JSON
        let solver_output: SolverResult = serde_json::from_str(&output_json)?;

        Ok(solver_output)
    }

    async fn terminate(mut self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.process.kill().await?;
        Ok(())
    }
}

fn get_converters_dir() -> PathBuf {
    std::env::var("SMITHRIL_CONVERTERS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| panic!("SMITHRIL_CONVERTERS_DIR environment variable is not set"))
}

fn get_solver_path(solver_name: &str) -> PathBuf {
    get_converters_dir().join(solver_name)
}

async fn run_portfolio(
    converters: Vec<Converter>,
    input: SolverQuery,
) -> Result<Vec<SolverResult>, Box<dyn std::error::Error + Send + Sync>> {
    let mut handles = Vec::new();

    let solver_path = get_solver_path("smithril-server");
    let solver_path_string = solver_path.to_string_lossy().into_owned();
    // Spawn a process for each solver
    for converter in converters {
        let input_clone = input.clone();
        let solver_path_string = solver_path_string.clone();
        let handle = tokio::spawn(async move {
            let mut solver_process = SolverProcess::new(&solver_path_string).await?;
            solver_process.setup(converter).await?;
            let result = solver_process.query(&input_clone).await;
            solver_process.terminate().await?;
            result
        });
        handles.push(handle);
    }

    // Collect results from all solvers
    let mut results = Vec::new();
    for handle in handles {
        if let Ok(result) = handle.await {
            results.push(result?);
        }
    }

    Ok(results)
}

fn sat_works() -> Term {
    let x = Term {
        term: UnsortedTerm::Constant(crate::generalized::GenConstant::Symbol("x".to_string())),
        sort: Sort::BvSort(3),
    };
    let y = Term {
        term: UnsortedTerm::Constant(crate::generalized::GenConstant::Numeral(2)),
        sort: Sort::BvSort(3),
    };
    Term {
        term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
            crate::generalized::DuoOperationKind::Eq,
            x,
            y,
        ))),
        sort: Sort::BoolSort(),
    }
}

fn unsat_works() -> Term {
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
    Term {
        term: UnsortedTerm::Operation(Box::new(crate::generalized::GenOperation::Duo(
            crate::generalized::DuoOperationKind::And,
            eq,
            n,
        ))),
        sort: Sort::BoolSort(),
    }
}

#[tokio::main]
async fn main() {
    println!("The client has started");
    let converters = vec![Converter::Bitwuzla, Converter::Z3];
    let t = sat_works();
    let input = SolverQuery { query: t };

    match run_portfolio(converters.clone(), input).await {
        Ok(results) => {
            for (i, result) in results.iter().enumerate() {
                println!("Solver {}: {:?}", i + 1, result);
            }
        }
        Err(e) => eprintln!("Error: {}", e),
    }

    let t = unsat_works();
    let input = SolverQuery { query: t };

    match run_portfolio(converters, input).await {
        Ok(results) => {
            for (i, result) in results.iter().enumerate() {
                println!("Solver {}: {:?}", i + 1, result);
            }
        }
        Err(e) => eprintln!("Error: {}", e),
    }
}
