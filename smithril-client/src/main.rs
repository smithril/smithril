use core::panic;
use futures::stream::FuturesUnordered;
use futures::StreamExt;
use std::path::PathBuf;

use ipc_channel::ipc::{IpcOneShotServer, IpcReceiver, IpcSender};
use smithril_lib::converters::{ClientMessageType, ConverterType, ServerMessageType, SolverQuery};
use smithril_lib::generalized::{self, SolverResult, Sort, Term, UnsortedTerm};
use tokio::process::{Child, Command};
use tokio::select;
use tokio_util::sync::CancellationToken;
struct SolverProcess {
    process: Child,
    sender: IpcSender<ClientMessageType>,
    receiver: IpcReceiver<ServerMessageType>,
}

impl SolverProcess {
    async fn new(solver_path: &str) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let (one_shot_server, one_shot_server_name) = IpcOneShotServer::new().unwrap();

        let process = Command::new(solver_path)
            .arg(one_shot_server_name)
            .spawn()?;
        let (_, (sender, receiver)) = one_shot_server.accept().unwrap();

        Ok(SolverProcess {
            process,
            sender,
            receiver,
        })
    }

    async fn setup(
        &mut self,
        converter: ConverterType,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        // Send input to the solver's stdin
        self.sender.send(ClientMessageType::Converter(converter))?;

        // Receive output from the solver's stdout
        let output_response = self.receiver.recv()?;

        match output_response {
            ServerMessageType::Result(res) => match res {
                SolverResult::Sat => {
                    println!("Sat");
                    Ok(())
                }
                SolverResult::Unsat => {
                    println!("Unsat");
                    Ok(())
                }
                SolverResult::Unknown => {
                    println!("Unknown");
                    Ok(())
                }
            },
            ServerMessageType::Txt(s) => {
                println!("{}", s);
                Ok(())
            }
        }
    }

    async fn assert(&mut self, input: &SolverQuery) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        //Send to solver
        self.sender.send(ClientMessageType::Assert(input.clone()))?;
        //Recieve from solver
        let solver_output = self.receiver.recv()?;
        match solver_output {
            ServerMessageType::Result(res) => println!("{}", res),
            ServerMessageType::Txt(s) => println!("{}", s),
        }
        Ok(())
    }

    async fn check_sat(
        &mut self,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        //Send to solver
        self.sender.send(ClientMessageType::CheckSat())?;
        //Recieve from solver
        let solver_output = self.receiver.recv()?;
        match solver_output {
            ServerMessageType::Result(res) => Ok(res),
            ServerMessageType::Txt(s) => Err(Box::new(tokio::io::Error::new(
                tokio::io::ErrorKind::Other,
                s,
            ))),
        }
    }

    async fn terminate(mut self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.process.kill().await?;
        Ok(())
    }
}

// terminal: export SMITHRIL_CONVERTERS_DIR=~/rust_projects/smithril/target/debug/
fn get_converters_dir() -> PathBuf {
    std::env::var("SMITHRIL_CONVERTERS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| panic!("SMITHRIL_CONVERTERS_DIR environment variable is not set"))
}

fn get_solver_path(solver_name: &str) -> PathBuf {
    get_converters_dir().join(solver_name)
}

async fn run_solver(
    solver_path_string: String,
    converter: ConverterType,
    input_clone: SolverQuery,
    token: CancellationToken,
) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
    let mut solver_process = SolverProcess::new(&solver_path_string).await?;
    let result = select! {
        res = query_solver(&mut solver_process, converter, &input_clone) => { res }
        _ = token.cancelled() => {
            solver_process.terminate().await?;
            let custom_error = tokio::io::Error::new(tokio::io::ErrorKind::Other, "oh no!");
            return Result::Err(custom_error.into_inner().unwrap())
        }
    };
    solver_process.terminate().await?;
    result
}

async fn query_solver(
    solver_process: &mut SolverProcess,
    converter: ConverterType,
    input_clone: &SolverQuery,
) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
    solver_process.setup(converter).await?;
    solver_process.assert(input_clone).await;
    return solver_process.check_sat().await;
}

async fn run_portfolio(
    converters: Vec<ConverterType>,
    input: SolverQuery,
) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
    let mut handles = Vec::new();

    let solver_path = get_solver_path("smithril-server");
    let solver_path_string = solver_path.to_string_lossy().into_owned();
    let token = CancellationToken::new();

    // Spawn a process for each solver
    for converter in converters {
        let input_clone = input.clone();
        let solver_path_string = solver_path_string.clone();
        let cloned_token = token.clone();
        let handle = tokio::spawn(async move {
            run_solver(solver_path_string, converter, input_clone, cloned_token).await
        });
        handles.push(handle);
    }
    let mut futs = handles.into_iter().collect::<FuturesUnordered<_>>();

    let result = futs.next().await.unwrap();
    token.cancel();
    result.unwrap()
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
    let converters = vec![ConverterType::Bitwuzla, ConverterType::Z3];
    let t = sat_works();
    let input = SolverQuery { query: t };

    match run_portfolio(converters.clone(), input).await {
        Ok(result) => {
            println!("Solver: {:?}", result);
        }
        Err(e) => eprintln!("Error: {}", e),
    }

    let t = unsat_works();
    let input = SolverQuery { query: t };

    match run_portfolio(converters, input).await {
        Ok(result) => {
            println!("Solver: {:?}", result);
        }
        Err(e) => eprintln!("Error: {}", e),
    }
}
