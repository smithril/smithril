use core::panic;
use futures::stream::FuturesUnordered;
use futures::StreamExt;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

use ipc_channel::ipc::{IpcOneShotServer, IpcReceiver, IpcSender};
use tokio::process::{Child, Command};
use tokio::select;
use tokio_util::sync::CancellationToken;

use crate::converters::Converter;
use crate::generalized::{SolverResult, Term};

pub trait AsyncSolver {
    fn assert(
        &mut self,
        term: &Term,
    ) -> impl std::future::Future<
        Output = Result<SolverCommandResponse, Box<dyn std::error::Error + Send + Sync>>,
    > + Send;
    fn reset(
        &mut self,
    ) -> impl std::future::Future<
        Output = Result<SolverCommandResponse, Box<dyn std::error::Error + Send + Sync>>,
    > + Send;
    fn interrupt(
        &mut self,
    ) -> impl std::future::Future<Output = Result<(), Box<dyn std::error::Error + Send + Sync>>> + Send;
    fn check_sat(
        &mut self,
    ) -> impl std::future::Future<
        Output = Result<SolverResult, Box<dyn std::error::Error + Send + Sync>>,
    > + Send;
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum SolverCommand {
    Reset(),
    Assert(Term),
    CheckSat(),
}

#[derive(Serialize, PartialEq, Eq, Deserialize, Debug, Clone)]
pub enum SolverCommandResponse {
    Success(),
    Error(String),
}

#[derive(Serialize, Deserialize, Debug)]
pub struct RemoteSolver {
    pub command_sender: IpcSender<SolverCommand>,
    pub interrupt_sender: IpcSender<()>,
    pub response_receiver: IpcReceiver<SolverCommandResponse>,
    pub solver_result_receiver: IpcReceiver<SolverResult>,
}

impl RemoteSolver {
    async fn cancellable_check_sat(
        &mut self,
        token: CancellationToken,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        select! {
            res = self.check_sat() => { res }
            _ = token.cancelled() => {
                self.interrupt().await.unwrap();
                let custom_error = tokio::io::Error::new(tokio::io::ErrorKind::Other, "oh no!");
                Result::Err(custom_error.into_inner().unwrap())
            }
        }
    }
}

impl AsyncSolver for RemoteSolver {
    async fn assert(
        &mut self,
        term: &Term,
    ) -> Result<SolverCommandResponse, Box<dyn std::error::Error + Send + Sync>> {
        self.command_sender
            .send(SolverCommand::Assert(term.clone()))?;
        let command_response = self.response_receiver.recv()?;
        Ok(command_response)
    }

    async fn check_sat(
        &mut self,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        self.command_sender.send(SolverCommand::CheckSat())?;
        let command_response = self.solver_result_receiver.recv()?;
        Ok(command_response)
    }

    async fn interrupt(&mut self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.interrupt_sender.send(())?;
        Ok(())
    }

    async fn reset(
        &mut self,
    ) -> Result<SolverCommandResponse, Box<dyn std::error::Error + Send + Sync>> {
        self.command_sender.send(SolverCommand::Reset())?;
        let command_response = self.response_receiver.recv()?;
        Ok(command_response)
    }
}

struct SolverProcess {
    process: Child,
    pub solver: RemoteSolver,
}

impl SolverProcess {
    async fn new(
        solver_path: &str,
        converter: &Converter,
    ) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let (one_shot_server, one_shot_server_name) = IpcOneShotServer::new().unwrap();

        let serialized_converter = serde_json::to_string(converter).unwrap();
        let process = Command::new(solver_path)
            .arg(one_shot_server_name)
            .arg(serialized_converter)
            .spawn()?;
        let (_, solver) = one_shot_server.accept().unwrap();

        Ok(SolverProcess { process, solver })
    }

    async fn terminate(&mut self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.process.kill().await?;
        Ok(())
    }
}

pub struct PortfolioSolver {
    solvers: Vec<SolverProcess>,
}

fn get_solver_path(solver_name: &str) -> PathBuf {
    get_converters_dir().join(solver_name)
}

fn get_converters_dir() -> PathBuf {
    std::env::var("SMITHRIL_CONVERTERS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| panic!("SMITHRIL_CONVERTERS_DIR environment variable is not set"))
}

impl PortfolioSolver {
    pub async fn new(converters: Vec<Converter>) -> Self {
        let solver_path = get_solver_path("smithril-runner");
        let solver_path_string = solver_path.to_string_lossy().into_owned();
        let mut solvers: Vec<SolverProcess> = Default::default();

        for converter in &converters {
            let solver_process = SolverProcess::new(&solver_path_string, converter)
                .await
                .unwrap();
            solvers.push(solver_process);
        }
        Self { solvers }
    }

    pub async fn terminate(&mut self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        for solver in self.solvers.iter_mut() {
            solver.terminate().await?;
        }
        Ok(())
    }
}

impl AsyncSolver for PortfolioSolver {
    async fn assert(
        &mut self,
        term: &Term,
    ) -> Result<SolverCommandResponse, Box<dyn std::error::Error + Send + Sync>> {
        let mut handles = Vec::new();
        for solver in self.solvers.iter_mut() {
            let handler = solver.solver.assert(term);
            handles.push(handler);
        }
        for handler in handles {
            handler.await.unwrap();
        }
        Ok(SolverCommandResponse::Success())
    }

    async fn reset(
        &mut self,
    ) -> Result<SolverCommandResponse, Box<dyn std::error::Error + Send + Sync>> {
        let mut handles = Vec::new();
        for solver in self.solvers.iter_mut() {
            let handler = solver.solver.reset();
            handles.push(handler);
        }
        for handler in handles {
            handler.await.unwrap();
        }
        Ok(SolverCommandResponse::Success())
    }

    async fn interrupt(&mut self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut handles = Vec::new();
        for solver in self.solvers.iter_mut() {
            let handler = solver.solver.interrupt();
            handles.push(handler);
        }
        for handler in handles {
            handler.await.unwrap();
        }
        Ok(())
    }

    async fn check_sat(
        &mut self,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        let mut handles = Vec::new();
        let token = CancellationToken::new();
        for solver in self.solvers.iter_mut() {
            let handler = solver.solver.cancellable_check_sat(token.clone());
            handles.push(handler);
        }
        let mut futs = handles.into_iter().collect::<FuturesUnordered<_>>();

        let mut result = SolverResult::Unknown;
        while let Some(res) = futs.next().await {
            let res = res?;
            if SolverResult::Unknown == res {
                continue;
            }
            token.cancel();
            result = res;
            break;
        }
        while futs.next().await.is_some() {}
        Ok(result)
    }
}

#[cfg(test)]
fn sat_works() -> Term {
    use crate::generalized::{Sort, UnsortedTerm};

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

#[cfg(test)]
fn unsat_works() -> Term {
    use crate::generalized::{Sort, UnsortedTerm};

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

#[tokio::test]
async fn portfolio_solver_test() {
    use std::env;
    let mut smithril_converters_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    smithril_converters_dir.push("../target/debug");
    let smithril_converters_path = env::join_paths(vec![smithril_converters_dir]).unwrap();
    env::set_var("SMITHRIL_CONVERTERS_DIR", smithril_converters_path);

    let converters = vec![Converter::Bitwuzla, Converter::Z3];
    let t = sat_works();

    let mut psolver = PortfolioSolver::new(converters.clone()).await;
    let status = psolver.assert(&t).await.unwrap();
    assert_eq!(SolverCommandResponse::Success(), status);
    let status = psolver.check_sat().await.unwrap();
    assert_eq!(SolverResult::Sat, status);
    let status = psolver.reset().await.unwrap();
    assert_eq!(SolverCommandResponse::Success(), status);

    let t = unsat_works();

    let status = psolver.assert(&t).await.unwrap();
    assert_eq!(SolverCommandResponse::Success(), status);
    let status = psolver.check_sat().await.unwrap();
    assert_eq!(SolverResult::Unsat, status);
    let status = psolver.reset().await.unwrap();
    assert_eq!(SolverCommandResponse::Success(), status);

    psolver.terminate().await.unwrap();
}
