use core::fmt;
use futures::stream::FuturesUnordered;
use futures::StreamExt;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::rc::Rc;

use ipc_channel::ipc::{IpcOneShotServer, IpcReceiver, IpcSender};
use tokio::process::{Child, Command};
use tokio::select;
use tokio_util::sync::CancellationToken;

use crate::converters::Converter;
use crate::generalized::{Options, SolverResult, Term};

pub struct RemoteFactory {
    process: Child,
    worker: Rc<RemoteWorker>,
}

impl RemoteFactory {
    pub async fn new(
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

        Ok(RemoteFactory {
            process,
            worker: Rc::new(solver),
        })
    }

    pub async fn terminate(&mut self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.process.kill().await?;
        Ok(())
    }

    pub async fn new_context(
        &self,
    ) -> Result<RemoteContext, Box<dyn std::error::Error + Send + Sync>> {
        self.worker
            .command_sender
            .send(RemoteCommand::NewContext())?;
        let command_response = self.worker.new_context_receiver.recv()?;
        let command_response = RemoteContext {
            label: command_response,
        };
        Ok(command_response)
    }

    pub async fn new_solver(
        &self,
        context: &RemoteContext,
    ) -> Result<RemoteSolver, Box<dyn std::error::Error + Send + Sync>> {
        self.worker
            .command_sender
            .send(RemoteCommand::NewSolver(context.label))?;
        let command_response = self.worker.new_solver_receiver.recv()?;
        let command_response = RemoteSolver {
            label: command_response,
            worker: self.worker.clone(),
        };
        Ok(command_response)
    }

    pub async fn delete_context(
        &self,
        context: RemoteContext,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker
            .command_sender
            .send(RemoteCommand::DeleteContext(context.label))?;
        Ok(())
    }

    pub async fn delete_solver(
        &self,
        solver: RemoteSolver,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker
            .command_sender
            .send(RemoteCommand::DeleteSolver(solver.label))?;
        Ok(())
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum RemoteCommand {
    NewContext(),
    NewSolver(ContextLabel),
    NewSolverWithOptions(ContextLabel, Options),
    DeleteContext(ContextLabel),
    DeleteSolver(SolverLabel),
    Reset(SolverLabel),
    Assert(SolverLabel, Term),
    CheckSat(SolverLabel),
}

#[derive(PartialEq, Eq, Hash, Serialize, Deserialize, Debug, Clone, Copy)]
pub enum RemoteState {
    Busy,
    Idle,
}

#[derive(PartialEq, Eq, Hash, Serialize, Deserialize, Debug, Clone, Copy)]
pub struct SolverLabel(pub u64);

#[derive(PartialEq, Eq, Hash, Serialize, Deserialize, Debug, Clone, Copy)]
pub struct ContextLabel(pub u64);

#[derive(PartialEq, Eq, Hash, Serialize, Deserialize, Debug, Clone, Copy)]
pub struct OptionsLabel(pub u64);

#[derive(Debug)]
pub struct RemoteSolver {
    label: SolverLabel,
    worker: Rc<RemoteWorker>,
}

#[derive(Serialize, Deserialize, Debug)]
struct SolverError {
    message: String,
}

impl fmt::Display for SolverError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl RemoteSolver {
    pub async fn assert(
        &self,
        term: &Term,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker
            .command_sender
            .send(RemoteCommand::Assert(self.label, term.clone()))?;
        Ok(())
    }

    pub async fn reset(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker
            .command_sender
            .send(RemoteCommand::Reset(self.label))?;
        Ok(())
    }

    pub async fn interrupt(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.interrupt_sender.send(self.label)?;
        Ok(())
    }

    pub async fn check_sat(
        &self,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        self.worker
            .command_sender
            .send(RemoteCommand::CheckSat(self.label))?;
        let command_response = self.worker.solver_result_receiver.recv()?;
        Ok(command_response)
    }
}

#[derive(Debug)]
pub struct RemoteContext {
    label: ContextLabel,
}

impl RemoteContext {}

#[derive(Serialize, Deserialize, Debug)]
pub struct RemoteWorker {
    pub command_sender: IpcSender<RemoteCommand>,
    pub interrupt_sender: IpcSender<SolverLabel>,
    pub check_state_sender: IpcSender<()>,
    pub state_receiver: IpcReceiver<RemoteState>,
    pub new_solver_receiver: IpcReceiver<SolverLabel>,
    pub new_context_receiver: IpcReceiver<ContextLabel>,
    pub new_options_receiver: IpcReceiver<OptionsLabel>,
    pub solver_result_receiver: IpcReceiver<SolverResult>,
}

impl RemoteSolver {
    pub async fn cancellable_check_sat(
        &self,
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

pub struct SmithrilFactory {
    factories: Vec<RemoteFactory>,
}

fn get_solver_path(solver_name: &str) -> PathBuf {
    get_converters_dir().join(solver_name)
}

fn get_converters_dir() -> PathBuf {
    std::env::var("SMITHRIL_CONVERTERS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| panic!("SMITHRIL_CONVERTERS_DIR environment variable is not set"))
}

impl SmithrilFactory {
    pub async fn new(converters: Vec<Converter>) -> Self {
        let solver_path = get_solver_path("smithril-runner");
        let solver_path_string = solver_path.to_string_lossy().into_owned();
        let mut factories: Vec<RemoteFactory> = Default::default();

        for converter in &converters {
            let solver_process = RemoteFactory::new(&solver_path_string, converter)
                .await
                .unwrap();
            factories.push(solver_process);
        }
        Self { factories }
    }

    pub async fn terminate(&mut self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        for solver in self.factories.iter_mut() {
            solver.terminate().await?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct SmithrilContext {
    contexts: Vec<RemoteContext>,
}

#[derive(Debug)]
pub struct SmithrilSolver {
    solvers: Vec<RemoteSolver>,
}

impl SmithrilFactory {
    pub async fn new_context(&self) -> Rc<SmithrilContext> {
        let mut handles = Vec::new();
        for factory in self.factories.iter() {
            let handler = factory.new_context();
            handles.push(handler);
        }
        let mut contexts = Vec::new();
        for handler in handles {
            contexts.push(handler.await.unwrap());
        }
        Rc::new(SmithrilContext { contexts })
    }

    pub async fn delete_context(&self, context: Rc<SmithrilContext>) {
        assert_eq!(Rc::strong_count(&context), 1);
        let context = Rc::try_unwrap(context).unwrap();
        let mut handles = Vec::new();
        for (factory, context) in self.factories.iter().zip(context.contexts.into_iter()) {
            let handler = factory.delete_context(context);
            handles.push(handler);
        }
        for handler in handles {
            handler.await.unwrap();
        }
    }

    pub async fn new_solver(&self, context: Rc<SmithrilContext>) -> Rc<SmithrilSolver> {
        let mut handles = Vec::new();
        for (factory, context) in self.factories.iter().zip(context.contexts.iter()) {
            let handler = factory.new_solver(context);
            handles.push(handler);
        }
        let mut solvers = Vec::new();
        for handler in handles {
            solvers.push(handler.await.unwrap());
        }
        Rc::new(SmithrilSolver { solvers })
    }

    pub async fn delete_solver(&self, solver: Rc<SmithrilSolver>) {
        assert_eq!(Rc::strong_count(&solver), 1);
        let solver = Rc::try_unwrap(solver).unwrap();
        let mut handles = Vec::new();
        for (factory, solver) in self.factories.iter().zip(solver.solvers.into_iter()) {
            let handler = factory.delete_solver(solver);
            handles.push(handler);
        }
        for handler in handles {
            handler.await.unwrap();
        }
    }
}

impl SmithrilSolver {
    pub async fn assert(
        &self,
        term: &Term,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut handles = Vec::new();
        for solver in self.solvers.iter() {
            let handler = solver.assert(term);
            handles.push(handler);
        }
        for handler in handles {
            handler.await.unwrap();
        }
        Ok(())
    }

    pub async fn reset(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut handles = Vec::new();
        for solver in self.solvers.iter() {
            let handler = solver.reset();
            handles.push(handler);
        }
        for handler in handles {
            handler.await.unwrap();
        }
        Ok(())
    }

    pub async fn interrupt(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut handles = Vec::new();
        for solver in self.solvers.iter() {
            let handler = solver.interrupt();
            handles.push(handler);
        }
        for handler in handles {
            handler.await.unwrap();
        }
        Ok(())
    }

    pub async fn check_sat(
        &self,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        let mut handles = Vec::new();
        let token = CancellationToken::new();
        for solver in self.solvers.iter() {
            let handler = solver.cancellable_check_sat(token.clone());
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
async fn smithril_test() {
    use std::env;
    let mut smithril_converters_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    smithril_converters_dir.push("../target/debug");
    let smithril_converters_path = env::join_paths(vec![smithril_converters_dir]).unwrap();
    unsafe {
        env::set_var("SMITHRIL_CONVERTERS_DIR", smithril_converters_path);
    }

    let converters = vec![Converter::Bitwuzla, Converter::Z3];
    let t = sat_works();

    let mut factory = SmithrilFactory::new(converters.clone()).await;
    let context = factory.new_context().await;
    let solver = factory.new_solver(context).await;
    solver.assert(&t).await.unwrap();
    let status = solver.check_sat().await.unwrap();
    assert_eq!(SolverResult::Sat, status);
    solver.reset().await.unwrap();

    let t = unsat_works();

    solver.assert(&t).await.unwrap();
    let status = solver.check_sat().await.unwrap();
    assert_eq!(SolverResult::Unsat, status);
    solver.reset().await.unwrap();

    factory.terminate().await.unwrap();
}
