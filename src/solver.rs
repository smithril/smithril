use futures::channel::oneshot;
use futures::stream::FuturesUnordered;
use futures::StreamExt;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt::{self, Debug, Display};
use std::hash::Hash;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, RwLock};
use std::time::Duration;

use ipc_channel::ipc::{IpcOneShotServer, IpcReceiver, IpcSender};
use tokio::process::{Child, Command};
use tokio::select;
use tokio_util::sync::CancellationToken;

use crate::converters::Converter;
use crate::generalized::{
    AsyncContext, AsyncFactory, AsyncResultFactory, AsyncResultSolver, AsyncSolver, Options,
    SolverResult,
};
use crate::term::Term;

pub struct RemoteFactory {
    worker: Arc<RemoteWorker>,
}

impl RemoteFactory {
    pub async fn new(
        solver_path: &str,
        converter: &Converter,
    ) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let context_id = 0u64;
        let solver_id = 0u64;

        Ok(RemoteFactory {
            worker: Arc::new(
                RemoteWorker::new(solver_path, converter, context_id, solver_id).await?,
            ),
        })
    }
}

impl AsyncResultFactory<RemoteContext, RemoteSolver> for RemoteFactory {
    async fn terminate(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.terminate().await?;
        Ok(())
    }

    async fn new_context(&self) -> Result<RemoteContext, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.worker.new_context().await?;
        let command_response = RemoteContext {
            label: command_response,
        };
        Ok(command_response)
    }

    async fn new_solver(
        &self,
        context: &RemoteContext,
        options: &Options,
    ) -> Result<Arc<RemoteSolver>, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.worker.new_solver(context.label, options).await?;
        let command_response = RemoteSolver {
            label: command_response,
            worker: self.worker.clone(),
            context: context.label,
            timeout: options.external_timeout,
        };
        let command_response = Arc::new(command_response);
        Ok(command_response)
    }

    async fn delete_context(
        &self,
        context: RemoteContext,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.delete_context(context.label).await?;
        Ok(())
    }

    async fn delete_solver(
        &self,
        solver: Arc<RemoteSolver>,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker
            .delete_solver(solver.context, solver.label)
            .await?;
        Ok(())
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum RemoteSolverCommand {
    Assert(SolverLabel, Term),
    Reset(SolverLabel),
    CheckSat(SolverLabel),
    UnsatCore(SolverLabel),
    Eval(SolverLabel, Term),
    Push(SolverLabel),
    Pop(SolverLabel, u64),
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum RemoteFactoryCommand {
    DeleteContext(ContextLabel),
    DeleteSolver(SolverLabel),
    NewContext(),
    NewSolver(ContextLabel, Options),
    RestoreContext(ContextLabel),
    RestoreSolver(ContextLabel, SolverLabel, Options),
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum RemoteCommand {
    Solver(RemoteSolverCommand),
    Factory(RemoteFactoryCommand),
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

#[derive(Debug)]
pub struct RemoteSolver {
    context: ContextLabel,
    label: SolverLabel,
    timeout: Option<Duration>,
    worker: Arc<RemoteWorker>,
}

impl PartialEq for RemoteSolver {
    fn eq(&self, other: &Self) -> bool {
        self.context == other.context && self.label == other.label && self.timeout == other.timeout
    }
}

impl Eq for RemoteSolver {}

impl Hash for RemoteSolver {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.context.hash(state);
        self.label.hash(state);
        self.timeout.hash(state);
    }
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

impl AsyncResultSolver for RemoteSolver {
    async fn assert(&self, term: &Term) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.assert(self.label, term).await?;
        Ok(())
    }

    async fn reset(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.reset(self.label).await?;
        Ok(())
    }

    async fn interrupt(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.interrupt(self.label).await?;
        Ok(())
    }

    async fn check_sat(&self) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.worker.check_sat(self.label).await?;
        Ok(command_response)
    }

    async fn unsat_core(&self) -> Result<Vec<Term>, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.worker.unsat_core(self.label).await?;
        Ok(command_response)
    }

    async fn eval(
        &self,
        term: &Term,
    ) -> Result<Option<Term>, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.worker.eval(self.label, term).await?;
        Ok(command_response)
    }

    async fn push(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.push(self.label).await?;
        Ok(())
    }

    async fn pop(&self, size: u64) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.pop(self.label, size).await?;
        Ok(())
    }
}

impl RemoteSolver {}

#[derive(Hash, PartialEq, Eq, Debug)]
pub struct RemoteContext {
    label: ContextLabel,
}

impl AsyncContext for RemoteContext {}

#[derive(Debug)]
pub struct RemoteWorker {
    solver_path: String,
    converter: Converter,
    context_id: RwLock<u64>,
    solver_id: RwLock<u64>,
    process: RwLock<Child>,
    count_communication: Mutex<u64>,
    is_alive: Mutex<bool>,
    active_contexts: RwLock<HashSet<ContextLabel>>,
    active_solvers: RwLock<HashSet<(ContextLabel, SolverLabel)>>,
    solver_commands: RwLock<HashMap<SolverLabel, Vec<RemoteSolverCommand>>>,
    postponed_commands: RwLock<Vec<RemoteCommand>>,
    solver_options: RwLock<HashMap<SolverLabel, Options>>,
    communicator: tokio::sync::RwLock<RemoteWorkerLockingCommunicator>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct RemoteWorkerCommunicator {
    pub command_sender: IpcSender<RemoteCommand>,
    pub interrupt_sender: IpcSender<SolverLabel>,
    pub check_state_sender: IpcSender<()>,
    pub state_receiver: IpcReceiver<RemoteState>,
    pub new_solver_receiver: IpcReceiver<SolverLabel>,
    pub new_context_receiver: IpcReceiver<ContextLabel>,
    pub solver_result_receiver: IpcReceiver<SolverResult>,
    pub confirmation_receiver: IpcReceiver<()>,
    pub eval_receiver: IpcReceiver<Option<Term>>,
    pub unsat_core_receiver: IpcReceiver<Vec<Term>>,
}

#[derive(Debug)]
pub struct RemoteWorkerLockingCommunicator {
    command_sender: Mutex<IpcSender<RemoteCommand>>,
    interrupt_sender: Mutex<IpcSender<SolverLabel>>,
    check_state_sender: Mutex<IpcSender<()>>,
    state_receiver: Mutex<IpcReceiver<RemoteState>>,
    new_solver_receiver: Mutex<IpcReceiver<SolverLabel>>,
    new_context_receiver: Mutex<IpcReceiver<ContextLabel>>,
    solver_result_receiver: Mutex<IpcReceiver<SolverResult>>,
    confirmation_receiver: Mutex<IpcReceiver<()>>,
    pub eval_receiver: Mutex<IpcReceiver<Option<Term>>>,
    pub unsat_core_receiver: Mutex<IpcReceiver<Vec<Term>>>,
}

impl RemoteWorkerLockingCommunicator {
    pub fn new(communicator: RemoteWorkerCommunicator) -> Self {
        Self {
            command_sender: Mutex::new(communicator.command_sender),
            interrupt_sender: Mutex::new(communicator.interrupt_sender),
            check_state_sender: Mutex::new(communicator.check_state_sender),
            state_receiver: Mutex::new(communicator.state_receiver),
            new_solver_receiver: Mutex::new(communicator.new_solver_receiver),
            new_context_receiver: Mutex::new(communicator.new_context_receiver),
            solver_result_receiver: Mutex::new(communicator.solver_result_receiver),
            confirmation_receiver: Mutex::new(communicator.confirmation_receiver),
            eval_receiver: Mutex::new(communicator.eval_receiver),
            unsat_core_receiver: Mutex::new(communicator.unsat_core_receiver),
        }
    }

    async fn send_factory_command(
        &self,
        command: RemoteFactoryCommand,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.command_sender
            .lock()
            .unwrap()
            .send(RemoteCommand::Factory(command))?;
        Ok(())
    }

    async fn send_solver_command(
        &self,
        command: RemoteSolverCommand,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.command_sender
            .lock()
            .unwrap()
            .send(RemoteCommand::Solver(command))?;
        Ok(())
    }

    pub async fn new_context(
        &self,
    ) -> Result<ContextLabel, Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::NewContext())
            .await?;
        let command_response = self.new_context_receiver.lock().unwrap().recv()?;
        Ok(command_response)
    }

    pub async fn new_solver(
        &self,
        context: ContextLabel,
        options: &Options,
    ) -> Result<SolverLabel, Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::NewSolver(context, options.clone()))
            .await?;
        let command_response = self.new_solver_receiver.lock().unwrap().recv()?;
        Ok(command_response)
    }

    pub async fn restore_context(
        &self,
        context: ContextLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::RestoreContext(context))
            .await?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    pub async fn restore_solver(
        &self,
        context: ContextLabel,
        solver: SolverLabel,
        options: &Options,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::RestoreSolver(
            context,
            solver,
            options.clone(),
        ))
        .await?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    pub async fn delete_context(
        &self,
        context: ContextLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::DeleteContext(context))
            .await?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    pub async fn delete_solver(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::DeleteSolver(solver))
            .await?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    pub async fn assert(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Assert(solver, term.clone());
        self.send_solver_command(command).await?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    pub async fn reset(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Reset(solver);
        self.send_solver_command(command).await?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    pub async fn interrupt(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.interrupt_sender.lock().unwrap().send(solver)?;
        Ok(())
    }

    pub async fn check_sat(
        &self,
        solver: SolverLabel,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::CheckSat(solver);
        self.send_solver_command(command).await?;
        let command_response = self.solver_result_receiver.lock().unwrap().recv()?;
        Ok(command_response)
    }

    pub async fn eval(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<Option<Term>, Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Eval(solver, term.clone());
        self.send_solver_command(command).await?;
        let command_response = self.eval_receiver.lock().unwrap().recv()?;
        Ok(command_response)
    }

    pub async fn unsat_core(
        &self,
        solver: SolverLabel,
    ) -> Result<Vec<Term>, Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::UnsatCore(solver);
        self.send_solver_command(command).await?;
        let command_response = self.unsat_core_receiver.lock().unwrap().recv()?;
        Ok(command_response)
    }

    pub async fn check_state(
        &self,
    ) -> Result<RemoteState, Box<dyn std::error::Error + Send + Sync>> {
        let state = {
            self.check_state_sender.lock().unwrap().send(())?;
            self.state_receiver.lock().unwrap().recv()?
        };
        Ok(state)
    }

    pub async fn push(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Push(solver);
        self.send_solver_command(command).await?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    pub async fn pop(
        &self,
        solver: SolverLabel,
        size: u64,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Pop(solver, size);
        self.send_solver_command(command).await?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }
}

#[derive(Debug)]
pub struct WorkerError {}
impl Display for WorkerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Worker error!")
    }
}

impl Error for WorkerError {}

impl RemoteWorker {
    pub async fn new(
        solver_path: &str,
        converter: &Converter,
        context_id: u64,
        solver_id: u64,
    ) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let (process, communicator) =
            RemoteWorker::start_process(converter, context_id, solver_id, solver_path).await?;
        let process = RwLock::new(process);
        let communicator = RemoteWorkerLockingCommunicator::new(communicator);
        let communicator = tokio::sync::RwLock::new(communicator);
        let solver_path = solver_path.to_string();
        let converter = converter.clone();
        let context_id = RwLock::new(context_id);
        let solver_id = RwLock::new(solver_id);
        let count_ready = Mutex::new(0);
        let is_alive = Mutex::new(true);

        Ok(RemoteWorker {
            process,
            communicator,
            active_contexts: Default::default(),
            active_solvers: Default::default(),
            solver_commands: Default::default(),
            solver_options: Default::default(),
            postponed_commands: Default::default(),
            solver_path,
            converter,
            context_id,
            solver_id,
            count_communication: count_ready,
            is_alive,
        })
    }

    async fn start_process(
        converter: &Converter,
        context_id: u64,
        solver_id: u64,
        solver_path: &str,
    ) -> Result<(Child, RemoteWorkerCommunicator), Box<dyn std::error::Error + Send + Sync>> {
        let (one_shot_server, one_shot_server_name) = IpcOneShotServer::new().unwrap();
        let serialized_converter = serde_json::to_string(converter).unwrap();
        let serialized_context_solver_id = serde_json::to_string(&(context_id, solver_id)).unwrap();
        let process = Command::new(solver_path)
            .arg(one_shot_server_name)
            .arg(serialized_converter)
            .arg(serialized_context_solver_id)
            .spawn()?;
        let (_, communicator) = one_shot_server.accept().unwrap();
        Ok((process, communicator))
    }

    async fn resend_command(
        &self,
        command: RemoteCommand,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        match command {
            RemoteCommand::Solver(command) => match command {
                RemoteSolverCommand::Assert(solver, term) => {
                    self.communicator().await.assert(solver, &term).await?;
                }
                RemoteSolverCommand::Reset(solver) => {
                    self.communicator().await.reset(solver).await?;
                }
                RemoteSolverCommand::CheckSat(solver) => {
                    let _ = self.communicator().await.check_sat(solver).await?;
                }
                RemoteSolverCommand::UnsatCore(solver) => {
                    let _ = self.communicator().await.unsat_core(solver).await?;
                }
                RemoteSolverCommand::Eval(solver, term) => {
                    let _ = self.communicator().await.eval(solver, &term).await?;
                }
                RemoteSolverCommand::Push(solver) => {
                    self.communicator().await.push(solver).await?;
                }
                RemoteSolverCommand::Pop(solver, size) => {
                    self.communicator().await.pop(solver, size).await?;
                }
            },
            RemoteCommand::Factory(command) => match command {
                RemoteFactoryCommand::DeleteContext(context) => {
                    self.communicator().await.delete_context(context).await?;
                }
                RemoteFactoryCommand::DeleteSolver(solver) => {
                    self.communicator().await.delete_solver(solver).await?;
                }
                RemoteFactoryCommand::NewContext() => {
                    let _ = self.communicator().await.new_context().await?;
                }
                RemoteFactoryCommand::NewSolver(context, options) => {
                    let _ = self
                        .communicator()
                        .await
                        .new_solver(context, &options)
                        .await?;
                }
                RemoteFactoryCommand::RestoreContext(context) => {
                    self.communicator().await.restore_context(context).await?;
                }
                RemoteFactoryCommand::RestoreSolver(context, solver, options) => {
                    self.communicator()
                        .await
                        .restore_solver(context, solver, &options)
                        .await?;
                }
            },
        }
        Ok(())
    }

    pub async fn restart(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        if !*self.is_alive.lock().unwrap() {
            return Ok(());
        }
        self.wait_zero_communication_to_lock_is_alive();
        self.terminate().await?;
        let context_id = *self.context_id.read().unwrap();
        let solver_id = *self.solver_id.read().unwrap();
        let (process, communicator) = RemoteWorker::start_process(
            &self.converter,
            context_id,
            solver_id,
            self.solver_path.as_str(),
        )
        .await?;
        let communicator = RemoteWorkerLockingCommunicator::new(communicator);
        {
            *self.process.write().unwrap() = process;
            *self.communicator.write().await = communicator;
        }
        let contexts: Vec<_> = self
            .active_contexts
            .read()
            .unwrap()
            .iter()
            .cloned()
            .collect();
        for context in contexts {
            self.resend_command(RemoteCommand::Factory(
                RemoteFactoryCommand::RestoreContext(context),
            ))
            .await?;
        }
        let solvers: Vec<_> = self
            .active_solvers
            .read()
            .unwrap()
            .iter()
            .cloned()
            .collect();
        for (context, solver) in solvers {
            let option = {
                self.solver_options
                    .read()
                    .unwrap()
                    .get(&solver)
                    .unwrap()
                    .clone()
            };
            let command = RemoteCommand::Factory(RemoteFactoryCommand::RestoreSolver(
                context, solver, option,
            ));
            self.resend_command(command).await?;
        }
        let solver_commands = { self.solver_commands.read().unwrap().clone() };

        for (_, commands) in solver_commands {
            for command in commands {
                let command = RemoteCommand::Solver(command.clone());
                self.resend_command(command).await?;
            }
        }
        {
            self.postponed_commands.write().unwrap().clear();
        }
        {
            *self.is_alive.lock().unwrap() = true;
        }
        Ok(())
    }

    fn wait_zero_communication_to_lock_is_alive(&self) {
        loop {
            let lock = self.count_communication.lock().unwrap();
            if *lock == 0 {
                *self.is_alive.lock().unwrap() = false;
                break;
            }
        }
    }

    fn inc_communication(&self) {
        loop {
            let lock = self.is_alive.lock().unwrap();
            if *lock {
                *self.count_communication.lock().unwrap() += 1;
                break;
            }
        }
    }

    fn dec_communication(&self) {
        loop {
            let lock = self.is_alive.lock().unwrap();
            if *lock {
                *self.count_communication.lock().unwrap() -= 1;
                break;
            }
        }
    }

    pub async fn check_state(
        &self,
    ) -> Result<RemoteState, Box<dyn std::error::Error + Send + Sync>> {
        self.inc_communication();
        let state = self.communicator().await.check_state().await?;
        self.dec_communication();
        Ok(state)
    }

    pub async fn terminate(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        {
            self.process.write().unwrap().start_kill()?;
        }
        Ok(())
    }

    async fn communicator(&self) -> tokio::sync::RwLockReadGuard<RemoteWorkerLockingCommunicator> {
        self.communicator.read().await
    }

    async fn save_solver_command(
        &self,
        solver_label: SolverLabel,
        command: RemoteSolverCommand,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.solver_commands
            .write()
            .unwrap()
            .entry(solver_label)
            .or_default()
            .push(command.clone());
        Ok(())
    }

    async fn try_resend_postponed_commands(
        &self,
    ) -> Result<bool, Box<dyn std::error::Error + Send + Sync>> {
        let state = self.check_state().await?;
        match state {
            RemoteState::Busy => Ok(false),
            RemoteState::Idle => {
                let postponed_commands = { self.postponed_commands.read().unwrap() }.clone();
                if !postponed_commands.is_empty() {
                    for command in postponed_commands.into_iter() {
                        self.resend_command(command).await?;
                    }
                    self.postponed_commands.write().unwrap().clear();
                }
                Ok(true)
            }
        }
    }

    fn postpone_command(&self, command: RemoteCommand) {
        self.postponed_commands.write().unwrap().push(command);
    }

    pub async fn new_context(
        &self,
    ) -> Result<ContextLabel, Box<dyn std::error::Error + Send + Sync>> {
        {
            *self.context_id.write().unwrap() += 1;
        }
        let command_response = if !self.try_resend_postponed_commands().await? {
            self.postpone_command(RemoteCommand::Factory(RemoteFactoryCommand::NewContext()));
            let context_id = { *self.context_id.read().unwrap() };
            ContextLabel(context_id)
        } else {
            self.inc_communication();
            let context = self.communicator().await.new_context().await?;
            self.dec_communication();
            context
        };

        self.active_contexts
            .write()
            .unwrap()
            .insert(command_response);
        Ok(command_response)
    }

    pub async fn new_solver(
        &self,
        context: ContextLabel,
        options: &Options,
    ) -> Result<SolverLabel, Box<dyn std::error::Error + Send + Sync>> {
        {
            *self.solver_id.write().unwrap() += 1;
        }
        let command_response = if !self.try_resend_postponed_commands().await? {
            self.postpone_command(RemoteCommand::Factory(RemoteFactoryCommand::NewSolver(
                context,
                options.clone(),
            )));
            let solver_id = { *self.solver_id.read().unwrap() };
            SolverLabel(solver_id)
        } else {
            self.inc_communication();
            let solver = self
                .communicator()
                .await
                .new_solver(context, options)
                .await?;
            self.dec_communication();
            solver
        };
        self.active_solvers
            .write()
            .unwrap()
            .insert((context, command_response));
        self.solver_options
            .write()
            .unwrap()
            .insert(command_response, options.clone());
        Ok(command_response)
    }

    pub async fn delete_context(
        &self,
        context: ContextLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        if !self.try_resend_postponed_commands().await? {
            self.postpone_command(RemoteCommand::Factory(RemoteFactoryCommand::DeleteContext(
                context,
            )));
        } else {
            self.inc_communication();
            self.communicator().await.delete_context(context).await?;
            self.dec_communication();
        };
        self.active_contexts.write().unwrap().remove(&context);
        Ok(())
    }

    pub async fn delete_solver(
        &self,
        context: ContextLabel,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        if !self.try_resend_postponed_commands().await? {
            self.postpone_command(RemoteCommand::Factory(RemoteFactoryCommand::DeleteSolver(
                solver,
            )));
        } else {
            self.inc_communication();
            self.communicator().await.delete_solver(solver).await?;
            self.dec_communication();
        };
        self.active_solvers
            .write()
            .unwrap()
            .remove(&(context, solver));
        self.solver_commands.write().unwrap().remove(&solver);
        self.solver_options.write().unwrap().remove(&solver);
        Ok(())
    }

    pub async fn assert(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Assert(solver, term.clone());
        self.save_solver_command(solver, command.clone()).await?;
        if !self.try_resend_postponed_commands().await? {
            self.postpone_command(RemoteCommand::Solver(command));
        } else {
            self.inc_communication();
            self.communicator().await.assert(solver, term).await?;
            self.dec_communication();
        };
        Ok(())
    }

    pub async fn reset(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Reset(solver);
        self.save_solver_command(solver, command.clone()).await?;
        if !self.try_resend_postponed_commands().await? {
            self.postpone_command(RemoteCommand::Solver(command));
        } else {
            self.inc_communication();
            self.communicator().await.reset(solver).await?;
            self.dec_communication();
        };
        Ok(())
    }

    pub async fn eval(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<Option<Term>, Box<dyn std::error::Error + Send + Sync>> {
        if !self.try_resend_postponed_commands().await? {
            Err(Box::new(WorkerError {}))
        } else {
            self.inc_communication();
            let command_response = self.communicator().await.eval(solver, term).await?;
            self.dec_communication();
            Ok(command_response)
        }
    }

    pub async fn unsat_core(
        &self,
        solver: SolverLabel,
    ) -> Result<Vec<Term>, Box<dyn std::error::Error + Send + Sync>> {
        if !self.try_resend_postponed_commands().await? {
            Err(Box::new(WorkerError {}))
        } else {
            self.inc_communication();
            let command_response = self.communicator().await.unsat_core(solver).await?;
            self.dec_communication();
            Ok(command_response)
        }
    }

    pub async fn interrupt(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        if *self.is_alive.lock().unwrap() {
            self.communicator().await.interrupt(solver).await?;
        }
        Ok(())
    }

    pub async fn check_sat(
        &self,
        solver: SolverLabel,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        if !self.try_resend_postponed_commands().await? {
            self.restart().await?;
        }
        let command_response = self.communicator().await.check_sat(solver).await?;
        Ok(command_response)
    }

    pub async fn push(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Push(solver);
        self.save_solver_command(solver, command.clone()).await?;
        if !self.try_resend_postponed_commands().await? {
            self.postpone_command(RemoteCommand::Solver(command));
        } else {
            self.inc_communication();
            self.communicator().await.push(solver).await?;
            self.dec_communication();
        };
        Ok(())
    }

    pub async fn pop(
        &self,
        solver: SolverLabel,
        size: u64,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Pop(solver, size);
        self.save_solver_command(solver, command.clone()).await?;
        if !self.try_resend_postponed_commands().await? {
            self.postpone_command(RemoteCommand::Solver(command));
        } else {
            self.inc_communication();
            self.communicator().await.pop(solver, size).await?;
            self.dec_communication();
        };
        Ok(())
    }
}

impl RemoteSolver {
    pub async fn cancellabel_check_sat(
        s: Arc<Self>,
        token: CancellationToken,
        id: usize,
    ) -> Result<(SolverResult, usize), Box<dyn std::error::Error + Send + Sync>> {
        let (tx_cancell, rx_cancell) = oneshot::channel();

        {
            let s = s.clone();
            tokio::spawn(async move {
                let (tx_token, rx_token) = oneshot::channel();
                tokio::spawn(async move {
                    token.cancelled().await;
                    let _ = tx_token.send(());
                });
                if let Some(timeout) = s.timeout {
                    let (tx_timeout, rx_timeout) = oneshot::channel();
                    tokio::spawn(async move {
                        tokio::time::sleep(timeout).await;
                        let _ = tx_timeout.send(());
                    });
                    select! {
                        _  = rx_timeout => {
                            let _ = tx_cancell.send(());
                        }
                        _ = rx_token => {
                            let _ = tx_cancell.send(());
                        }
                    }
                } else {
                    rx_token.await.unwrap();
                    let _ = tx_cancell.send(());
                }
            });
        }

        let (tx_check_sat, rx_check_sat) = oneshot::channel();
        {
            let s = s.clone();

            tokio::spawn(async move {
                let res = s.check_sat().await;
                let _ = tx_check_sat.send(res);
            });
        }
        select! {
            _  =  rx_cancell => {
                s.interrupt().await?;
                Ok((SolverResult::Unknown, id))
            }
            res = rx_check_sat => {
                let res = res??;
                Ok((res, id))
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
    let mut smithril_converters_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    if cfg!(debug_assertions) {
        smithril_converters_dir.push("target/debug");
    } else {
        smithril_converters_dir.push("target/release");
    }
    smithril_converters_dir
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
}

#[derive(Hash, PartialEq, Eq, Debug)]
pub struct SmithrilContext {
    contexts: Vec<RemoteContext>,
}

impl AsyncContext for SmithrilContext {}

#[derive(Debug)]
pub struct SmithrilSolver {
    solvers: Vec<Arc<RemoteSolver>>,
    last_fastest_solver_index: RwLock<usize>,
}

impl PartialEq for SmithrilSolver {
    fn eq(&self, other: &Self) -> bool {
        self.solvers.eq(&other.solvers)
    }
}

impl Eq for SmithrilSolver {}

impl Hash for SmithrilSolver {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.solvers.hash(state);
    }
}

impl AsyncFactory<SmithrilContext, SmithrilSolver> for SmithrilFactory {
    async fn terminate(&self) {
        for solver in self.factories.iter() {
            solver.terminate().await.unwrap();
        }
    }

    async fn new_context(&self) -> Arc<SmithrilContext> {
        let mut handles = Vec::new();
        for factory in self.factories.iter() {
            let handler = factory.new_context();
            handles.push(handler);
        }
        let mut contexts = Vec::new();
        for handler in handles {
            contexts.push(handler.await.unwrap());
        }
        Arc::new(SmithrilContext { contexts })
    }

    async fn delete_context(&self, context: Arc<SmithrilContext>) {
        assert_eq!(Arc::strong_count(&context), 1);
        let context = Arc::try_unwrap(context).unwrap();
        let mut handles = Vec::new();
        for (factory, context) in self.factories.iter().zip(context.contexts.into_iter()) {
            let handler = factory.delete_context(context);
            handles.push(handler);
        }
        for handler in handles {
            handler.await.unwrap();
        }
    }

    async fn new_solver(
        &self,
        context: Arc<SmithrilContext>,
        options: &Options,
    ) -> Arc<SmithrilSolver> {
        let mut handles = Vec::new();
        for (factory, context) in self.factories.iter().zip(context.contexts.iter()) {
            let handler = factory.new_solver(context, options);
            handles.push(handler);
        }
        let mut solvers = Vec::new();
        for handler in handles {
            solvers.push(handler.await.unwrap());
        }
        Arc::new(SmithrilSolver {
            solvers,
            last_fastest_solver_index: RwLock::new(Default::default()),
        })
    }

    async fn delete_solver(&self, solver: Arc<SmithrilSolver>) {
        assert_eq!(Arc::strong_count(&solver), 1);
        let mut handles = Vec::new();
        {
            let solver = Arc::try_unwrap(solver).ok().unwrap();
            let solvers = solver.solvers;
            for (factory, solver) in self.factories.iter().zip(solvers.into_iter()) {
                let handler = factory.delete_solver(solver);
                handles.push(handler);
            }
        }
        for handler in handles {
            handler.await.unwrap();
        }
    }
}

impl AsyncSolver for SmithrilSolver {
    async fn assert(&self, term: &Term) {
        let mut handles = Vec::new();
        for solver in self.solvers.iter() {
            let handler = solver.assert(term);
            handles.push(handler);
        }
        for handler in handles {
            handler.await.unwrap();
        }
    }

    async fn reset(&self) {
        let mut handles = Vec::new();
        for solver in self.solvers.iter() {
            let handler = solver.reset();
            handles.push(handler);
        }
        for handler in handles {
            handler.await.unwrap();
        }
    }

    async fn interrupt(&self) {
        let mut handles = Vec::new();
        for solver in self.solvers.iter() {
            let handler = solver.interrupt();
            handles.push(handler);
        }
        for handler in handles {
            handler.await.unwrap();
        }
    }

    async fn check_sat(&self) -> SolverResult {
        let mut handles = Vec::new();
        let token = CancellationToken::new();
        for (count, solver) in self.solvers.iter().enumerate() {
            let handler = RemoteSolver::cancellabel_check_sat(solver.clone(), token.clone(), count);
            handles.push(handler);
        }
        let mut futs = handles.into_iter().collect::<FuturesUnordered<_>>();

        let mut result = SolverResult::Unknown;
        while let Some(res) = futs.next().await {
            let (res, count) = res.unwrap();
            if SolverResult::Unknown == res {
                continue;
            }
            token.cancel();
            *self.last_fastest_solver_index.write().unwrap() = count;
            result = res;
            break;
        }
        while let Some(_) = futs.next().await {}
        result
    }

    async fn unsat_core(&self) -> Vec<Term> {
        let last_fastest_solver_index = { *self.last_fastest_solver_index.read().unwrap() };
        let solver = self.solvers.get(last_fastest_solver_index).unwrap();
        solver.unsat_core().await.unwrap()
    }

    async fn eval(&self, term: &Term) -> Option<Term> {
        let last_fastest_solver_index = { *self.last_fastest_solver_index.read().unwrap() };
        let solver = self.solvers.get(last_fastest_solver_index).unwrap();
        solver.eval(term).await.unwrap()
    }

    async fn push(&self) {
        let mut handles = Vec::new();
        for solver in self.solvers.iter() {
            let handler = solver.push();
            handles.push(handler);
        }
        for handler in handles {
            handler.await.unwrap();
        }
    }

    async fn pop(&self, size: u64) {
        let mut handles = Vec::new();
        for solver in self.solvers.iter() {
            let handler = solver.pop(size);
            handles.push(handler);
        }
        for handler in handles {
            handler.await.unwrap();
        }
    }
}

#[cfg(test)]
fn sat_works(seed: &str) -> Term {
    use crate::term::{self};

    let x_name = format!("x{}", seed).to_string();
    let bv_sort = term::mk_bv_sort(3);
    let x = term::mk_smt_symbol(&x_name, &bv_sort);
    let y = term::mk_bv_value_uint64(2, &bv_sort);
    term::mk_eq(&x, &y)
}

#[cfg(test)]
fn unsat_works() -> Term {
    use crate::term::{self};

    let bv_sort = term::mk_bv_sort(3);
    let x = term::mk_smt_symbol("x", &bv_sort);
    let y = term::mk_bv_value_uint64(2, &bv_sort);
    let eq = term::mk_eq(&x, &y);
    let n = term::mk_not(&eq);
    term::mk_and(&eq, &n)
}

#[tokio::test(flavor = "multi_thread")]
async fn smithril_working_test() {
    let converters = vec![Converter::Bitwuzla, Converter::Z3];
    let t = sat_works("");

    let factory = SmithrilFactory::new(converters.clone()).await;
    let context = factory.new_context().await;
    let solver = factory.new_solver(context, &Options::default()).await;
    solver.assert(&t).await;
    let status = solver.check_sat().await;
    assert_eq!(SolverResult::Sat, status);
    solver.reset().await;

    let t = unsat_works();

    solver.assert(&t).await;
    let status = solver.check_sat().await;
    assert_eq!(SolverResult::Unsat, status);
    solver.reset().await;

    factory.terminate().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn smithril_unsat_core_test() {
    let converters = vec![Converter::Bitwuzla, Converter::Z3];

    let factory = SmithrilFactory::new(converters.clone()).await;
    let context = factory.new_context().await;
    let mut options = Options::default();
    options.set_produce_unsat_core(true);
    let solver = factory.new_solver(context, &options).await;

    let t = unsat_works();

    solver.assert(&t).await;
    let status = solver.check_sat().await;
    assert_eq!(SolverResult::Unsat, status);
    let unsat_core = solver.unsat_core().await;
    assert_eq!(unsat_core.len(), 1);

    factory.terminate().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn smithril_timeout_test() {
    let converters = vec![Converter::Dummy];

    let factory = SmithrilFactory::new(converters.clone()).await;
    let context = factory.new_context().await;
    let mut options = Options::default();
    options.set_external_timeout(Some(Duration::from_nanos(1)));
    let solver = factory.new_solver(context, &options).await;
    for i in 0..1000 {
        let t = sat_works(&i.to_string());
        solver.assert(&t).await;
    }
    let status = solver.check_sat().await;
    assert_eq!(SolverResult::Unknown, status);

    factory.terminate().await;
}
