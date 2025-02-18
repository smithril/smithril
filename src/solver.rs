use crossbeam_channel::{unbounded, Receiver, Sender};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt::{self, Debug, Display};
use std::hash::Hash;
use std::process::{Child, Command};
use std::sync::{Arc, Mutex, RwLock};
use std::thread;
use std::time::Duration;

use crate::converters::Converter;
use crate::generalized::{
    AsyncContext, AsyncFactory, AsyncSolver, Options, ResultFactory, ResultSolver, SolverResult,
};
use crate::runner;
use crate::term::Term;
use ipc_channel::ipc::{IpcOneShotServer, IpcReceiver, IpcSender};

pub struct RemoteFactory<T: WorkerCommunicator> {
    worker: Arc<RemoteWorker<T>>,
}

impl<T: WorkerCommunicator> RemoteFactory<T> {
    pub fn new(converter: &Converter) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let context_id = 0u64;
        let solver_id = 0u64;

        Ok(RemoteFactory {
            worker: Arc::new(RemoteWorker::new(converter, context_id, solver_id)?),
        })
    }
}

impl<T: WorkerCommunicator> ResultFactory<RemoteContext, RemoteSolver<T>> for RemoteFactory<T> {
    fn new_context(&self) -> Result<RemoteContext, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.worker.new_context()?;
        let command_response = RemoteContext {
            label: command_response,
        };
        Ok(command_response)
    }

    fn new_solver(
        &self,
        context: &RemoteContext,
        options: &Options,
    ) -> Result<Arc<RemoteSolver<T>>, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.worker.new_solver(context.label, options)?;
        let command_response = RemoteSolver {
            label: command_response,
            worker: self.worker.clone(),
            context: context.label,
            timeout: options.external_timeout,
        };
        let command_response = Arc::new(command_response);
        Ok(command_response)
    }

    fn delete_context(
        &self,
        context: RemoteContext,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.delete_context(context.label)?;
        Ok(())
    }

    fn delete_solver(
        &self,
        solver: Arc<RemoteSolver<T>>,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.delete_solver(solver.context, solver.label)?;
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
pub struct RemoteSolver<T: WorkerCommunicator> {
    context: ContextLabel,
    label: SolverLabel,
    timeout: Option<Duration>,
    worker: Arc<RemoteWorker<T>>,
}

impl<T: WorkerCommunicator> PartialEq for RemoteSolver<T> {
    fn eq(&self, other: &Self) -> bool {
        self.context == other.context && self.label == other.label && self.timeout == other.timeout
    }
}

impl<T: WorkerCommunicator> Eq for RemoteSolver<T> {}

impl<T: WorkerCommunicator> Hash for RemoteSolver<T> {
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

impl<T: WorkerCommunicator> ResultSolver for RemoteSolver<T> {
    fn assert(&self, term: &Term) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.assert(self.label, term)?;
        Ok(())
    }

    fn reset(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.reset(self.label)?;
        Ok(())
    }

    fn interrupt(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.interrupt(self.label)?;
        Ok(())
    }

    fn receive_check_sat(
        &self,
        counter: u64,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.worker.receive_check_sat(counter)?;
        Ok(command_response)
    }

    fn send_check_sat(&self) -> Result<u64, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.worker.send_check_sat(self.label)?;
        Ok(command_response)
    }

    fn unsat_core(&self) -> Result<Vec<Term>, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.worker.unsat_core(self.label)?;
        Ok(command_response)
    }

    fn eval(&self, term: &Term) -> Result<Option<Term>, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.worker.eval(self.label, term)?;
        Ok(command_response)
    }

    fn push(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.push(self.label)?;
        Ok(())
    }

    fn pop(&self, size: u64) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.pop(self.label, size)?;
        Ok(())
    }
}

#[derive(Hash, PartialEq, Eq, Debug)]
pub struct RemoteContext {
    label: ContextLabel,
}

impl AsyncContext for RemoteContext {}

#[derive(Debug)]
pub struct RemoteWorker<T: WorkerCommunicator> {
    converter: Converter,
    context_id: RwLock<u64>,
    solver_id: RwLock<u64>,
    state: Mutex<(RemoteState, u64)>,
    active_contexts: RwLock<HashSet<ContextLabel>>,
    active_solvers: RwLock<HashSet<(ContextLabel, SolverLabel)>>,
    solver_commands: RwLock<HashMap<SolverLabel, Vec<RemoteSolverCommand>>>,
    postponed_commands: RwLock<Vec<RemoteCommand>>,
    solver_options: RwLock<HashMap<SolverLabel, Options>>,
    communicator: RwLock<Arc<T>>,
}

impl<T: WorkerCommunicator> Drop for RemoteWorker<T> {
    fn drop(&mut self) {
        self.terminate();
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct IpcWorkerChannels {
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
pub struct IpcWorkerCommunicator {
    pub process: Mutex<Child>,
    pub command_sender: Mutex<IpcSender<RemoteCommand>>,
    pub interrupt_sender: Mutex<IpcSender<SolverLabel>>,
    pub check_state_sender: Mutex<IpcSender<()>>,
    pub state_receiver: Mutex<IpcReceiver<RemoteState>>,
    pub new_solver_receiver: Mutex<IpcReceiver<SolverLabel>>,
    pub new_context_receiver: Mutex<IpcReceiver<ContextLabel>>,
    pub solver_result_receiver: Mutex<IpcReceiver<SolverResult>>,
    pub confirmation_receiver: Mutex<IpcReceiver<()>>,
    pub eval_receiver: Mutex<IpcReceiver<Option<Term>>>,
    pub unsat_core_receiver: Mutex<IpcReceiver<Vec<Term>>>,
}

#[derive(Debug)]
pub struct CrossbeamWorkerCommunicator {
    pub command_sender: Sender<RemoteCommand>,
    pub interrupt_sender: Sender<SolverLabel>,
    pub terminate_sender: Sender<()>,
    pub state_receiver: Receiver<RemoteState>,
    pub new_solver_receiver: Receiver<SolverLabel>,
    pub new_context_receiver: Receiver<ContextLabel>,
    pub solver_result_receiver: Receiver<SolverResult>,
    pub confirmation_receiver: Receiver<()>,
    pub eval_receiver: Receiver<Option<Term>>,
    pub unsat_core_receiver: Receiver<Vec<Term>>,
}

impl IpcWorkerCommunicator {
    pub fn new(communicator: IpcWorkerChannels, process: Child) -> Self {
        Self {
            command_sender: Mutex::new(communicator.command_sender),
            interrupt_sender: Mutex::new(communicator.interrupt_sender),
            new_solver_receiver: Mutex::new(communicator.new_solver_receiver),
            new_context_receiver: Mutex::new(communicator.new_context_receiver),
            solver_result_receiver: Mutex::new(communicator.solver_result_receiver),
            confirmation_receiver: Mutex::new(communicator.confirmation_receiver),
            eval_receiver: Mutex::new(communicator.eval_receiver),
            unsat_core_receiver: Mutex::new(communicator.unsat_core_receiver),
            check_state_sender: Mutex::new(communicator.check_state_sender),
            state_receiver: Mutex::new(communicator.state_receiver),
            process: Mutex::new(process),
        }
    }
}

pub trait WorkerCommunicator {
    fn start_process(converter: &Converter, context_id: u64, solver_id: u64) -> Self;
    fn send_factory_command(
        &self,
        command: RemoteFactoryCommand,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn send_solver_command(
        &self,
        command: RemoteSolverCommand,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn new_context(&self) -> Result<ContextLabel, Box<dyn std::error::Error + Send + Sync>>;
    fn new_solver(
        &self,
        context: ContextLabel,
        options: &Options,
    ) -> Result<SolverLabel, Box<dyn std::error::Error + Send + Sync>>;
    fn restore_context(
        &self,
        context: ContextLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn restore_solver(
        &self,
        context: ContextLabel,
        solver: SolverLabel,
        options: &Options,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn delete_context(
        &self,
        context: ContextLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn delete_solver(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn assert(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn reset(&self, solver: SolverLabel) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn terminate(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn interrupt(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn send_check_sat(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn try_receive_check_sat(
        &self,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>>;
    fn eval(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<Option<Term>, Box<dyn std::error::Error + Send + Sync>>;
    fn unsat_core(
        &self,
        solver: SolverLabel,
    ) -> Result<Vec<Term>, Box<dyn std::error::Error + Send + Sync>>;
    fn push(&self, solver: SolverLabel) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
    fn pop(
        &self,
        solver: SolverLabel,
        size: u64,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>>;
}

impl WorkerCommunicator for IpcWorkerCommunicator {
    fn send_factory_command(
        &self,
        command: RemoteFactoryCommand,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.command_sender
            .lock()
            .unwrap()
            .send(RemoteCommand::Factory(command))?;
        Ok(())
    }

    fn send_solver_command(
        &self,
        command: RemoteSolverCommand,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.command_sender
            .lock()
            .unwrap()
            .send(RemoteCommand::Solver(command))?;
        Ok(())
    }

    fn new_context(&self) -> Result<ContextLabel, Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::NewContext())?;
        let command_response = self.new_context_receiver.lock().unwrap().recv()?;
        Ok(command_response)
    }

    fn new_solver(
        &self,
        context: ContextLabel,
        options: &Options,
    ) -> Result<SolverLabel, Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::NewSolver(context, options.clone()))?;
        let command_response = self.new_solver_receiver.lock().unwrap().recv()?;
        Ok(command_response)
    }

    fn restore_context(
        &self,
        context: ContextLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::RestoreContext(context))?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    fn restore_solver(
        &self,
        context: ContextLabel,
        solver: SolverLabel,
        options: &Options,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::RestoreSolver(
            context,
            solver,
            options.clone(),
        ))?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    fn delete_context(
        &self,
        context: ContextLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::DeleteContext(context))?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    fn delete_solver(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::DeleteSolver(solver))?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    fn assert(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Assert(solver, term.clone());
        self.send_solver_command(command)?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    fn reset(&self, solver: SolverLabel) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Reset(solver);
        self.send_solver_command(command)?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    fn interrupt(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.interrupt_sender.lock().unwrap().send(solver)?;
        Ok(())
    }

    fn send_check_sat(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::CheckSat(solver);
        self.send_solver_command(command)?;
        Ok(())
    }

    fn try_receive_check_sat(
        &self,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.solver_result_receiver.lock().unwrap().try_recv()?;
        Ok(command_response)
    }

    fn eval(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<Option<Term>, Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Eval(solver, term.clone());
        self.send_solver_command(command)?;
        let command_response = self.eval_receiver.lock().unwrap().recv()?;
        Ok(command_response)
    }

    fn unsat_core(
        &self,
        solver: SolverLabel,
    ) -> Result<Vec<Term>, Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::UnsatCore(solver);
        self.send_solver_command(command)?;
        let command_response = self.unsat_core_receiver.lock().unwrap().recv()?;
        Ok(command_response)
    }

    fn push(&self, solver: SolverLabel) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Push(solver);
        self.send_solver_command(command)?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    fn pop(
        &self,
        solver: SolverLabel,
        size: u64,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Pop(solver, size);
        self.send_solver_command(command)?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    fn start_process(converter: &Converter, context_id: u64, solver_id: u64) -> Self {
        let (one_shot_server, one_shot_server_name) = IpcOneShotServer::new().unwrap();
        let serialized_converter = serde_json::to_string(converter).unwrap();
        let serialized_context_solver_id = serde_json::to_string(&(context_id, solver_id)).unwrap();
        let process = Command::new("smithril-runner")
            .arg(one_shot_server_name)
            .arg(serialized_converter)
            .arg(serialized_context_solver_id)
            .spawn()
            .expect("smithtil-runner shoud be installed in PATH");
        let (_, communicator) = one_shot_server.accept().unwrap();
        Self::new(communicator, process)
    }

    fn terminate(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.process.lock().unwrap().kill()?;
        Ok(())
    }
}

impl WorkerCommunicator for CrossbeamWorkerCommunicator {
    fn send_factory_command(
        &self,
        command: RemoteFactoryCommand,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.command_sender.send(RemoteCommand::Factory(command))?;
        Ok(())
    }

    fn send_solver_command(
        &self,
        command: RemoteSolverCommand,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.command_sender.send(RemoteCommand::Solver(command))?;
        Ok(())
    }

    fn new_context(&self) -> Result<ContextLabel, Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::NewContext())?;
        let command_response = self.new_context_receiver.recv()?;
        Ok(command_response)
    }

    fn new_solver(
        &self,
        context: ContextLabel,
        options: &Options,
    ) -> Result<SolverLabel, Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::NewSolver(context, options.clone()))?;
        let command_response = self.new_solver_receiver.recv()?;
        Ok(command_response)
    }

    fn restore_context(
        &self,
        context: ContextLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::RestoreContext(context))?;
        self.confirmation_receiver.recv()?;
        Ok(())
    }

    fn restore_solver(
        &self,
        context: ContextLabel,
        solver: SolverLabel,
        options: &Options,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::RestoreSolver(
            context,
            solver,
            options.clone(),
        ))?;
        self.confirmation_receiver.recv()?;
        Ok(())
    }

    fn delete_context(
        &self,
        context: ContextLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::DeleteContext(context))?;
        self.confirmation_receiver.recv()?;
        Ok(())
    }

    fn delete_solver(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::DeleteSolver(solver))?;
        self.confirmation_receiver.recv()?;
        Ok(())
    }

    fn assert(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Assert(solver, term.clone());
        self.send_solver_command(command)?;
        self.confirmation_receiver.recv()?;
        Ok(())
    }

    fn reset(&self, solver: SolverLabel) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Reset(solver);
        self.send_solver_command(command)?;
        self.confirmation_receiver.recv()?;
        Ok(())
    }

    fn interrupt(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.interrupt_sender.send(solver)?;
        Ok(())
    }

    fn send_check_sat(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::CheckSat(solver);
        self.send_solver_command(command)?;
        Ok(())
    }

    fn try_receive_check_sat(
        &self,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.solver_result_receiver.try_recv()?;
        Ok(command_response)
    }

    fn eval(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<Option<Term>, Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Eval(solver, term.clone());
        self.send_solver_command(command)?;
        let command_response = self.eval_receiver.recv()?;
        Ok(command_response)
    }

    fn unsat_core(
        &self,
        solver: SolverLabel,
    ) -> Result<Vec<Term>, Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::UnsatCore(solver);
        self.send_solver_command(command)?;
        let command_response = self.unsat_core_receiver.recv()?;
        Ok(command_response)
    }

    fn push(&self, solver: SolverLabel) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Push(solver);
        self.send_solver_command(command)?;
        self.confirmation_receiver.recv()?;
        Ok(())
    }

    fn pop(
        &self,
        solver: SolverLabel,
        size: u64,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Pop(solver, size);
        self.send_solver_command(command)?;
        self.confirmation_receiver.recv()?;
        Ok(())
    }

    fn terminate(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.terminate_sender.send(())?;
        Ok(())
    }

    fn start_process(converter: &Converter, context_id: u64, solver_id: u64) -> Self {
        let serialized_converter = serde_json::to_string(converter).unwrap();
        let serialized_context_solver_id = serde_json::to_string(&(context_id, solver_id)).unwrap();
        let (response_sender, response_receiver) = unbounded();
        {
            let serialized_converter = serialized_converter.to_string();
            let serialized_context_solver_id = serialized_context_solver_id.to_string();
            thread::spawn(move || {
                runner::run(
                    response_sender,
                    serialized_converter,
                    serialized_context_solver_id,
                );
            });
        }
        response_receiver.recv().unwrap()
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

impl<T: WorkerCommunicator> RemoteWorker<T> {
    pub fn new(
        converter: &Converter,
        context_id: u64,
        solver_id: u64,
    ) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let communicator = T::start_process(converter, context_id, solver_id);
        let communicator = Arc::new(communicator);
        let communicator = RwLock::new(communicator);
        let converter = converter.clone();
        let context_id = RwLock::new(context_id);
        let solver_id = RwLock::new(solver_id);
        let state = Mutex::new((RemoteState::Idle, 0u64));

        Ok(RemoteWorker {
            communicator,
            active_contexts: Default::default(),
            active_solvers: Default::default(),
            solver_commands: Default::default(),
            solver_options: Default::default(),
            postponed_commands: Default::default(),
            converter,
            context_id,
            solver_id,
            state,
        })
    }

    pub fn restart(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.terminate();
        let context_id = *self.context_id.read().unwrap();
        let solver_id = *self.solver_id.read().unwrap();
        let communicator = T::start_process(&self.converter, context_id, solver_id);
        let communicator = Arc::new(communicator);
        {
            *self.communicator.write().unwrap() = communicator;
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
            ))?;
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
            self.resend_command(command)?;
        }
        let solver_commands = { self.solver_commands.read().unwrap().clone() };

        for (_, commands) in solver_commands {
            for command in commands {
                let command = RemoteCommand::Solver(command.clone());
                self.resend_command(command)?;
            }
        }
        {
            self.postponed_commands.write().unwrap().clear();
        }
        Ok(())
    }

    fn resend_command(
        &self,
        command: RemoteCommand,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        match command {
            RemoteCommand::Solver(command) => match command {
                RemoteSolverCommand::Assert(solver, term) => {
                    self.communicator().assert(solver, &term)?;
                }
                RemoteSolverCommand::Reset(solver) => {
                    self.communicator().reset(solver)?;
                }
                RemoteSolverCommand::CheckSat(solver) => {
                    self.communicator().send_check_sat(solver)?;
                }
                RemoteSolverCommand::UnsatCore(solver) => {
                    let _ = self.communicator().unsat_core(solver)?;
                }
                RemoteSolverCommand::Eval(solver, term) => {
                    let _ = self.communicator().eval(solver, &term)?;
                }
                RemoteSolverCommand::Push(solver) => {
                    self.communicator().push(solver)?;
                }
                RemoteSolverCommand::Pop(solver, size) => {
                    self.communicator().pop(solver, size)?;
                }
            },
            RemoteCommand::Factory(command) => match command {
                RemoteFactoryCommand::DeleteContext(context) => {
                    self.communicator().delete_context(context)?;
                }
                RemoteFactoryCommand::DeleteSolver(solver) => {
                    self.communicator().delete_solver(solver)?;
                }
                RemoteFactoryCommand::NewContext() => {
                    let _ = self.communicator().new_context()?;
                }
                RemoteFactoryCommand::NewSolver(context, options) => {
                    let _ = self.communicator().new_solver(context, &options)?;
                }
                RemoteFactoryCommand::RestoreContext(context) => {
                    self.communicator().restore_context(context)?;
                }
                RemoteFactoryCommand::RestoreSolver(context, solver, options) => {
                    self.communicator()
                        .restore_solver(context, solver, &options)?;
                }
            },
        }
        Ok(())
    }

    pub fn terminate(&self) {
        self.communicator().terminate().unwrap();
    }

    fn communicator(&self) -> Arc<T> {
        self.communicator.read().unwrap().clone()
    }

    fn save_solver_command(
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

    fn try_resend_postponed_commands(
        &self,
        state: RemoteState,
    ) -> Result<bool, Box<dyn Error + Send + Sync>> {
        match state {
            RemoteState::Busy => Ok(false),
            RemoteState::Idle => {
                self.resend_postponed_commands()?;
                Ok(true)
            }
        }
    }

    fn resend_postponed_commands(&self) -> Result<(), Box<dyn Error + Send + Sync>> {
        let mut lock = self.postponed_commands.write().unwrap();
        let postponed_commands = lock.clone();
        if !postponed_commands.is_empty() {
            for command in postponed_commands.into_iter() {
                self.resend_command(command)?;
            }
            lock.clear();
        }
        Ok(())
    }

    fn postpone_command(&self, command: RemoteCommand) {
        self.postponed_commands.write().unwrap().push(command);
    }

    pub fn new_context(&self) -> Result<ContextLabel, Box<dyn std::error::Error + Send + Sync>> {
        let lock = self.state.lock().unwrap();
        let state = lock.0;
        {
            *self.context_id.write().unwrap() += 1;
        }
        let command_response = if !self.try_resend_postponed_commands(state)? {
            self.postpone_command(RemoteCommand::Factory(RemoteFactoryCommand::NewContext()));
            let context_id = { *self.context_id.read().unwrap() };
            ContextLabel(context_id)
        } else {
            let context = self.communicator().new_context();
            context?
        };

        self.active_contexts
            .write()
            .unwrap()
            .insert(command_response);
        Ok(command_response)
    }

    pub fn new_solver(
        &self,
        context: ContextLabel,
        options: &Options,
    ) -> Result<SolverLabel, Box<dyn std::error::Error + Send + Sync>> {
        let lock = self.state.lock().unwrap();
        let state = lock.0;
        {
            *self.solver_id.write().unwrap() += 1;
        }
        let command_response = if !self.try_resend_postponed_commands(state)? {
            self.postpone_command(RemoteCommand::Factory(RemoteFactoryCommand::NewSolver(
                context,
                options.clone(),
            )));
            let solver_id = { *self.solver_id.read().unwrap() };
            SolverLabel(solver_id)
        } else {
            let solver = self.communicator().new_solver(context, options);
            solver?
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

    pub fn delete_context(
        &self,
        context: ContextLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let lock = self.state.lock().unwrap();
        let state = lock.0;
        if !self.try_resend_postponed_commands(state)? {
            self.postpone_command(RemoteCommand::Factory(RemoteFactoryCommand::DeleteContext(
                context,
            )));
        } else {
            let command_response = self.communicator().delete_context(context);
            command_response?;
        };
        self.active_contexts.write().unwrap().remove(&context);
        Ok(())
    }

    pub fn delete_solver(
        &self,
        context: ContextLabel,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let lock = self.state.lock().unwrap();
        let state = lock.0;
        if !self.try_resend_postponed_commands(state)? {
            self.postpone_command(RemoteCommand::Factory(RemoteFactoryCommand::DeleteSolver(
                solver,
            )));
        } else {
            let command_response = self.communicator().delete_solver(solver);
            command_response?;
        };
        self.active_solvers
            .write()
            .unwrap()
            .remove(&(context, solver));
        self.solver_commands.write().unwrap().remove(&solver);
        self.solver_options.write().unwrap().remove(&solver);
        Ok(())
    }

    pub fn assert(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let lock = self.state.lock().unwrap();
        let state = lock.0;
        let command = RemoteSolverCommand::Assert(solver, term.clone());
        self.save_solver_command(solver, command.clone())?;
        if !self.try_resend_postponed_commands(state)? {
            self.postpone_command(RemoteCommand::Solver(command));
        } else {
            let command_response = self.communicator().assert(solver, term);
            command_response?;
        };
        Ok(())
    }

    pub fn reset(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let lock = self.state.lock().unwrap();
        let state = lock.0;
        let command = RemoteSolverCommand::Reset(solver);
        self.save_solver_command(solver, command.clone())?;
        if !self.try_resend_postponed_commands(state)? {
            self.postpone_command(RemoteCommand::Solver(command));
        } else {
            let command_response = self.communicator().reset(solver);
            command_response?;
        };
        Ok(())
    }

    pub fn eval(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<Option<Term>, Box<dyn std::error::Error + Send + Sync>> {
        let lock = self.state.lock().unwrap();
        let state = lock.0;
        if !self.try_resend_postponed_commands(state)? {
            Err(Box::new(WorkerError {}))
        } else {
            let command_response = self.communicator().eval(solver, term);
            Ok(command_response?)
        }
    }

    pub fn unsat_core(
        &self,
        solver: SolverLabel,
    ) -> Result<Vec<Term>, Box<dyn std::error::Error + Send + Sync>> {
        let lock = self.state.lock().unwrap();
        let state = lock.0;
        if !self.try_resend_postponed_commands(state)? {
            Err(Box::new(WorkerError {}))
        } else {
            let command_response = self.communicator().unsat_core(solver);
            Ok(command_response?)
        }
    }

    pub fn interrupt(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let lock = self.state.lock().unwrap();
        let state = lock.0;
        if state != RemoteState::Busy {
            self.communicator().interrupt(solver)?;
        }
        Ok(())
    }

    pub fn receive_check_sat(
        &self,
        counter: u64,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = loop {
            let mut lock = self.state.lock().unwrap();
            let (_, current_counter) = *lock;
            if counter == current_counter {
                if let Ok(res) = self.communicator().try_receive_check_sat() {
                    *lock = (RemoteState::Idle, current_counter);
                    break res;
                }
            } else {
                break SolverResult::Unknown;
            }
        };
        Ok(command_response)
    }

    fn send_check_sat(
        &self,
        solver: SolverLabel,
    ) -> Result<u64, Box<dyn std::error::Error + Send + Sync>> {
        let mut lock = self.state.lock().unwrap();
        let (state, counter) = *lock;
        let counter = counter + 1;
        match state {
            RemoteState::Busy => {
                self.restart()?;
            }
            RemoteState::Idle => {
                self.resend_postponed_commands()?;
                *lock = (RemoteState::Busy, counter);
            }
        }
        self.communicator().send_check_sat(solver)?;
        Ok(counter)
    }

    pub fn push(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let lock = self.state.lock().unwrap();
        let state = lock.0;
        let command = RemoteSolverCommand::Push(solver);
        self.save_solver_command(solver, command.clone())?;
        if !self.try_resend_postponed_commands(state)? {
            self.postpone_command(RemoteCommand::Solver(command));
        } else {
            let command_response = self.communicator().push(solver);
            command_response?;
        };
        Ok(())
    }

    pub fn pop(
        &self,
        solver: SolverLabel,
        size: u64,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Pop(solver, size);
        let lock = self.state.lock().unwrap();
        let state = lock.0;
        self.save_solver_command(solver, command.clone())?;
        if !self.try_resend_postponed_commands(state)? {
            self.postpone_command(RemoteCommand::Solver(command));
        } else {
            let command_response = self.communicator().pop(solver, size);
            command_response?;
        };
        Ok(())
    }
}

#[derive(Clone)]
pub enum InterruptionType {
    Abort,
    Result(SolverResult, usize),
}

impl<T: WorkerCommunicator + Send + Sync + 'static> RemoteSolver<T> {
    pub fn cancellabel_check_sat(
        s: Arc<Self>,
        token: Receiver<()>,
        tx_check_sat: Sender<InterruptionType>,
        id: usize,
    ) {
        let (tx_cancell, rx_cancell) = unbounded();

        {
            let timeout = s.timeout;
            thread::spawn(move || {
                if let Some(timeout) = timeout {
                    let (tx_timeout1, rx_timeout) = unbounded();
                    let tx_timeout2 = tx_timeout1.clone();
                    thread::spawn(move || {
                        thread::sleep(timeout);
                        let _ = tx_timeout1.send(());
                    });
                    thread::spawn(move || {
                        let _ = token.recv();
                        let _ = tx_timeout2.send(());
                    });
                    let _ = rx_timeout.recv();
                    let _ = tx_cancell.send(());
                } else {
                    let _ = token.recv();
                    let _ = tx_cancell.send(());
                }
            });
        }

        let tx_check_sat2 = tx_check_sat.clone();
        if rx_cancell.try_recv().is_ok() {
            let _ = tx_check_sat2.send(InterruptionType::Abort);
        } else {
            let s = s.clone();
            if let Ok(counter) = s.send_check_sat() {
                thread::spawn(move || {
                    let res = s.receive_check_sat(counter);
                    if let Ok(res) = res {
                        let _ = tx_check_sat.send(InterruptionType::Result(res, id));
                    } else {
                        let _ = tx_check_sat.send(InterruptionType::Abort);
                    }
                });
            }

            thread::spawn(move || {
                let _ = rx_cancell.recv();
                let _ = tx_check_sat2.send(InterruptionType::Abort);
            });
        }
    }
}

pub struct SmithrilFactory<T: WorkerCommunicator> {
    factories: Vec<RemoteFactory<T>>,
}

impl<T: WorkerCommunicator> SmithrilFactory<T> {
    pub fn new(converters: Vec<Converter>) -> Self {
        let mut factories: Vec<RemoteFactory<T>> = Default::default();

        for converter in &converters {
            let solver_process = RemoteFactory::new(converter).unwrap();
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
pub struct SmithrilSolver<T: WorkerCommunicator> {
    solvers: Vec<Arc<RemoteSolver<T>>>,
    last_fastest_solver_index: RwLock<Option<usize>>,
}

impl<T: WorkerCommunicator> PartialEq for SmithrilSolver<T> {
    fn eq(&self, other: &Self) -> bool {
        self.solvers.eq(&other.solvers)
    }
}

impl<T: WorkerCommunicator> Eq for SmithrilSolver<T> {}

impl<T: WorkerCommunicator> Hash for SmithrilSolver<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.solvers.hash(state);
    }
}

impl<T: WorkerCommunicator + Send + Sync + 'static> AsyncFactory<SmithrilContext, SmithrilSolver<T>>
    for SmithrilFactory<T>
{
    fn new_context(&self) -> Arc<SmithrilContext> {
        let mut contexts = Vec::new();
        for factory in self.factories.iter() {
            contexts.push(factory.new_context().unwrap());
        }
        Arc::new(SmithrilContext { contexts })
    }

    fn delete_context(&self, context: Arc<SmithrilContext>) {
        assert_eq!(Arc::strong_count(&context), 1);
        let context = Arc::try_unwrap(context).unwrap();
        for (factory, context) in self.factories.iter().zip(context.contexts.into_iter()) {
            factory.delete_context(context).unwrap();
        }
    }

    fn new_solver(
        &self,
        context: Arc<SmithrilContext>,
        options: &Options,
    ) -> Arc<SmithrilSolver<T>> {
        let mut solvers = Vec::new();
        for (factory, context) in self.factories.iter().zip(context.contexts.iter()) {
            solvers.push(factory.new_solver(context, options).unwrap());
        }
        Arc::new(SmithrilSolver {
            solvers,
            last_fastest_solver_index: RwLock::new(Default::default()),
        })
    }

    fn delete_solver(&self, solver: Arc<SmithrilSolver<T>>) {
        assert_eq!(Arc::strong_count(&solver), 1);
        let solver = Arc::try_unwrap(solver).ok().unwrap();
        let solvers = solver.solvers;
        for (factory, solver) in self.factories.iter().zip(solvers.into_iter()) {
            factory.delete_solver(solver).unwrap()
        }
    }
}

impl<T: WorkerCommunicator + Send + Sync + 'static> AsyncSolver for SmithrilSolver<T> {
    fn assert(&self, term: &Term) {
        for solver in self.solvers.iter() {
            solver.assert(term).unwrap();
        }
    }

    fn reset(&self) {
        for solver in self.solvers.iter() {
            solver.reset().unwrap();
        }
    }

    fn interrupt(&self) {
        for solver in self.solvers.iter() {
            solver.interrupt().unwrap();
        }
    }

    fn check_sat(&self) -> SolverResult {
        let (cancell, token) = unbounded();
        let (s_check_sat, r_check_sat) = unbounded();
        let index = { *self.last_fastest_solver_index.read().unwrap() };
        if let Some(index) = index {
            let solver = self.solvers.get(index).unwrap();
            RemoteSolver::cancellabel_check_sat(
                solver.clone(),
                token.clone(),
                s_check_sat.clone(),
                index,
            );
        }
        for (count, solver) in self.solvers.iter().enumerate() {
            if index.is_none() || index.unwrap() != count {
                RemoteSolver::cancellabel_check_sat(
                    solver.clone(),
                    token.clone(),
                    s_check_sat.clone(),
                    count,
                );
            }
        }

        {
            *self.last_fastest_solver_index.write().unwrap() = None;
        }

        let mut result = SolverResult::Unknown;
        for _ in 0..self.solvers.len() {
            match r_check_sat.recv().unwrap() {
                InterruptionType::Abort => (),
                InterruptionType::Result(SolverResult::Unknown, _) => (),
                InterruptionType::Result(res, count) => {
                    cancell.send(()).unwrap();
                    *self.last_fastest_solver_index.write().unwrap() = Some(count);
                    result = res;
                    break;
                }
            }
        }
        if result == SolverResult::Unknown {
            *self.last_fastest_solver_index.write().unwrap() = None;
        }
        result
    }

    fn unsat_core(&self) -> Vec<Term> {
        let last_fastest_solver_index =
            { *self.last_fastest_solver_index.read().unwrap() }.unwrap();
        let solver = self.solvers.get(last_fastest_solver_index).unwrap();
        solver.unsat_core().unwrap()
    }

    fn eval(&self, term: &Term) -> Option<Term> {
        let last_fastest_solver_index =
            { *self.last_fastest_solver_index.read().unwrap() }.unwrap();
        let solver = self.solvers.get(last_fastest_solver_index).unwrap();
        solver.eval(term).unwrap()
    }

    fn push(&self) {
        for solver in self.solvers.iter() {
            solver.push().unwrap();
        }
    }

    fn pop(&self, size: u64) {
        for solver in self.solvers.iter() {
            solver.pop(size).unwrap();
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

#[test]
fn smithril_working_ipc_test() {
    let converters = vec![Converter::Bitwuzla, Converter::Z3];
    let t = sat_works("");

    let factory = SmithrilFactory::<IpcWorkerCommunicator>::new(converters.clone());
    let context = factory.new_context();
    let solver = factory.new_solver(context, &Options::default());
    solver.assert(&t);
    let status = solver.check_sat();
    assert_eq!(SolverResult::Sat, status);
    solver.reset();

    let t = unsat_works();

    solver.assert(&t);
    let status = solver.check_sat();
    assert_eq!(SolverResult::Unsat, status);
    solver.reset();
}

#[test]
fn smithril_unsat_core_ipc_test() {
    let converters = vec![Converter::Bitwuzla, Converter::Z3];

    let factory = SmithrilFactory::<IpcWorkerCommunicator>::new(converters.clone());
    let context = factory.new_context();
    let mut options = Options::default();
    options.set_produce_unsat_core(true);
    let solver = factory.new_solver(context, &options);

    let t = unsat_works();

    solver.assert(&t);
    let status = solver.check_sat();
    assert_eq!(SolverResult::Unsat, status);
    let unsat_core = solver.unsat_core();
    assert_eq!(unsat_core.len(), 1);
}

#[test]
fn smithril_timeout_test() {
    let converters = vec![Converter::Dummy];

    let factory = SmithrilFactory::<CrossbeamWorkerCommunicator>::new(converters.clone());
    let context = factory.new_context();
    let mut options = Options::default();
    options.set_external_timeout(Some(Duration::from_nanos(1)));
    let solver = factory.new_solver(context, &options);
    for i in 0..1000 {
        let t = sat_works(&i.to_string());
        solver.assert(&t);
    }
    let status = solver.check_sat();
    assert_eq!(SolverResult::Unknown, status);
}
