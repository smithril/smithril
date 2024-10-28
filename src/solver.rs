use crossbeam_channel::{unbounded, Receiver, Sender};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt::{self, Debug, Display};
use std::hash::Hash;
use std::path::PathBuf;
use std::process::{Child, Command};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

use ipc_channel::ipc::{IpcOneShotServer, IpcReceiver, IpcSender};

use crate::converters::Converter;
use crate::generalized::{
    AsyncContext, AsyncFactory, AsyncSolver, Options, ResultFactory, ResultSolver, SolverResult,
};
use crate::term::Term;

pub struct RemoteFactory {
    worker: Arc<RemoteWorker>,
}

impl RemoteFactory {
    pub fn new(
        solver_path: &str,
        converter: &Converter,
    ) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let context_id = 0u64;
        let solver_id = 0u64;

        Ok(RemoteFactory {
            worker: Arc::new(RemoteWorker::new(
                solver_path,
                converter,
                context_id,
                solver_id,
            )?),
        })
    }

    fn terminate(&self) {
        self.worker.terminate();
    }
}

impl ResultFactory<RemoteContext, RemoteSolver> for RemoteFactory {
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
    ) -> Result<Arc<RemoteSolver>, Box<dyn std::error::Error + Send + Sync>> {
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
        solver: Arc<RemoteSolver>,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.delete_solver(solver.context, solver.label)?;
        Ok(())
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub enum RemoteSolverCommand {
    Assert(SolverLabel, Term),
    Reset(SolverLabel),
    CheckSat(SolverLabel, u64),
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

impl ResultSolver for RemoteSolver {
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
pub struct RemoteWorker {
    solver_path: String,
    converter: Converter,
    context_id: Mutex<u64>,
    solver_id: Mutex<u64>,
    process: Mutex<Child>,
    state: Mutex<(RemoteState, u64)>,
    active_contexts: Mutex<HashSet<ContextLabel>>,
    active_solvers: Mutex<HashSet<(ContextLabel, SolverLabel)>>,
    solver_commands: Mutex<HashMap<SolverLabel, Vec<RemoteSolverCommand>>>,
    postponed_commands: Mutex<Vec<RemoteCommand>>,
    solver_options: Mutex<HashMap<SolverLabel, Options>>,
    communicator: Mutex<Arc<RemoteWorkerLockingCommunicator>>,
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
    pub counter: Mutex<u64>,
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
            counter: Mutex::new(0),
        }
    }

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

    pub fn new_context(&self) -> Result<ContextLabel, Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::NewContext())?;
        let command_response = self.new_context_receiver.lock().unwrap().recv()?;
        Ok(command_response)
    }

    pub fn new_solver(
        &self,
        context: ContextLabel,
        options: &Options,
    ) -> Result<SolverLabel, Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::NewSolver(context, options.clone()))?;
        let command_response = self.new_solver_receiver.lock().unwrap().recv()?;
        Ok(command_response)
    }

    pub fn restore_context(
        &self,
        context: ContextLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::RestoreContext(context))?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    pub fn restore_solver(
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

    pub fn delete_context(
        &self,
        context: ContextLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::DeleteContext(context))?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    pub fn delete_solver(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.send_factory_command(RemoteFactoryCommand::DeleteSolver(solver))?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    pub fn assert(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Assert(solver, term.clone());
        self.send_solver_command(command)?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    pub fn reset(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Reset(solver);
        self.send_solver_command(command)?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    pub fn interrupt(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.interrupt_sender.lock().unwrap().send(solver)?;
        Ok(())
    }

    pub fn send_check_sat(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut lock = self.counter.lock().unwrap();
        *lock += 1;
        let command = RemoteSolverCommand::CheckSat(solver, *lock);
        self.send_solver_command(command)?;
        Ok(())
    }

    pub fn try_receive_check_sat(
        &self,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.solver_result_receiver.lock().unwrap().try_recv()?;
        Ok(command_response)
    }

    pub fn eval(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<Option<Term>, Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Eval(solver, term.clone());
        self.send_solver_command(command)?;
        let command_response = self.eval_receiver.lock().unwrap().recv()?;
        Ok(command_response)
    }

    pub fn unsat_core(
        &self,
        solver: SolverLabel,
    ) -> Result<Vec<Term>, Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::UnsatCore(solver);
        self.send_solver_command(command)?;
        let command_response = self.unsat_core_receiver.lock().unwrap().recv()?;
        Ok(command_response)
    }

    pub fn check_state(&self) -> Result<RemoteState, Box<dyn std::error::Error + Send + Sync>> {
        let state = {
            self.check_state_sender.lock().unwrap().send(())?;
            self.state_receiver.lock().unwrap().recv()?
        };
        Ok(state)
    }

    pub fn push(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Push(solver);
        self.send_solver_command(command)?;
        self.confirmation_receiver.lock().unwrap().recv()?;
        Ok(())
    }

    pub fn pop(
        &self,
        solver: SolverLabel,
        size: u64,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Pop(solver, size);
        self.send_solver_command(command)?;
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
    pub fn new(
        solver_path: &str,
        converter: &Converter,
        context_id: u64,
        solver_id: u64,
    ) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let (process, communicator) =
            RemoteWorker::start_process(converter, context_id, solver_id, solver_path)?;
        let process = Mutex::new(process);
        let communicator = RemoteWorkerLockingCommunicator::new(communicator);
        let communicator = Arc::new(communicator);
        let communicator = Mutex::new(communicator);
        let solver_path = solver_path.to_string();
        let converter = converter.clone();
        let context_id = Mutex::new(context_id);
        let solver_id = Mutex::new(solver_id);
        let check_sat = Mutex::new((RemoteState::Idle, 0u64));

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
            state: check_sat,
        })
    }

    fn start_process(
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
                RemoteSolverCommand::CheckSat(solver, _) => {
                    let _ = self.communicator().send_check_sat(solver)?;
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

    pub fn restart(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.terminate();
        dbg!("restart", &self.converter);
        let context_id = *self.context_id.lock().unwrap();
        let solver_id = *self.solver_id.lock().unwrap();
        let (process, communicator) = RemoteWorker::start_process(
            &self.converter,
            context_id,
            solver_id,
            self.solver_path.as_str(),
        )?;
        let communicator = RemoteWorkerLockingCommunicator::new(communicator);
        let communicator = Arc::new(communicator);
        {
            *self.process.lock().unwrap() = process;
            *self.communicator.lock().unwrap() = communicator;
        }
        let contexts: Vec<_> = self
            .active_contexts
            .lock()
            .unwrap()
            .iter()
            .cloned()
            .collect();
        for context in contexts {
            dbg!("restore context", &context);
            self.resend_command(RemoteCommand::Factory(
                RemoteFactoryCommand::RestoreContext(context),
            ))?;
        }
        let solvers: Vec<_> = self
            .active_solvers
            .lock()
            .unwrap()
            .iter()
            .cloned()
            .collect();
        for (context, solver) in solvers {
            let option = {
                self.solver_options
                    .lock()
                    .unwrap()
                    .get(&solver)
                    .unwrap()
                    .clone()
            };
            dbg!("restore solver", &solver);
            let command = RemoteCommand::Factory(RemoteFactoryCommand::RestoreSolver(
                context, solver, option,
            ));
            self.resend_command(command)?;
        }
        let solver_commands = { self.solver_commands.lock().unwrap().clone() };

        for (_, commands) in solver_commands {
            for command in commands {
                let command = RemoteCommand::Solver(command.clone());
                self.resend_command(command)?;
            }
        }
        {
            self.postponed_commands.lock().unwrap().clear();
        }
        Ok(())
    }

    pub fn check_state(&self) -> Result<RemoteState, Box<dyn std::error::Error + Send + Sync>> {
        let state = self.communicator().check_state()?;
        Ok(state)
    }

    pub fn terminate(&self) {
        self.process.lock().unwrap().kill().unwrap();
    }

    fn communicator(&self) -> Arc<RemoteWorkerLockingCommunicator> {
        self.communicator.lock().unwrap().clone()
    }

    fn save_solver_command(
        &self,
        solver_label: SolverLabel,
        command: RemoteSolverCommand,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.solver_commands
            .lock()
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
        let mut lock = self.postponed_commands.lock().unwrap();
        let postponed_commands = lock.clone();
        Ok(if !postponed_commands.is_empty() {
            for command in postponed_commands.into_iter() {
                self.resend_command(command)?;
            }
            lock.clear();
        })
    }

    fn postpone_command(&self, command: RemoteCommand) {
        self.postponed_commands.lock().unwrap().push(command);
    }

    pub fn new_context(&self) -> Result<ContextLabel, Box<dyn std::error::Error + Send + Sync>> {
        let lock = self.state.lock().unwrap();
        let state = lock.0;
        {
            *self.context_id.lock().unwrap() += 1;
        }
        let command_response = if !self.try_resend_postponed_commands(state)? {
            self.postpone_command(RemoteCommand::Factory(RemoteFactoryCommand::NewContext()));
            let context_id = { *self.context_id.lock().unwrap() };
            ContextLabel(context_id)
        } else {
            let context = self.communicator().new_context();
            context?
        };

        self.active_contexts
            .lock()
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
            *self.solver_id.lock().unwrap() += 1;
        }
        let command_response = if !self.try_resend_postponed_commands(state)? {
            self.postpone_command(RemoteCommand::Factory(RemoteFactoryCommand::NewSolver(
                context,
                options.clone(),
            )));
            let solver_id = { *self.solver_id.lock().unwrap() };
            SolverLabel(solver_id)
        } else {
            let solver = self.communicator().new_solver(context, options);
            solver?
        };
        self.active_solvers
            .lock()
            .unwrap()
            .insert((context, command_response));
        self.solver_options
            .lock()
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
        self.active_contexts.lock().unwrap().remove(&context);
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
            .lock()
            .unwrap()
            .remove(&(context, solver));
        self.solver_commands.lock().unwrap().remove(&solver);
        self.solver_options.lock().unwrap().remove(&solver);
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
        let state = (*lock).0;
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

    // pub fn close_check_sat(&self, counter: u64) {
    //     let mut lock = self.state.lock().unwrap();
    //     let (state, new_counter) = *lock;
    //     if counter == new_counter {
    //         dbg!("close_check_sat good");
    //         assert_eq!(state, RemoteState::Busy);
    //         *lock = (RemoteState::Idle, counter);
    //     } else {
    //         dbg!(("close_check_sat bad", counter, new_counter));
    //     }
    // }

    // fn open_check_sat(&self) -> Result<u64, Box<dyn Error + Send + Sync>> {
    //     let counter = {
    //         let mut lock = self.state.lock().unwrap();
    //         let (state, counter) = *lock;
    //         let counter = counter + 1;
    //         *lock = (state, counter);
    //         counter
    //     };
    //     {
    //         let mut lock = self.state.lock().unwrap();
    //         let (state, counter) = *lock;
    //         match state {
    //             RemoteState::Busy => {
    //                 self.restart()?;
    //             }
    //             RemoteState::Idle => {
    //                 self.resend_postponed_commands()?;
    //                 *lock = (RemoteState::Busy, counter);
    //             }
    //         }
    //     }
    //     Ok(counter)
    // }

    pub fn push(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let lock = self.state.lock().unwrap();
        let state = (*lock).0;
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
        let state = (*lock).0;
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

impl RemoteSolver {
    pub fn cancellabel_check_sat(
        s: Arc<Self>,
        token: Receiver<()>,
        tx_check_sat: Sender<InterruptionType>,
        id: usize,
    ) {
        let (tx_cancell, rx_cancell) = unbounded();

        {
            let timeout = s.timeout.clone();
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
        {
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

pub struct SmithrilFactory {
    factories: Vec<RemoteFactory>,
}

impl Drop for SmithrilFactory {
    fn drop(&mut self) {
        self.terminate();
    }
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
    pub fn new(converters: Vec<Converter>) -> Self {
        let solver_path = get_solver_path("smithril-runner");
        let solver_path_string = solver_path.to_string_lossy().into_owned();
        let mut factories: Vec<RemoteFactory> = Default::default();

        for converter in &converters {
            let solver_process = RemoteFactory::new(&solver_path_string, converter).unwrap();
            factories.push(solver_process);
        }
        Self { factories }
    }

    fn terminate(&self) {
        for solver in self.factories.iter() {
            solver.terminate();
        }
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
    last_fastest_solver_index: Mutex<Option<usize>>,
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

    fn new_solver(&self, context: Arc<SmithrilContext>, options: &Options) -> Arc<SmithrilSolver> {
        let mut solvers = Vec::new();
        for (factory, context) in self.factories.iter().zip(context.contexts.iter()) {
            solvers.push(factory.new_solver(context, options).unwrap());
        }
        Arc::new(SmithrilSolver {
            solvers,
            last_fastest_solver_index: Mutex::new(Default::default()),
        })
    }

    fn delete_solver(&self, solver: Arc<SmithrilSolver>) {
        assert_eq!(Arc::strong_count(&solver), 1);
        let solver = Arc::try_unwrap(solver).ok().unwrap();
        let solvers = solver.solvers;
        for (factory, solver) in self.factories.iter().zip(solvers.into_iter()) {
            factory.delete_solver(solver).unwrap()
        }
    }
}

impl AsyncSolver for SmithrilSolver {
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
        for (count, solver) in self.solvers.iter().enumerate() {
            RemoteSolver::cancellabel_check_sat(
                solver.clone(),
                token.clone(),
                s_check_sat.clone(),
                count,
            );
        }

        {
            *self.last_fastest_solver_index.lock().unwrap() = None;
        }

        let mut result = SolverResult::Unknown;
        for _ in 0..self.solvers.len() {
            match r_check_sat.recv().unwrap() {
                InterruptionType::Abort => (),
                InterruptionType::Result(SolverResult::Unknown, _) => (),
                InterruptionType::Result(res, count) => {
                    cancell.send(()).unwrap();
                    *self.last_fastest_solver_index.lock().unwrap() = Some(count);
                    result = res;
                    break;
                }
            }
        }
        dbg!((
            "check_sat",
            "smithril",
            &result,
            *self.last_fastest_solver_index.lock().unwrap()
        ));
        if result == SolverResult::Unknown {
            *self.last_fastest_solver_index.lock().unwrap() = None;
        }
        result
    }

    fn unsat_core(&self) -> Vec<Term> {
        let last_fastest_solver_index =
            { *self.last_fastest_solver_index.lock().unwrap() }.unwrap();
        let solver = self.solvers.get(last_fastest_solver_index).unwrap();
        let res = solver.unsat_core().unwrap();
        res
    }

    fn eval(&self, term: &Term) -> Option<Term> {
        let last_fastest_solver_index =
            { *self.last_fastest_solver_index.lock().unwrap() }.unwrap();
        let solver = self.solvers.get(last_fastest_solver_index).unwrap();
        let res = solver.eval(term).unwrap();
        res
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
fn smithril_working_test() {
    let converters = vec![Converter::Bitwuzla, Converter::Z3];
    let t = sat_works("");

    let factory = SmithrilFactory::new(converters.clone());
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
fn smithril_unsat_core_test() {
    let converters = vec![Converter::Bitwuzla, Converter::Z3];

    let factory = SmithrilFactory::new(converters.clone());
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

    let factory = SmithrilFactory::new(converters.clone());
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
