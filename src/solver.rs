use crossbeam_channel::{unbounded, Receiver, Sender};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt::{self, Debug, Display};
use std::hash::Hash;
use std::path::PathBuf;
use std::process::{Child, Command};
use std::sync::{Arc, Mutex, RwLock, RwLockReadGuard};
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
        let var_name = 0u64;
        let context_id = var_name;
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
}

impl ResultFactory<RemoteContext, RemoteSolver> for RemoteFactory {
    fn terminate(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        self.worker.terminate()?;
        Ok(())
    }

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

    fn check_sat(&self) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        let command_response = self.worker.check_sat(self.label)?;
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
    in_resend: Mutex<bool>,
    active_contexts: RwLock<HashSet<ContextLabel>>,
    active_solvers: RwLock<HashSet<(ContextLabel, SolverLabel)>>,
    solver_commands: RwLock<HashMap<SolverLabel, Vec<RemoteSolverCommand>>>,
    postponed_commands: RwLock<Vec<RemoteCommand>>,
    solver_options: RwLock<HashMap<SolverLabel, Options>>,
    communicator: RwLock<RemoteWorkerLockingCommunicator>,
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

    pub fn check_sat(
        &self,
        solver: SolverLabel,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::CheckSat(solver);
        self.send_solver_command(command)?;
        let command_response = self.solver_result_receiver.lock().unwrap().recv()?;
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
        let process = RwLock::new(process);
        let communicator = RemoteWorkerLockingCommunicator::new(communicator);
        let communicator = RwLock::new(communicator);
        let solver_path = solver_path.to_string();
        let converter = converter.clone();
        let context_id = RwLock::new(context_id);
        let solver_id = RwLock::new(solver_id);
        let count_ready = Mutex::new(0);
        let is_alive = Mutex::new(true);
        let in_resend = Mutex::new(false);

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
            in_resend,
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
                RemoteSolverCommand::CheckSat(solver) => {
                    let _ = self.communicator().check_sat(solver)?;
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
        if !*self.is_alive.lock().unwrap() {
            return Ok(());
        }
        self.wait_zero_communication_to_lock_is_alive();
        self.terminate()?;
        let context_id = *self.context_id.read().unwrap();
        let solver_id = *self.solver_id.read().unwrap();
        let (process, communicator) = RemoteWorker::start_process(
            &self.converter,
            context_id,
            solver_id,
            self.solver_path.as_str(),
        )?;
        let communicator = RemoteWorkerLockingCommunicator::new(communicator);
        {
            *self.process.write().unwrap() = process;
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

    fn wait_and_lock_in_resend(&self) {
        loop {
            let mut lock = self.in_resend.lock().unwrap();
            if !*lock {
                *lock = true;
                break;
            }
        }
    }

    fn free_in_resend(&self) {
        *self.in_resend.lock().unwrap() = false;
    }

    pub fn check_state(&self) -> Result<RemoteState, Box<dyn std::error::Error + Send + Sync>> {
        self.inc_communication();
        let state = self.communicator().check_state()?;
        self.dec_communication();
        Ok(state)
    }

    pub fn terminate(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        {
            self.process.write().unwrap().kill()?;
        }
        Ok(())
    }

    fn communicator(&self) -> RwLockReadGuard<RemoteWorkerLockingCommunicator> {
        self.communicator.read().unwrap()
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
    ) -> Result<bool, Box<dyn std::error::Error + Send + Sync>> {
        self.wait_and_lock_in_resend();
        let state = self.check_state()?;
        let res = match state {
            RemoteState::Busy => Ok(false),
            RemoteState::Idle => {
                let postponed_commands = { self.postponed_commands.read().unwrap() }.clone();
                if !postponed_commands.is_empty() {
                    for command in postponed_commands.into_iter() {
                        self.resend_command(command)?;
                    }
                    self.postponed_commands.write().unwrap().clear();
                }
                Ok(true)
            }
        };
        self.free_in_resend();
        res
    }

    fn postpone_command(&self, command: RemoteCommand) {
        self.postponed_commands.write().unwrap().push(command);
    }

    pub fn new_context(&self) -> Result<ContextLabel, Box<dyn std::error::Error + Send + Sync>> {
        {
            *self.context_id.write().unwrap() += 1;
        }
        let command_response = if !self.try_resend_postponed_commands()? {
            self.postpone_command(RemoteCommand::Factory(RemoteFactoryCommand::NewContext()));
            let context_id = { *self.context_id.read().unwrap() };
            ContextLabel(context_id)
        } else {
            self.inc_communication();
            let context = self.communicator().new_context()?;
            self.dec_communication();
            context
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
        {
            *self.solver_id.write().unwrap() += 1;
        }
        let command_response = if !self.try_resend_postponed_commands()? {
            self.postpone_command(RemoteCommand::Factory(RemoteFactoryCommand::NewSolver(
                context,
                options.clone(),
            )));
            let solver_id = { *self.solver_id.read().unwrap() };
            SolverLabel(solver_id)
        } else {
            self.inc_communication();
            let solver = self.communicator().new_solver(context, options)?;
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

    pub fn delete_context(
        &self,
        context: ContextLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        if !self.try_resend_postponed_commands()? {
            self.postpone_command(RemoteCommand::Factory(RemoteFactoryCommand::DeleteContext(
                context,
            )));
        } else {
            self.inc_communication();
            self.communicator().delete_context(context)?;
            self.dec_communication();
        };
        self.active_contexts.write().unwrap().remove(&context);
        Ok(())
    }

    pub fn delete_solver(
        &self,
        context: ContextLabel,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        if !self.try_resend_postponed_commands()? {
            self.postpone_command(RemoteCommand::Factory(RemoteFactoryCommand::DeleteSolver(
                solver,
            )));
        } else {
            self.inc_communication();
            self.communicator().delete_solver(solver)?;
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

    pub fn assert(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Assert(solver, term.clone());
        self.save_solver_command(solver, command.clone())?;
        if !self.try_resend_postponed_commands()? {
            self.postpone_command(RemoteCommand::Solver(command));
        } else {
            self.inc_communication();
            self.communicator().assert(solver, term)?;
            self.dec_communication();
        };
        Ok(())
    }

    pub fn reset(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Reset(solver);
        self.save_solver_command(solver, command.clone())?;
        if !self.try_resend_postponed_commands()? {
            self.postpone_command(RemoteCommand::Solver(command));
        } else {
            self.inc_communication();
            self.communicator().reset(solver)?;
            self.dec_communication();
        };
        Ok(())
    }

    pub fn eval(
        &self,
        solver: SolverLabel,
        term: &Term,
    ) -> Result<Option<Term>, Box<dyn std::error::Error + Send + Sync>> {
        if !self.try_resend_postponed_commands()? {
            Err(Box::new(WorkerError {}))
        } else {
            self.inc_communication();
            let command_response = self.communicator().eval(solver, term)?;
            self.dec_communication();
            Ok(command_response)
        }
    }

    pub fn unsat_core(
        &self,
        solver: SolverLabel,
    ) -> Result<Vec<Term>, Box<dyn std::error::Error + Send + Sync>> {
        if !self.try_resend_postponed_commands()? {
            Err(Box::new(WorkerError {}))
        } else {
            self.inc_communication();
            let command_response = self.communicator().unsat_core(solver)?;
            self.dec_communication();
            Ok(command_response)
        }
    }

    pub fn interrupt(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        if *self.is_alive.lock().unwrap() {
            self.communicator().interrupt(solver)?;
        }
        Ok(())
    }

    pub fn check_sat(
        &self,
        solver: SolverLabel,
    ) -> Result<SolverResult, Box<dyn std::error::Error + Send + Sync>> {
        if !self.try_resend_postponed_commands()? {
            self.restart()?;
        }
        let command_response = self.communicator().check_sat(solver)?;
        Ok(command_response)
    }

    pub fn push(
        &self,
        solver: SolverLabel,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Push(solver);
        self.save_solver_command(solver, command.clone())?;
        if !self.try_resend_postponed_commands()? {
            self.postpone_command(RemoteCommand::Solver(command));
        } else {
            self.inc_communication();
            self.communicator().push(solver)?;
            self.dec_communication();
        };
        Ok(())
    }

    pub fn pop(
        &self,
        solver: SolverLabel,
        size: u64,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let command = RemoteSolverCommand::Pop(solver, size);
        self.save_solver_command(solver, command.clone())?;
        if !self.try_resend_postponed_commands()? {
            self.postpone_command(RemoteCommand::Solver(command));
        } else {
            self.inc_communication();
            self.communicator().pop(solver, size)?;
            self.dec_communication();
        };
        Ok(())
    }
}

#[derive(Clone)]
pub enum InterruptionType {
    Cancell,
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
            let s = s.clone();
            thread::spawn(move || {
                if let Some(timeout) = s.timeout {
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

            thread::spawn(move || {
                if let Ok(res) = s.check_sat() {
                    let _ = tx_check_sat.send(InterruptionType::Result(res, id));
                }
            });

            thread::spawn(move || {
                let _ = rx_cancell.recv();
                let _ = tx_check_sat2.send(InterruptionType::Cancell);
            });
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
    fn terminate(&self) {
        for solver in self.factories.iter() {
            solver.terminate().unwrap();
        }
    }

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
            last_fastest_solver_index: RwLock::new(Default::default()),
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

        let mut result = SolverResult::Unknown;
        while let InterruptionType::Result(res, count) = r_check_sat.recv().unwrap() {
            if SolverResult::Unknown == res {
                continue;
            }
            cancell.send(()).unwrap();
            *self.last_fastest_solver_index.write().unwrap() = count;
            result = res;
            break;
        }
        result
    }

    fn unsat_core(&self) -> Vec<Term> {
        let last_fastest_solver_index = { *self.last_fastest_solver_index.read().unwrap() };
        let solver = self.solvers.get(last_fastest_solver_index).unwrap();
        solver.unsat_core().unwrap()
    }

    fn eval(&self, term: &Term) -> Option<Term> {
        let last_fastest_solver_index = { *self.last_fastest_solver_index.read().unwrap() };
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

    factory.terminate();
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

    factory.terminate();
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

    factory.terminate();
}
