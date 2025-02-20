use crossbeam_channel::{unbounded, Receiver, Sender};
use ipc_channel::ipc::{IpcReceiver, IpcSender};
use std::{
    collections::HashMap,
    error::Error,
    sync::{Arc, RwLock},
    thread,
};

use crate::{
    capi::SolverResult,
    converters::{self, Converter},
    generalized::{Context, Factory, Interrupter, Solver},
    solver::{
        ContextLabel, CrossbeamWorkerCommunicator, RemoteCommand, RemoteFactoryCommand,
        RemoteSolverCommand, RemoteState, SolverLabel,
    },
    term::Term,
};

pub trait InterruptCommander {
    fn receive_interrupt(&self) -> Result<SolverLabel, Box<dyn Error>>;
}

pub trait TerminateCommander {
    fn receive_terminate(&self) -> Result<(), Box<dyn Error>>;
}

pub trait WorkerCommander {
    fn receive_command(&self) -> Result<RemoteCommand, Box<dyn Error>>;
    fn send_state(&self, state: RemoteState) -> Result<(), Box<dyn Error>>;
    fn send_solver_result(&self, solver_result: SolverResult) -> Result<(), Box<dyn Error>>;
    fn send_new_solver(&self, new_solver: SolverLabel) -> Result<(), Box<dyn Error>>;
    fn send_new_context(&self, new_context: ContextLabel) -> Result<(), Box<dyn Error>>;
    fn send_confirmation(&self) -> Result<(), Box<dyn Error>>;
    fn send_eval(&self, term: Option<Term>) -> Result<(), Box<dyn Error>>;
    fn send_unsat_core(&self, unsat_core: Vec<Term>) -> Result<(), Box<dyn Error>>;
}

#[derive(Debug, Clone)]
pub struct CrossbeamInterruptCommander {
    pub interrupt_receiver: Receiver<SolverLabel>,
    pub terminate_receiver: Receiver<()>,
}

#[derive(Debug, Clone)]
pub struct CrossbeamWorkerCommander {
    pub command_receiver: Receiver<RemoteCommand>,
    pub state_sender: Sender<RemoteState>,
    pub solver_result_sender: Sender<SolverResult>,
    pub new_solver_sender: Sender<SolverLabel>,
    pub new_context_sender: Sender<ContextLabel>,
    pub confirmation_sender: Sender<()>,
    pub eval_sender: Sender<Option<Term>>,
    pub unsat_core_sender: Sender<Vec<Term>>,
}

impl InterruptCommander for CrossbeamInterruptCommander {
    fn receive_interrupt(&self) -> Result<SolverLabel, Box<dyn Error>> {
        let interrupt = self.interrupt_receiver.recv()?;
        Ok(interrupt)
    }
}

impl TerminateCommander for CrossbeamInterruptCommander {
    fn receive_terminate(&self) -> Result<(), Box<dyn Error>> {
        self.terminate_receiver.recv()?;
        Ok(())
    }
}

impl WorkerCommander for CrossbeamWorkerCommander {
    fn receive_command(&self) -> Result<RemoteCommand, Box<dyn Error>> {
        let command = self.command_receiver.recv()?;
        Ok(command)
    }

    fn send_state(&self, state: RemoteState) -> Result<(), Box<dyn Error>> {
        self.state_sender.send(state)?;
        Ok(())
    }

    fn send_solver_result(&self, solver_result: SolverResult) -> Result<(), Box<dyn Error>> {
        self.solver_result_sender.send(solver_result)?;
        Ok(())
    }

    fn send_new_solver(&self, new_solver: SolverLabel) -> Result<(), Box<dyn Error>> {
        self.new_solver_sender.send(new_solver)?;
        Ok(())
    }

    fn send_new_context(&self, new_context: ContextLabel) -> Result<(), Box<dyn Error>> {
        self.new_context_sender.send(new_context)?;
        Ok(())
    }

    fn send_confirmation(&self) -> Result<(), Box<dyn Error>> {
        self.confirmation_sender.send(())?;
        Ok(())
    }

    fn send_eval(&self, term: Option<Term>) -> Result<(), Box<dyn Error>> {
        self.eval_sender.send(term)?;
        Ok(())
    }

    fn send_unsat_core(&self, unsat_core: Vec<Term>) -> Result<(), Box<dyn Error>> {
        self.unsat_core_sender.send(unsat_core)?;
        Ok(())
    }
}

pub fn run(
    communicator_sender: Sender<CrossbeamWorkerCommunicator>,
    serialized_converter: String,
    context_solver_id: String,
) {
    let converter_kind: Converter = serde_json::from_str(serialized_converter.as_str()).unwrap();
    let (context_id, solver_id): (u64, u64) =
        serde_json::from_str(context_solver_id.as_str()).unwrap();

    let (command_sender, command_receiver) = unbounded();
    let (interrupt_sender, interrupt_receiver) = unbounded();
    let (terminate_sender, terminate_receiver) = unbounded();
    let (state_sender, state_receiver) = unbounded();
    let (solver_result_sender, solver_result_receiver) = unbounded();
    let (new_context_sender, new_context_receiver) = unbounded();
    let (new_solver_sender, new_solver_receiver) = unbounded();
    let (confirmation_sender, confirmation_receiver) = unbounded();
    let (eval_sender, eval_receiver) = unbounded();
    let (unsat_core_sender, unsat_core_receiver) = unbounded();
    let remove_solver = CrossbeamWorkerCommunicator {
        solver_result_receiver,
        interrupt_sender,
        new_solver_receiver,
        new_context_receiver,
        terminate_sender,
        state_receiver,
        command_sender,
        confirmation_receiver,
        eval_receiver,
        unsat_core_receiver,
    };

    communicator_sender.send(remove_solver).unwrap();

    let remote_solver_commander = CrossbeamWorkerCommander {
        solver_result_sender,
        new_solver_sender,
        new_context_sender,
        state_sender,
        command_receiver,
        confirmation_sender,
        eval_sender,
        unsat_core_sender,
    };

    let remote_interrupt_commander = CrossbeamInterruptCommander {
        interrupt_receiver,
        terminate_receiver,
    };

    match converter_kind {
        Converter::Bitwuzla => {
            let mut factory = converters::mk_bitwuzla_factory();
            start(
                &mut factory,
                remote_solver_commander,
                remote_interrupt_commander.clone(),
                remote_interrupt_commander,
                context_id,
                solver_id,
            )
        }
        Converter::Z3 => {
            let mut factory = converters::mk_z3_factory();
            start(
                &mut factory,
                remote_solver_commander,
                remote_interrupt_commander.clone(),
                remote_interrupt_commander,
                context_id,
                solver_id,
            )
        }
        Converter::Dummy => {
            let mut factory = converters::mk_dummy_factory();
            start(
                &mut factory,
                remote_solver_commander,
                remote_interrupt_commander.clone(),
                remote_interrupt_commander,
                context_id,
                solver_id,
            )
        }
    };
}

#[derive(Debug)]
pub struct IpcInterrupCommander {
    pub interrupt_receiver: IpcReceiver<SolverLabel>,
}

#[derive(Debug)]
pub struct IpcTerminateCommander {
    pub terminate_receiver: IpcReceiver<()>,
}

#[derive(Debug)]
pub struct IpcWorkerCommander {
    pub command_receiver: IpcReceiver<RemoteCommand>,
    pub check_state_receiver: IpcReceiver<()>,
    pub state_sender: IpcSender<RemoteState>,
    pub solver_result_sender: IpcSender<SolverResult>,
    pub new_solver_sender: IpcSender<SolverLabel>,
    pub new_context_sender: IpcSender<ContextLabel>,
    pub confirmation_sender: IpcSender<()>,
    pub eval_sender: IpcSender<Option<Term>>,
    pub unsat_core_sender: IpcSender<Vec<Term>>,
}

impl InterruptCommander for IpcInterrupCommander {
    fn receive_interrupt(&self) -> Result<SolverLabel, Box<dyn Error>> {
        let interrupt = self.interrupt_receiver.recv()?;
        Ok(interrupt)
    }
}

impl TerminateCommander for IpcTerminateCommander {
    fn receive_terminate(&self) -> Result<(), Box<dyn Error>> {
        self.terminate_receiver.recv()?;
        Ok(())
    }
}

impl WorkerCommander for IpcWorkerCommander {
    fn receive_command(&self) -> Result<RemoteCommand, Box<dyn Error>> {
        let command = self.command_receiver.recv()?;
        Ok(command)
    }

    fn send_state(&self, state: RemoteState) -> Result<(), Box<dyn Error>> {
        self.state_sender.send(state)?;
        Ok(())
    }

    fn send_solver_result(&self, solver_result: SolverResult) -> Result<(), Box<dyn Error>> {
        self.solver_result_sender.send(solver_result)?;
        Ok(())
    }

    fn send_new_solver(&self, new_solver: SolverLabel) -> Result<(), Box<dyn Error>> {
        self.new_solver_sender.send(new_solver)?;
        Ok(())
    }

    fn send_new_context(&self, new_context: ContextLabel) -> Result<(), Box<dyn Error>> {
        self.new_context_sender.send(new_context)?;
        Ok(())
    }

    fn send_confirmation(&self) -> Result<(), Box<dyn Error>> {
        self.confirmation_sender.send(())?;
        Ok(())
    }

    fn send_eval(&self, term: Option<Term>) -> Result<(), Box<dyn Error>> {
        self.eval_sender.send(term)?;
        Ok(())
    }

    fn send_unsat_core(&self, unsat_core: Vec<Term>) -> Result<(), Box<dyn Error>> {
        self.unsat_core_sender.send(unsat_core)?;
        Ok(())
    }
}

pub fn start<
    C: Context,
    SL: Solver + Send + Sync + 'static,
    GF: Factory<C, SL, I>,
    I: Interrupter + Send + Sync + 'static,
    WC: WorkerCommander + Send + 'static,
    IC: InterruptCommander + Send + 'static,
    TC: TerminateCommander + Send + 'static,
>(
    factory: &mut GF,
    worker_commander: WC,
    interrupt_commander: IC,
    terminate_commander: TC,
    context_id: u64,
    solver_id: u64,
) {
    let mut context_id = context_id;
    let mut contexts = HashMap::new();
    let mut solver_id = solver_id;
    let mut solvers: HashMap<SolverLabel, Arc<SL>> = HashMap::new();
    let interrupters: Arc<RwLock<HashMap<SolverLabel, Arc<I>>>> =
        Arc::new(RwLock::new(HashMap::new()));
    let is_alive: Arc<RwLock<bool>> = Arc::new(RwLock::new(true));

    {
        let interrupters = interrupters.clone();
        thread::spawn(move || {
            let interrupter_loop = || -> Result<(), Box<dyn Error>> {
                loop {
                    let solver_label = interrupt_commander.receive_interrupt()?;
                    let interrupters = interrupters.read().unwrap();
                    if let Some(interrupter) = interrupters.get(&solver_label) {
                        interrupter.interrupt();
                    }
                }
            };
            let _ = interrupter_loop();
        });
    }

    {
        let is_alive = is_alive.clone();
        thread::spawn(move || {
            let terminate_loop = || -> Result<(), Box<dyn Error>> {
                terminate_commander.receive_terminate()?;
                *is_alive.write().unwrap() = false;
                Ok(())
            };
            let _ = terminate_loop();
        });
    }

    let mut command_loop = || -> Result<(), Box<dyn Error>> {
        loop {
            if *is_alive.read().unwrap() {
                let command = worker_commander.receive_command()?;
                match command {
                    RemoteCommand::Solver(command) => match command {
                        RemoteSolverCommand::Assert(solver_label, term) => {
                            let solver = solvers.get(&solver_label).unwrap().clone();
                            Solver::assert(solver.as_ref(), &term);
                            worker_commander.send_confirmation()?;
                        }
                        RemoteSolverCommand::Reset(solver_label) => {
                            let solver = solvers.get(&solver_label).unwrap().clone();
                            Solver::reset(solver.as_ref());
                            worker_commander.send_confirmation()?;
                        }
                        RemoteSolverCommand::CheckSat(solver_label) => {
                            let result =
                                Solver::check_sat(solvers.get(&solver_label).unwrap().as_ref());
                            worker_commander.send_solver_result(result)?;
                        }
                        RemoteSolverCommand::UnsatCore(solver_label) => {
                            let solver = solvers.get(&solver_label).unwrap().clone();
                            let result = Solver::unsat_core(solver.as_ref());
                            worker_commander.send_unsat_core(result)?;
                        }
                        RemoteSolverCommand::Eval(solver_label, term) => {
                            let solver = solvers.get(&solver_label).unwrap().clone();
                            let result = Solver::eval(solver.as_ref(), &term);
                            worker_commander.send_eval(result)?;
                        }
                        RemoteSolverCommand::Push(solver_label) => {
                            let solver = solvers.get(&solver_label).unwrap().clone();
                            Solver::push(solver.as_ref());
                            worker_commander.send_confirmation()?;
                        }
                        RemoteSolverCommand::Pop(solver_label, size) => {
                            let solver = solvers.get(&solver_label).unwrap().clone();
                            Solver::pop(solver.as_ref(), size);
                            worker_commander.send_confirmation()?;
                        }
                    },
                    RemoteCommand::Factory(command) => match command {
                        RemoteFactoryCommand::NewContext() => {
                            let context = factory.new_context();
                            context_id += 1;
                            let context_label = ContextLabel(context_id);
                            contexts.insert(context_label, context);
                            worker_commander.send_new_context(context_label)?;
                        }
                        RemoteFactoryCommand::DeleteContext(context_label) => {
                            contexts.remove(&context_label);
                            worker_commander.send_confirmation()?;
                        }
                        RemoteFactoryCommand::DeleteSolver(solver_label) => {
                            solvers.remove(&solver_label);
                            worker_commander.send_confirmation()?;
                        }
                        RemoteFactoryCommand::NewSolver(context_label, options) => {
                            let context = contexts.get(&context_label).unwrap();
                            let solver = factory.new_solver(context.clone(), &options);
                            let interrupter = Arc::new(factory.new_interrupter(solver.clone()));
                            solver_id += 1;
                            let solver_label = SolverLabel(solver_id);
                            solvers.insert(solver_label, solver);
                            interrupters
                                .write()
                                .unwrap()
                                .insert(solver_label, interrupter.clone());
                            worker_commander.send_new_solver(solver_label)?;
                        }
                        RemoteFactoryCommand::RestoreContext(context_label) => {
                            let context = factory.new_context();
                            contexts.insert(context_label, context);
                            worker_commander.send_confirmation()?;
                        }
                        RemoteFactoryCommand::RestoreSolver(
                            context_label,
                            solver_label,
                            options,
                        ) => {
                            let context = contexts.get(&context_label).unwrap();
                            let solver = factory.new_solver(context.clone(), &options);
                            let interrupter = Arc::new(factory.new_interrupter(solver.clone()));
                            solvers.insert(solver_label, solver);
                            interrupters
                                .write()
                                .unwrap()
                                .insert(solver_label, interrupter.clone());
                            worker_commander.send_confirmation()?;
                        }
                    },
                }
            } else {
                break Ok(());
            }
        }
    };
    let _ = command_loop();
}
