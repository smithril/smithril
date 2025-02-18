use crossbeam_channel::{unbounded, Receiver, Sender};
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

#[derive(Debug)]
pub struct RemoteCommander {
    pub command_receiver: Receiver<RemoteCommand>,
    pub interrupt_receiver: Receiver<SolverLabel>,
    pub terminate_receiver: Receiver<()>,
    pub state_sender: Sender<RemoteState>,
    pub solver_result_sender: Sender<SolverResult>,
    pub new_solver_sender: Sender<SolverLabel>,
    pub new_context_sender: Sender<ContextLabel>,
    pub confirmation_sender: Sender<()>,
    pub eval_sender: Sender<Option<Term>>,
    pub unsat_core_sender: Sender<Vec<Term>>,
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

    let remote_solver_commander = RemoteCommander {
        solver_result_sender,
        new_solver_sender,
        new_context_sender,
        interrupt_receiver,
        state_sender,
        terminate_receiver,
        command_receiver,
        confirmation_sender,
        eval_sender,
        unsat_core_sender,
    };

    match converter_kind {
        Converter::Bitwuzla => {
            let mut factory = converters::mk_bitwuzla_factory();
            start(&mut factory, remote_solver_commander, context_id, solver_id)
        }
        Converter::Z3 => {
            let mut factory = converters::mk_z3_factory();
            start(&mut factory, remote_solver_commander, context_id, solver_id)
        }
        Converter::Dummy => {
            let mut factory = converters::mk_dummy_factory();
            start(&mut factory, remote_solver_commander, context_id, solver_id)
        }
    };
}

fn start<
    C: Context,
    SL: Solver + Send + Sync + 'static,
    GF: Factory<C, SL, I>,
    I: Interrupter + Send + Sync + 'static,
>(
    factory: &mut GF,
    remote_commander: RemoteCommander,
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
                    let solver_label = remote_commander.interrupt_receiver.recv()?;
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
                remote_commander.terminate_receiver.recv()?;
                *is_alive.write().unwrap() = false;
                Ok(())
            };
            let _ = terminate_loop();
        });
    }

    let mut command_loop = || -> Result<(), Box<dyn Error>> {
        loop {
            if *is_alive.read().unwrap() {
                let command = remote_commander.command_receiver.recv()?;
                match command {
                    RemoteCommand::Solver(command) => match command {
                        RemoteSolverCommand::Assert(solver_label, term) => {
                            let solver = solvers.get(&solver_label).unwrap().clone();
                            Solver::assert(solver.as_ref(), &term);
                            remote_commander.confirmation_sender.send(())?;
                        }
                        RemoteSolverCommand::Reset(solver_label) => {
                            let solver = solvers.get(&solver_label).unwrap().clone();
                            Solver::reset(solver.as_ref());
                            remote_commander.confirmation_sender.send(())?;
                        }
                        RemoteSolverCommand::CheckSat(solver_label) => {
                            let result =
                                Solver::check_sat(solvers.get(&solver_label).unwrap().as_ref());
                            remote_commander.solver_result_sender.send(result)?;
                        }
                        RemoteSolverCommand::UnsatCore(solver_label) => {
                            let solver = solvers.get(&solver_label).unwrap().clone();
                            let result = Solver::unsat_core(solver.as_ref());
                            remote_commander.unsat_core_sender.send(result)?;
                        }
                        RemoteSolverCommand::Eval(solver_label, term) => {
                            let solver = solvers.get(&solver_label).unwrap().clone();
                            let result = Solver::eval(solver.as_ref(), &term);
                            remote_commander.eval_sender.send(result)?;
                        }
                        RemoteSolverCommand::Push(solver_label) => {
                            let solver = solvers.get(&solver_label).unwrap().clone();
                            Solver::push(solver.as_ref());
                            remote_commander.confirmation_sender.send(())?;
                        }
                        RemoteSolverCommand::Pop(solver_label, size) => {
                            let solver = solvers.get(&solver_label).unwrap().clone();
                            Solver::pop(solver.as_ref(), size);
                            remote_commander.confirmation_sender.send(())?;
                        }
                    },
                    RemoteCommand::Factory(command) => match command {
                        RemoteFactoryCommand::NewContext() => {
                            let context = factory.new_context();
                            context_id += 1;
                            let context_label = ContextLabel(context_id);
                            contexts.insert(context_label, context);
                            remote_commander.new_context_sender.send(context_label)?;
                        }
                        RemoteFactoryCommand::DeleteContext(context_label) => {
                            contexts.remove(&context_label);
                            remote_commander.confirmation_sender.send(())?;
                        }
                        RemoteFactoryCommand::DeleteSolver(solver_label) => {
                            solvers.remove(&solver_label);
                            remote_commander.confirmation_sender.send(())?;
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
                            remote_commander.new_solver_sender.send(solver_label)?;
                        }
                        RemoteFactoryCommand::RestoreContext(context_label) => {
                            let context = factory.new_context();
                            contexts.insert(context_label, context);
                            remote_commander.confirmation_sender.send(())?;
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
                            remote_commander.confirmation_sender.send(())?;
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
