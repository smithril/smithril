use ipc_channel::ipc::{IpcReceiver, IpcSender};
use smithril::{
    converters::{self, Converter},
    generalized::{Context, Factory, Interrupter, Solver, SolverResult},
    solver::{
        ContextLabel, RemoteCommand, RemoteFactoryCommand, RemoteSolverCommand, RemoteState,
        RemoteWorkerCommunicator, SolverLabel,
    },
    term::Term,
};
use std::{
    collections::HashMap,
    env,
    sync::{Arc, RwLock},
    thread,
};

#[derive(Debug)]
pub struct RemoteCommander {
    pub command_receiver: IpcReceiver<RemoteCommand>,
    pub interrupt_receiver: IpcReceiver<SolverLabel>,
    pub check_state_receiver: IpcReceiver<()>,
    pub state_sender: IpcSender<RemoteState>,
    pub solver_result_sender: IpcSender<SolverResult>,
    pub new_solver_sender: IpcSender<SolverLabel>,
    pub new_context_sender: IpcSender<ContextLabel>,
    pub confirmation_sender: IpcSender<()>,
    pub eval_sender: IpcSender<Option<Term>>,
    pub unsat_core_sender: IpcSender<Vec<Term>>,
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let one_shot_server_name = &args[1];
    let serialized_converter = &args[2];
    let context_solver_id = &args[3];
    let converter_kind: Converter = serde_json::from_str(serialized_converter).unwrap();
    let (context_id, solver_id): (u64, u64) = serde_json::from_str(context_solver_id).unwrap();
    let tx = IpcSender::connect(one_shot_server_name.to_string()).unwrap();

    let (command_sender, command_receiver) = ipc_channel::ipc::channel::<RemoteCommand>().unwrap();
    let (interrupt_sender, interrupt_receiver) =
        ipc_channel::ipc::channel::<SolverLabel>().unwrap();
    let (check_state_sender, check_state_receiver) = ipc_channel::ipc::channel::<()>().unwrap();
    let (state_sender, state_receiver) = ipc_channel::ipc::channel::<RemoteState>().unwrap();
    let (solver_result_sender, solver_result_receiver) =
        ipc_channel::ipc::channel::<SolverResult>().unwrap();
    let (new_context_sender, new_context_receiver) =
        ipc_channel::ipc::channel::<ContextLabel>().unwrap();
    let (new_solver_sender, new_solver_receiver) =
        ipc_channel::ipc::channel::<SolverLabel>().unwrap();
    let (confirmation_sender, confirmation_receiver) = ipc_channel::ipc::channel::<()>().unwrap();
    let (eval_sender, eval_receiver) = ipc_channel::ipc::channel::<Option<Term>>().unwrap();
    let (unsat_core_sender, unsat_core_receiver) =
        ipc_channel::ipc::channel::<Vec<Term>>().unwrap();
    let remove_solver = RemoteWorkerCommunicator {
        solver_result_receiver,
        interrupt_sender,
        new_solver_receiver,
        new_context_receiver,
        check_state_sender,
        state_receiver,
        command_sender,
        confirmation_receiver,
        eval_receiver,
        unsat_core_receiver,
    };

    tx.send(remove_solver).unwrap();

    let remote_solver_commander = RemoteCommander {
        solver_result_sender,
        new_solver_sender,
        new_context_sender,
        interrupt_receiver,
        state_sender,
        check_state_receiver,
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
    let state = Arc::new(RwLock::new(RemoteState::Idle));
    {
        let interrupters = interrupters.clone();
        thread::spawn(move || loop {
            if let Ok(solver_label) = remote_commander.interrupt_receiver.recv() {
                let interrupters = interrupters.read().unwrap();
                if let Some(interrupter) = interrupters.get(&solver_label) {
                    interrupter.interrupt();
                }
            } else {
                break;
            }
        });
    }

    {
        let state = state.clone();
        thread::spawn(move || loop {
            if let Ok(()) = remote_commander.check_state_receiver.recv() {
                let state = *state.read().unwrap();
                remote_commander.state_sender.send(state).unwrap();
            } else {
                break;
            }
        });
    }

    loop {
        let command = remote_commander.command_receiver.recv().unwrap();
        match command {
            RemoteCommand::Solver(command) => match command {
                RemoteSolverCommand::Assert(solver_label, term) => {
                    let solver = solvers.get(&solver_label).unwrap().clone();
                    Solver::assert(solver.as_ref(), &term);
                    remote_commander.confirmation_sender.send(()).unwrap();
                }
                RemoteSolverCommand::Reset(solver_label) => {
                    let solver = solvers.get(&solver_label).unwrap().clone();
                    Solver::reset(solver.as_ref());
                    remote_commander.confirmation_sender.send(()).unwrap();
                }
                RemoteSolverCommand::CheckSat(solver_label) => {
                    {
                        let mut state = state.write().unwrap();
                        *state = RemoteState::Busy;
                    };
                    let result = if let Some(solver) = solvers.get(&solver_label) {
                        Solver::check_sat(solver.as_ref())
                    } else {
                        SolverResult::Unknown
                    };
                    {
                        let mut state = state.write().unwrap();
                        *state = RemoteState::Idle;
                    }
                    remote_commander.solver_result_sender.send(result).unwrap();
                }
                RemoteSolverCommand::UnsatCore(solver_label) => {
                    let solver = solvers.get(&solver_label).unwrap().clone();
                    let result = Solver::unsat_core(solver.as_ref());
                    remote_commander.unsat_core_sender.send(result).unwrap();
                }
                RemoteSolverCommand::Eval(solver_label, term) => {
                    let solver = solvers.get(&solver_label).unwrap().clone();
                    let result = Solver::eval(solver.as_ref(), &term);
                    remote_commander.eval_sender.send(result).unwrap();
                }
                RemoteSolverCommand::Push(solver_label) => {
                    let solver = solvers.get(&solver_label).unwrap().clone();
                    Solver::push(solver.as_ref());
                    remote_commander.confirmation_sender.send(()).unwrap();
                }
                RemoteSolverCommand::Pop(solver_label, size) => {
                    let solver = solvers.get(&solver_label).unwrap().clone();
                    Solver::pop(solver.as_ref(), size);
                    remote_commander.confirmation_sender.send(()).unwrap();
                }
            },
            RemoteCommand::Factory(command) => match command {
                RemoteFactoryCommand::NewContext() => {
                    let context = factory.new_context();
                    context_id += 1;
                    let context_label = ContextLabel(context_id);
                    contexts.insert(context_label, context);
                    remote_commander
                        .new_context_sender
                        .send(context_label)
                        .unwrap();
                }
                RemoteFactoryCommand::DeleteContext(context_label) => {
                    contexts.remove(&context_label);
                    remote_commander.confirmation_sender.send(()).unwrap();
                }
                RemoteFactoryCommand::DeleteSolver(solver_label) => {
                    solvers.remove(&solver_label);
                    remote_commander.confirmation_sender.send(()).unwrap();
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
                    remote_commander
                        .new_solver_sender
                        .send(solver_label)
                        .unwrap();
                }
                RemoteFactoryCommand::RestoreContext(context_label) => {
                    let context = factory.new_context();
                    contexts.insert(context_label, context);
                    remote_commander.confirmation_sender.send(()).unwrap();
                }
                RemoteFactoryCommand::RestoreSolver(context_label, solver_label, options) => {
                    let context = contexts.get(&context_label).unwrap();
                    let solver = factory.new_solver(context.clone(), &options);
                    let interrupter = Arc::new(factory.new_interrupter(solver.clone()));
                    solvers.insert(solver_label, solver);
                    interrupters
                        .write()
                        .unwrap()
                        .insert(solver_label, interrupter.clone());
                    remote_commander.confirmation_sender.send(()).unwrap();
                }
            },
        }
    }
}
