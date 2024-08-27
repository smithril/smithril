use ipc_channel::ipc::{IpcReceiver, IpcSender};
use smithril_lib::{
    converters::{self, Converter},
    generalized::{
        GeneralConverter, GeneralFactory, GeneralOptions, GeneralSolver, GeneralSort, GeneralTerm,
        Interrupter, Solver, SolverResult,
    },
    solver::{ContextLabel, OptionsLabel, RemoteCommand, RemoteWorker, SolverLabel},
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
    pub solver_result_sender: IpcSender<SolverResult>,
    pub new_solver_sender: IpcSender<SolverLabel>,
    pub new_options_sender: IpcSender<OptionsLabel>,
    pub new_context_sender: IpcSender<ContextLabel>,
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let one_shot_server_name = &args[1];
    let serialized_converter = &args[2];
    let converter_kind: Converter = serde_json::from_str(serialized_converter).unwrap();
    let tx = IpcSender::connect(one_shot_server_name.to_string()).unwrap();

    let (command_sender, command_receiver) = ipc_channel::ipc::channel::<RemoteCommand>().unwrap();
    let (interrupt_sender, interrupt_receiver) =
        ipc_channel::ipc::channel::<SolverLabel>().unwrap();
    let (solver_result_sender, solver_result_receiver) =
        ipc_channel::ipc::channel::<SolverResult>().unwrap();
    let (new_context_sender, new_context_receiver) =
        ipc_channel::ipc::channel::<ContextLabel>().unwrap();
    let (new_options_sender, new_options_receiver) =
        ipc_channel::ipc::channel::<OptionsLabel>().unwrap();
    let (new_solver_sender, new_solver_receiver) =
        ipc_channel::ipc::channel::<SolverLabel>().unwrap();
    let remove_solver = RemoteWorker {
        command_sender,
        solver_result_receiver,
        interrupt_sender,
        new_solver_receiver,
        new_context_receiver,
        new_options_receiver,
    };

    tx.send(remove_solver).unwrap();

    let remote_solver_commander = RemoteCommander {
        command_receiver,
        solver_result_sender,
        new_solver_sender,
        new_context_sender,
        interrupt_receiver,
        new_options_sender,
    };

    match converter_kind {
        Converter::Bitwuzla => {
            let mut factory = converters::mk_bitwuzla_factory();
            start(&mut factory, remote_solver_commander)
        }
        Converter::Z3 => {
            let mut factory = converters::mk_z3_factory();
            start(&mut factory, remote_solver_commander)
        }
    };
}

fn start<
    S: GeneralSort,
    T: GeneralTerm,
    O: GeneralOptions,
    C: GeneralConverter<S, T>,
    SL: GeneralSolver<S, T, O, C> + Solver,
    GF: GeneralFactory<S, T, O, C, SL, I>,
    I: Interrupter + Send + Sync + 'static,
>(
    factory: &mut GF,
    remote_commander: RemoteCommander,
) {
    let mut context_id = 0;
    let mut contexts = HashMap::new();
    let mut solver_id = 0;
    let mut solvers = HashMap::new();
    let interrupters: Arc<RwLock<HashMap<SolverLabel, Arc<I>>>> =
        Arc::new(RwLock::new(HashMap::new()));
    {
        let interrupters = interrupters.clone();
        thread::spawn(move || loop {
            let solver_label = remote_commander.interrupt_receiver.recv().unwrap();
            let interrupters = interrupters.read().unwrap();
            let interrupter = interrupters.get(&solver_label).unwrap();
            interrupter.interrupt();
        });
    }

    loop {
        let command = remote_commander.command_receiver.recv().unwrap();
        match command {
            RemoteCommand::NewContext() => {
                let context = factory.new_context();
                context_id += 1;
                let context_label = ContextLabel(context_id);
                contexts.insert(context_label, context);
                remote_commander
                    .new_context_sender
                    .send(context_label)
                    .unwrap();
            }
            RemoteCommand::NewSolver(context_label) => {
                let context = contexts.get(&context_label).unwrap();
                let solver = factory.new_solver(context.clone());
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
            RemoteCommand::DeleteContext(context_label) => {
                contexts.remove(&context_label);
            }
            RemoteCommand::DeleteSolver(solver_label) => {
                solvers.remove(&solver_label);
            }
            RemoteCommand::Assert(solver_lable, term) => {
                let solver = solvers.get(&solver_lable).unwrap();
                Solver::assert(solver.as_ref(), &term);
            }
            RemoteCommand::Reset(solver_lable) => {
                let solver = solvers.get(&solver_lable).unwrap();
                Solver::reset(solver.as_ref());
            }
            RemoteCommand::CheckSat(solver_lable) => {
                let solver = solvers.get(&solver_lable).unwrap();
                let result = Solver::check_sat(solver.as_ref());
                remote_commander.solver_result_sender.send(result).unwrap();
            }
            RemoteCommand::NewSolverWithOptions(context_label, options) => {
                let context = contexts.get(&context_label).unwrap();
                let solver = factory.new_solver_with_options(context.clone(), &options);
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
        }
    }
}
