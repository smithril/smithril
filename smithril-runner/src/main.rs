use ipc_channel::ipc::IpcSender;
use smithril::{
    converters::{self, Converter},
    generalized::SolverResult,
    runner::{start, IpcInterrupCommander, IpcTerminateCommander, IpcWorkerCommander},
    solver::{ContextLabel, IpcWorkerChannels, RemoteCommand, RemoteState, SolverLabel},
    term::Term,
};
use std::env;

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
    let (terminate_sender, terminate_receiver) = ipc_channel::ipc::channel::<()>().unwrap();
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
    let remove_solver = IpcWorkerChannels {
        solver_result_receiver,
        interrupt_sender,
        terminate_sender,
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

    let remote_terminate_commander = IpcTerminateCommander { terminate_receiver };
    let remote_interrupt_commander = IpcInterrupCommander { interrupt_receiver };

    let remote_solver_commander = IpcWorkerCommander {
        solver_result_sender,
        new_solver_sender,
        new_context_sender,
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
            start(
                &mut factory,
                remote_solver_commander,
                remote_interrupt_commander,
                remote_terminate_commander,
                context_id,
                solver_id,
            )
        }
        Converter::Z3 => {
            let mut factory = converters::mk_z3_factory();
            start(
                &mut factory,
                remote_solver_commander,
                remote_interrupt_commander,
                remote_terminate_commander,
                context_id,
                solver_id,
            )
        }
        Converter::Dummy => {
            let mut factory = converters::mk_dummy_factory();
            start(
                &mut factory,
                remote_solver_commander,
                remote_interrupt_commander,
                remote_terminate_commander,
                context_id,
                solver_id,
            )
        }
    };
}
