use ipc_channel::ipc::{IpcReceiver, IpcSender};
use smithril_lib::{
    converters::{self, Converter},
    generalized::{Solver, SolverResult},
    solver::{RemoteSolver, SolverCommand, SolverCommandResponse},
};
use std::{env, rc::Rc, sync::Arc, thread};

#[derive(Debug)]
pub struct RemoteSolverCommander {
    pub command_receiver: IpcReceiver<SolverCommand>,
    pub response_sender: IpcSender<SolverCommandResponse>,
    pub solver_result_sender: IpcSender<SolverResult>,
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let one_shot_server_name = &args[1];
    let serialized_converter = &args[2];
    let converter_kind: Converter = serde_json::from_str(serialized_converter).unwrap();
    let tx = IpcSender::connect(one_shot_server_name.to_string()).unwrap();

    let (command_sender, command_receiver) = ipc_channel::ipc::channel::<SolverCommand>().unwrap();
    let (interrupt_sender, interrupt_receiver) = ipc_channel::ipc::channel::<()>().unwrap();
    let (response_sender, response_receiver) =
        ipc_channel::ipc::channel::<SolverCommandResponse>().unwrap();
    let (solver_result_sender, solver_result_receiver) =
        ipc_channel::ipc::channel::<SolverResult>().unwrap();
    let remove_solver = RemoteSolver {
        command_sender,
        response_receiver,
        solver_result_receiver,
        interrupt_sender,
    };

    tx.send(remove_solver).unwrap();

    let remote_solver_commander = RemoteSolverCommander {
        command_receiver,
        response_sender,
        solver_result_sender,
    };

    let converter: Box<dyn Solver + Send + Sync> = match converter_kind {
        Converter::Bitwuzla => Box::new(converters::mk_bitwuzla_solver(Rc::new(
            converters::mk_bitwuzla_converter(),
        ))),
        Converter::Z3 => Box::new(converters::mk_z3_solver(Rc::new(
            converters::mk_z3_converter(),
        ))),
    };
    let converter = Arc::new(converter);

    {
        let converter = converter.clone();
        thread::spawn(move || loop {
            interrupt_receiver.recv().unwrap();
            converter.interrupt();
        });
    }

    loop {
        let command = remote_solver_commander.command_receiver.recv().unwrap();
        match command {
            SolverCommand::Assert(term) => {
                converter.assert(&term);
                remote_solver_commander
                    .response_sender
                    .send(SolverCommandResponse::Success())
                    .unwrap();
            }
            SolverCommand::Reset() => {
                converter.reset();
                remote_solver_commander
                    .response_sender
                    .send(SolverCommandResponse::Success())
                    .unwrap();
            }
            SolverCommand::CheckSat() => {
                let result = converter.check_sat();
                remote_solver_commander
                    .solver_result_sender
                    .send(result)
                    .unwrap();
            }
        }
    }
}
