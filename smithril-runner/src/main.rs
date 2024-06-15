use ipc_channel::ipc::{IpcReceiver, IpcSender};
use smithril_lib::{
    converters::{self, Converter},
    generalized::{GeneralSolver, SolverResult},
    solver::{RemoteSolver, SolverCommand, SolverCommandResponse},
};
use std::env;

#[derive(Debug)]
pub struct RemoteSolverCommander {
    pub command_receiver: IpcReceiver<SolverCommand>,
    pub response_sender: IpcSender<SolverCommandResponse>,
    pub solver_result_sender: IpcSender<SolverResult>,
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let one_shot_server_name = &args[1];
    let tx = IpcSender::connect(one_shot_server_name.to_string()).unwrap();

    let (command_sender, command_receiver) = ipc_channel::ipc::channel::<SolverCommand>().unwrap();
    let (response_sender, response_receiver) =
        ipc_channel::ipc::channel::<SolverCommandResponse>().unwrap();
    let (solver_result_sender, solver_result_receiver) =
        ipc_channel::ipc::channel::<SolverResult>().unwrap();
    let remove_solver = RemoteSolver {
        command_sender,
        response_receiver,
        solver_result_receiver,
    };

    tx.send(remove_solver).unwrap();

    let remote_solver_commander = RemoteSolverCommander {
        command_receiver,
        response_sender,
        solver_result_sender,
    };

    let mut converter: Option<Box<dyn GeneralSolver>> = Option::None;
    while let Ok(command) = remote_solver_commander.command_receiver.recv() {
        match command {
            SolverCommand::Init(converter_kind) => {
                converter = match converter_kind {
                    Converter::Bitwuzla => Some(Box::new(converters::mk_bitwulza())),
                    Converter::Z3 => Some(Box::new(converters::mk_z3())),
                };
                remote_solver_commander
                    .response_sender
                    .send(SolverCommandResponse::Success())
                    .unwrap();
            }
            SolverCommand::Assert(term) => match converter.as_ref() {
                Some(converter) => {
                    converter.assert(&term);
                    remote_solver_commander
                        .response_sender
                        .send(SolverCommandResponse::Success())
                        .unwrap();
                }
                None => {
                    remote_solver_commander
                        .response_sender
                        .send(SolverCommandResponse::Error(
                            "No one converter has set up!".to_string(),
                        ))
                        .unwrap();
                }
            },
            SolverCommand::Reset() => match converter.as_mut() {
                Some(converter) => {
                    converter.reset();
                    remote_solver_commander
                        .response_sender
                        .send(SolverCommandResponse::Success())
                        .unwrap();
                }
                None => {
                    remote_solver_commander
                        .response_sender
                        .send(SolverCommandResponse::Error(
                            "No one converter has set up!".to_string(),
                        ))
                        .unwrap();
                }
            },
            SolverCommand::CheckSat() => match converter.as_ref() {
                Some(converter) => {
                    let result = converter.check_sat();
                    remote_solver_commander
                        .solver_result_sender
                        .send(result)
                        .unwrap();
                }
                None => {
                    remote_solver_commander
                        .response_sender
                        .send(SolverCommandResponse::Error(
                            "No one converter has set up!".to_string(),
                        ))
                        .unwrap();
                }
            },
        }
    }
}
