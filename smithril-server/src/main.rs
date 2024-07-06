use ipc_channel::ipc::{IpcReceiver, IpcSender};
use smithril_lib::{
    converters::{self, ClientMessageType, ServerMessageType},
    generalized::GeneralSolver,
};
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();

    let one_shot_server_name = &args[1];
    let tx = IpcSender::connect(one_shot_server_name.to_string()).unwrap();

    let (server_tx, server_rx) = ipc_channel::ipc::channel::<ClientMessageType>().unwrap();
    let (client_tx, client_rx) = ipc_channel::ipc::channel::<ServerMessageType>().unwrap();

    tx.send((server_tx, client_rx)).unwrap();

    let receiver: IpcReceiver<ClientMessageType> = server_rx;
    let sender: IpcSender<ServerMessageType> = client_tx;
    let mut conv: Option<Box<dyn GeneralSolver>> = Option::None;

    // Receive the converter setup message
    while let Ok(cur_line) = receiver.recv() {
        match cur_line {
            ClientMessageType::Converter(converter) => match converter {
                converters::ConverterType::Bitwuzla => {
                    sender
                        .send(ServerMessageType::Txt(
                            "Bitwuzla converter has set up".to_string(),
                        ))
                        .unwrap();
                    conv = Some(Box::new(converters::mk_bitwulza()));
                }
                converters::ConverterType::Z3 => {
                    sender
                        .send(ServerMessageType::Txt(
                            "Z3 converter has set up".to_string(),
                        ))
                        .unwrap();
                    conv = Some(Box::new(converters::mk_z3()));
                }
            },
            // ClientMessageType::Query(input_query) => {
            //     let output: SolverResult = match conv.as_ref() {
            //         Some(conv) => solve_problem(conv.as_ref(), input_query),
            //         None => SolverResult::Unknown,
            //     };
            //     sender.send(ServerMessageType::Result(output)).unwrap();
            // }
            ClientMessageType::Assert(input_query) => {
                match conv.as_ref() {
                    Some(conv) => {
                        conv.assert(&input_query.query);
                        sender
                            .send(ServerMessageType::Txt("Assert successful".to_string()))
                            .unwrap();
                    }
                    None => sender
                        .send(ServerMessageType::Txt(
                            "Converter is not set up".to_string(),
                        ))
                        .unwrap(),
                };
            }
            ClientMessageType::CheckSat() => {
                match conv.as_ref() {
                    Some(conv) => {
                        let output = conv.check_sat();
                        sender.send(ServerMessageType::Result(output)).unwrap();
                    }
                    None => sender
                        .send(ServerMessageType::Txt(
                            "Converter is not set up".to_string(),
                        ))
                        .unwrap(),
                };
            } //mixa117 assert and check
              //mixa117 test for GeneralSolver in lib.rs
              //mixa117 evaluate (term) get_model
              //mixa117 unsat_core
              //push GeneralSolver+tests (without client/server)
        }
    }
}

// fn solve_problem<'a>(converter: &'a dyn GeneralSolver, input: SolverQuery) -> SolverResult {
//     converter.assert(&input.query);
//     converter.check_sat()
// }
