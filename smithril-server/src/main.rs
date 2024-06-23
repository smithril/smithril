use ipc_channel::ipc::{IpcReceiver, IpcSender};
use smithril_lib::{
    converters::{self, Converter},
    generalized::{GeneralConverter, GeneralSort, GeneralTerm, SolverQuery, SolverResult},
};
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();

    let one_shot_server_name = &args[1];
    let tx = IpcSender::connect(one_shot_server_name.to_string()).unwrap();

    let (server_tx, server_rx) = ipc_channel::ipc::channel::<String>().unwrap();
    let (client_tx, client_rx) = ipc_channel::ipc::channel::<String>().unwrap();

    tx.send((server_tx, client_rx)).unwrap();

    let receiver: IpcReceiver<String> = server_rx;
    let sender: IpcSender<String> = client_tx;

    // Receive the converter setup message
    let converter_line = receiver.recv().expect("Failed to receive converter");
    let converter: Converter =
        serde_json::from_str(&converter_line).expect("Failed to parse converter");

    // Send confirmation of converter setup
    match converter {
        Converter::Bitwuzla => {
            sender
                .send("Bitwuzla converter has set up".to_string())
                .unwrap();
        }
        Converter::Z3 => {
            sender.send("Z3 converter has set up".to_string()).unwrap();
        }
    }

    // Process each subsequent message
    while let Ok(input_line) = receiver.recv() {
        let input: SolverQuery = serde_json::from_str(&input_line).unwrap();
        let output = match converter {
            Converter::Bitwuzla => {
                let bc = converters::mk_bitwulza();
                solve_problem(&bc, input)
            }
            Converter::Z3 => {
                let bc = converters::mk_z3();
                solve_problem(&bc, input)
            }
        };
        let output_json = serde_json::to_string(&output).unwrap();
        sender.send(output_json).unwrap();
    }
}

fn solve_problem<'a, C, S, T>(converter: &'a C, input: SolverQuery) -> SolverResult
where
    C: GeneralConverter<'a, S, T>,
    S: GeneralSort,
    S: 'a,
    T: GeneralTerm,
    T: 'a,
{
    converter.assert(&converter.convert_term(&input.query));
    converter.check_sat()
}
