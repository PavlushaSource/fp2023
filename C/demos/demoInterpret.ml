open C_lib

let () =
  let s = Stdio.In_channel.input_all Stdlib.stdin in
  match Parser.parse s with
  | Ok parse_result -> (
    match Interpret.InterpreterResult.exec_program parse_result with
    | Ok res ->
        Format.printf "%a" InterpretTypes.pp_value res
    | Error err ->
        Format.printf "%a" InterpretTypes.pp_error err )
  | Error err ->
      Format.printf "Parsing error: %s\n" err
