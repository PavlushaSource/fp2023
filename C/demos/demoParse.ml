open C_lib

let () =
  let s = Stdio.In_channel.input_all Stdlib.stdin in
  match Parser.parse s with
  | Result.Ok ast ->
      Format.printf "%a\n" Ast.pp_program ast
  | Error err ->
      Format.printf "Error %s" err
