(** Copyright 2021-2023, PavlushaSource, Kakadu *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Ast
open Stdint
open Format
open InterpretTypes
module StringMap = Map.Make (String)

module type MONAD_ERROR = sig
  include Base.Monad.S2

  val fail : 'e -> ('a, 'e) t

  val ( let* ) : ('a, 'e) t -> ('a -> ('b, 'e) t) -> ('b, 'e) t
end

type variable = {var_type: types; var_value: value option; var_addr: int}

type context =
  { return_type: types
  ; func_name: name
  ; var_map: variable StringMap.t
  ; heap: Bytes.t
  ; free_byte: int
  ; functions: program
  ; occupied_list: (types * int * int) list
  ; last_value: value
  ; return_flag: bool }

module HEAP (M : MONAD_ERROR) = struct
  open M
  open InterpretTypes
  open Ast

  let get_type_size = function ID_int -> 4 | _ -> 1
end

module Interpret (M : MONAD_ERROR) = struct
  open M

  open HEAP (M)

  (* let rec exec_arith bin_op expr1 expr2 =
       let* val1 = arithmetics expr1 in
       let* val2 = arithmetics expr2 in
       match (bin_op, val1, val2) with
       | Add, I_Int num1, I_Int num2 ->
           return @@ I_Int (num1 + num2)
       | Sub, I_Int num1, I_Int num2 ->
           return @@ I_Int (num1 - num2)
       | _ ->
           fail ArithmeticsError

     and get_const value =
       match value with
       | V_int num ->
           return @@ I_Int num
       | V_char ch ->
           return @@ I_Char ch
       | _ ->
           fail UndefinedTypesConst

     and arithmetics expr =
       match expr with
       | Bin_expr (bin_op, expr1, expr2) ->
           exec_arith bin_op expr1 expr2
       | Const value ->
           get_const value
       | _ ->
           fail Unreachable

     and interpret_st_block sts_block =
       match sts_block with
       | Expression expr :: others ->
           arithmetics expr
       | _ ->
           fail Unreachable

     and exec_expression expr =

     and exec_statements st =
       match st with
       | Expression expr :: others -> (match exec_expression expr with
         | Ok _ -> exec_statements others
         | Error err -> fail err
         )
       | _ -> fail "Not implemented"



     and func_interpreter func =
       match func with
       | Func_def (Func_decl (return_type, name, args), body) -> (
           match body with
           | Compound sts -> (
           exec_statements sts
           >>= function
           | Some ret_val ->
               return ret_val
           | None ->
               if check_types_equality ID_void return_type then return @@ I_Int 0
               else
                 fail
                 @@ ReturnTypeMismatch
                      (name ^ "expected a return value, but nothing was returned"))
           | _ -> fail @@ FuncHasNoBody (name ^ "has no body!")
           )
       | _ ->
           fail Unreachable
  *)

  (* let rec exec_statement expr ctx =
     match expr with
     | Expression expr ->
         let* ctx = exec_expression expr ctx in
         return ctx
     | _ ->
         fail NotImplemented *)

  (* let define_return_type expected_type return_val =
     match (expected_type, return_val) with ID_int, I_Int -> true | _ -> false *)

  let take_var name var_map = 
    match StringMap.find_opt name var_map with
    | Some var -> return var
    | None -> fail @@ UnknownVariable name

  let const_for_value (ctx : context) = function
    | V_int x ->
        return (I_Int32 (Int32.of_int x), ctx)
    | _ ->
        fail UndefinedTypesConst

  let rec exec_bin_op expr1 expr2 bin_op ctx =
    let* val1, ctx = exec_expression expr1 ctx in
    let* val2, ctx = exec_expression expr2 ctx in
    match (bin_op, val1, val2) with
    | Add, I_Int32 x, I_Int32 y ->
        return (I_Int32 (Stdint.Int32.( + ) x y), ctx)
    | _ ->
        fail NotImplemented

  and exec_expression expr ctx : (value * context, error) t =
    match expr with
    | Bin_expr (bin_op, expr1, expr2) ->
        exec_bin_op expr1 expr2 bin_op ctx
    | Const x ->
        const_for_value ctx x
    | Var_name name -> (
      let* variable = take_var name ctx.var_map in
      match variable with
      | { var_type = _; var_value = Some v; var_addr = -1 } -> return (v, ctx)
      | _ -> fail NotImplemented)
    | _ ->
        fail NotImplemented

  and exec_declaration var_t var_name sts ctx =
    match sts with
    | Some (Expression x) ->
        let* return_value, ctx = exec_expression x ctx in
        return
          { ctx with
            var_map=
              StringMap.add var_name
                { var_type= var_t
                ; var_value= Option.some return_value
                ; var_addr= -1 } 
                ctx.var_map}
    | _ ->
        fail NotImplemented

  let exec_statement (st : statement) (ctx : context) : (context, error) t =
    match st with
    | Var_decl (var_type, name, sts) ->
        exec_declaration var_type name sts ctx
    | Return expr ->
        let* return_value, ctx = exec_expression expr ctx in
        return {ctx with last_value= return_value; return_flag= true}
    | _ ->
        fail NotImplemented

  let get_type_func = function
    | Func_def (Func_decl (return_type, _, _), _) ->
        return_type
    | _ ->
        failwith "It is impossible to determine the type of function"

  let exec_function func (ctx : (context, error) t) =
    match func with
    | Func_def (Func_decl (return_type, func_name, args), body) -> (
      match body with
      | Compound sts ->
          List.fold_left
            (fun ctx st ->
              let* ctx = ctx in
              if ctx.return_flag = true then return ctx
              else
                let* ctx = exec_statement st ctx in
                return ctx )
            ctx sts
      | _ ->
          fail Unreachable )
    | _ ->
        fail Unreachable

  let exec_program (program : program_function list) =
    let rec func_name = function
      | Func_def (fDecl, _) ->
          func_name fDecl
      | Func_decl (_, func_name, _) ->
          func_name
    in
    match
      Stdlib.List.find_opt
        (fun func -> String.equal (func_name func) "main")
        program
    with
    | Some func ->
        exec_function func
          (return
             { func_name= "main"
             ; return_type= get_type_func func
             ; var_map= StringMap.empty
             ; heap= Bytes.create 1024
             ; free_byte= 0
             ; occupied_list= []
             ; functions= program
             ; last_value= I_Null
             ; return_flag= false } )
    | None ->
        fail Unreachable
end

module MONAD_RESULT = struct
  include Base.Result

  let ( let* ) m f = m >>= fun x -> f x
end

module InterpreterResult = Interpret (MONAD_RESULT)

let parse_and_run str =
  match Parser.parse str with
  | Ok parse_result -> (
    match InterpreterResult.exec_program parse_result with
    | Ok ctx ->
        printf "%a" InterpretTypes.pp_value ctx.last_value
    | Error err ->
        printf "%a" InterpretTypes.pp_error err )
  | Error _ ->
      print_endline "Parsing Error!"

let%expect_test _ =
  let _ =
    parse_and_run
      {|
      int main() {
        int dima = 5 + 6;
        int grisha = 20 + 32;
        return dima + grisha;
      }
      |}
  in
  [%expect {| 10 |}]
