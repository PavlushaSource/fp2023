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

module Interpret (M : MONAD_ERROR) = struct
  open M

  let shift_left x y = Base.Int32.shift_left x (Int32.to_int y)

  let shift_right x y = Base.Int32.shift_right x (Int32.to_int y)

  let take_var name var_map =
    match StringMap.find_opt name var_map with
    | Some var ->
        return var
    | None ->
        fail @@ UnknownVariable name

  let const_for_value ctx = function
    | V_int x ->
        return (ID_int32, I_Int32 (Int32.of_int x), ctx)
    | V_char x ->
        return (ID_char, I_Char x, ctx)
    | V_float x ->
        return (ID_float, I_Float x, ctx)
    | _ ->
        fail UndefinedTypesConst

  let rec cast_val old_val new_type =
    match (old_val, new_type) with
    | I_Float x, ID_float ->
        return (I_Float x)
    | I_Float x, ID_uint32 ->
        return (I_Uint32 (Uint32.of_float x))
    | I_Float x, ID_int32 ->
        return (I_Int32 (Int32.of_float x))
    | I_Float x, ID_uint16 ->
        return (I_Uint16 (Uint16.of_float x))
    | I_Float x, ID_int16 ->
        return (I_Int16 (Int16.of_float x))
    | I_Float x, ID_uint8 ->
        return (I_Uint8 (Uint8.of_float x))
    | I_Float x, ID_int8 ->
        return (I_Int8 (Int8.of_float x))
    | I_Float x, ID_char ->
        let new_x = Float.to_int x in
        if new_x <= 255 && new_x >= 0 then
          return (I_Char (Base.Char.of_int_exn new_x))
        else
          fail
          @@ ReturnTypeMismatch
               "Trying to convert int number not in char boundaries in char"
    | I_Float x, ID_bool ->
        return (I_Bool (if x = Int.to_float 0 then false else true))
    | I_Uint32 x, ID_float ->
        return (I_Float (Uint32.to_float x))
    | I_Int32 x, ID_float ->
        return (I_Float (Int32.to_float x))
    | I_Uint16 x, ID_float ->
        return (I_Float (Uint16.to_float x))
    | I_Int16 x, ID_float ->
        return (I_Float (Int16.to_float x))
    | I_Uint8 x, ID_float ->
        return (I_Float (Uint8.to_float x))
    | I_Int8 x, ID_float ->
        return (I_Float (Int8.to_float x))
    | I_Char x, ID_float ->
        return (I_Float (Int.to_float (Char.code x)))
    | I_Bool x, ID_float ->
        return (I_Float (Bool.to_float x))
    | I_Uint32 x, ID_uint32 ->
        return (I_Uint32 x)
    | I_Uint32 x, ID_int32 ->
        return (I_Int32 (Int32.of_uint32 x))
    | I_Uint32 x, ID_uint16 ->
        return (I_Uint16 (Uint16.of_uint32 x))
    | I_Uint32 x, ID_int16 ->
        return (I_Int16 (Int16.of_uint32 x))
    | I_Uint32 x, ID_uint8 ->
        return (I_Uint8 (Uint8.of_uint32 x))
    | I_Uint32 x, ID_int8 ->
        return (I_Int8 (Int8.of_uint32 x))
    | I_Uint32 x, ID_char ->
        let new_x = Uint32.to_int x in
        if new_x <= 255 && new_x >= 0 then
          return (I_Char (Base.Char.of_int_exn new_x))
        else
          fail
          @@ ReturnTypeMismatch
               "Trying to convert int number not in char boundaries in char"
    | I_Uint32 x, ID_bool ->
        return (I_Bool (if Uint32.to_int x = 0 then false else true))
    | I_Int32 x, _ ->
        cast_val (I_Uint32 (Uint32.of_int32 x)) new_type
    | I_Uint16 x, _ ->
        cast_val (I_Uint32 (Uint32.of_uint16 x)) new_type
    | I_Int16 x, _ ->
        cast_val (I_Uint32 (Uint32.of_int16 x)) new_type
    | I_Uint8 x, _ ->
        cast_val (I_Uint32 (Uint32.of_uint8 x)) new_type
    | I_Int8 x, _ ->
        cast_val (I_Uint32 (Uint32.of_int8 x)) new_type
    | I_Char x, _ ->
        cast_val (I_Uint32 (Uint32.of_int (Char.code x))) new_type
    | I_Bool x, _ ->
        cast_val (I_Uint32 (Uint32.of_int (Bool.to_int x))) new_type
    | _ ->
        fail @@ ReturnTypeMismatch "Not supported type to cast"

  let find_necessary_func name func_list =
    let rec func_name = function
      | Func_def (fDecl, _) ->
          func_name fDecl
      | Func_decl (_, func_name, _) ->
          func_name
    in
    Stdlib.List.find_opt
      (fun func -> String.equal (func_name func) name)
      func_list

  let relevant_type t1 t2 =
    match (t1, t2) with
    | ID_float, _ | _, ID_float ->
        return ID_float
    | ID_uint32, _ | _, ID_uint32 ->
        return ID_uint32
    | ID_int32, _ | _, ID_int32 ->
        return ID_int32
    | ID_int, _ | _, ID_int ->
        return ID_int32
    | ID_uint16, _ | _, ID_uint16 ->
        return ID_uint16
    | ID_int16, _ | _, ID_int16 ->
        return ID_int16
    | ID_uint8, _ | _, ID_uint8 ->
        return ID_uint8
    | ID_int8, _ | _, ID_int8 ->
        return ID_int8
    | ID_char, _ | _, ID_char ->
        return ID_char
    | ID_bool, _ | _, ID_bool ->
        return ID_bool
    | _ ->
        fail
        @@ ReturnTypeMismatch
             "It is impossible to compare this type with anything"

  let exec_int_arith_op value1 value2 op =
    let* x = cast_val value1 ID_int32 in
    let* y = cast_val value2 ID_int32 in
    match (x, y) with
    | I_Int32 x, I_Int32 y ->
        return (I_Int32 (op x y))
    | _ ->
        fail Unreachable

  let exec_float_arith_op value1 value2 op =
    let* x = cast_val value1 ID_float in
    let* y = cast_val value2 ID_float in
    match (x, y) with
    | I_Float x, I_Float y ->
        return (I_Float (op x y))
    | _ ->
        fail Unreachable

  let exec_int_logical_op value1 value2 op =
    match (value1, value2) with
    | I_Int32 x, I_Int32 y ->
        return (I_Bool (op x y))
    | _ ->
        fail Unreachable

  let exec_float_logical_op value1 value2 op =
    match (value1, value2) with
    | I_Float x, I_Float y ->
        return (I_Bool (op x y))
    | _ ->
        fail Unreachable

  let get_type_func = function
    | Func_def (Func_decl (return_type, _, _), _) ->
        return_type
    | _ ->
        failwith "It is impossible to determine the type of function"

  let check_zero x =
    match x with
    | I_Float x when not (x = Int.to_float 0) ->
        return false
    | _ -> (
        let* x = cast_val x ID_int32 in
        match x with I_Int32 x when x = 0l -> return true | _ -> return false )

  let rec exec_bin_op expr1 expr2 bin_op ctx =
    let* val1_type, val1, ctx = exec_expression expr1 ctx in
    match (bin_op, val1) with
    | And, I_Bool false ->
        return (ID_bool, I_Bool false, ctx)
    | Or, I_Bool true ->
        return (ID_bool, I_Bool true, ctx)
    | _ ->
        let* val2_type, val2, ctx = exec_expression expr2 ctx in
        let* res =
          match (bin_op, val1, val2) with
          | Add, x, y -> (
            match (val1_type, val2_type) with
            | ID_float, _ | _, ID_float ->
                exec_float_arith_op val1 val2 Base.Float.( + )
            | _ ->
                exec_int_arith_op x y Base.Int32.( + ) )
          | Sub, x, y -> (
            match (val1_type, val2_type) with
            | ID_float, _ | _, ID_float ->
                exec_float_arith_op val1 val2 Base.Float.( - )
            | _ ->
                exec_int_arith_op x y Base.Int32.( - ) )
          | Mul, x, y -> (
            match (val1_type, val2_type) with
            | ID_float, _ | _, ID_float ->
                exec_float_arith_op val1 val2 Base.Float.( * )
            | _ ->
                exec_int_arith_op x y Base.Int32.( * ) )
          | Div, x, y ->
              let* zero_exist = check_zero y in
              if not zero_exist then
                match (val1_type, val2_type) with
                | ID_float, _ | _, ID_float ->
                    exec_float_arith_op val1 val2 Base.Float.( / )
                | _ ->
                    exec_int_arith_op x y Base.Int32.( / )
              else fail DivisionByZero
          | Mod, x, y ->
              let* zero_exist = check_zero y in
              if not zero_exist then
                match (val1_type, val2_type) with
                | ID_float, _ | _, ID_float ->
                    exec_float_arith_op val1 val2 Base.Float.( % )
                | _ ->
                    exec_int_arith_op x y Base.Int32.( % )
              else fail DivisionByZero
          | Lshift, x, y -> (
            match (val1_type, val2_type) with
            | ID_float, _ | _, ID_float ->
                fail ArithmeticsError
            | _ ->
                exec_int_arith_op x y shift_left )
          | Rshift, x, y -> (
            match (val1_type, val2_type) with
            | ID_float, _ | _, ID_float ->
                fail ArithmeticsError
            | _ ->
                exec_int_arith_op x y shift_right )
          | Less, x, y -> (
            match (val1_type, val2_type) with
            | ID_float, _ | _, ID_float ->
                exec_float_logical_op x y Base.Float.( < )
            | _ ->
                exec_int_logical_op x y Base.Int32.( < ) )
          | LessOrEqual, x, y -> (
            match (val1_type, val2_type) with
            | ID_float, _ | _, ID_float ->
                exec_float_logical_op x y Base.Float.( <= )
            | _ ->
                exec_int_logical_op x y Base.Int32.( <= ) )
          | Grow, x, y -> (
            match (val1_type, val2_type) with
            | ID_float, _ | _, ID_float ->
                exec_float_logical_op x y Base.Float.( > )
            | _ ->
                exec_int_logical_op x y Base.Int32.( > ) )
          | GrowOrEqual, x, y -> (
            match (val1_type, val2_type) with
            | ID_float, _ | _, ID_float ->
                exec_float_logical_op x y Base.Float.( >= )
            | _ ->
                exec_int_logical_op x y Base.Int32.( >= ) )
          | Equal, x, y -> (
            match (val1_type, val2_type) with
            | ID_float, _ | _, ID_float ->
                exec_float_logical_op x y Base.Float.( = )
            | _ ->
                exec_int_logical_op x y Base.Int32.( = ) )
          | NotEqual, x, y -> (
            match (val1_type, val2_type) with
            | ID_float, _ | _, ID_float ->
                exec_float_logical_op x y Base.Float.( <> )
            | _ ->
                exec_int_logical_op x y Base.Int32.( <> ) )
          | Or, _, y -> (
              let* y = cast_val y ID_int32 in
              match y with
              | I_Int32 y when y = 0l ->
                  return (I_Bool true)
              | _ ->
                  return (I_Bool false) )
          | And, _, y -> (
              let* y = cast_val y ID_int32 in
              match y with
              | I_Int32 y when y = 1l ->
                  return (I_Bool true)
              | _ ->
                  return (I_Bool false) )
        in
        let* necessary_type = relevant_type val1_type val2_type in
        let* return_val = cast_val res necessary_type in
        return (necessary_type, return_val, ctx)

  (* | Sub, x, y ->
     let* res = exec_bin_op' x y Base.Int32.( - ) in
     let* grow_type = change_grow_type val1_type val2_type in
     let* return_val = cast_val res grow_type in
     return (grow_type, return_val, ctx) *)

  and exec_expression expr ctx : (types * value * context, error) t =
    match expr with
    | Bin_expr (bin_op, expr1, expr2) ->
        exec_bin_op expr1 expr2 bin_op ctx
    | Const x ->
        const_for_value ctx x
    | Func_call (func_name, func_args) -> (
        let rec get_name_args arg_list =
          match arg_list with
          | hd :: tail -> (
            match hd with Arg (_, n) -> n :: get_name_args tail )
          | [] ->
              []
        in
        match find_necessary_func func_name ctx.functions with
        | Some func_finded -> (
          match func_finded with
          | Func_def (Func_decl (return_type, func_name, args), _) ->
              let* ctx' =
                List.fold_left2
                  (fun ctx' argument expr ->
                    let* ctx' = ctx' in
                    let* ctx' =
                      match argument with
                      | Arg (t, n) ->
                          exec_declaration t n (Some (Expression expr)) ctx'
                    in
                    return ctx' )
                  (return {ctx with func_name; return_type})
                  args func_args
              in
              let arg_names = get_name_args args in
              let ctx' =
                { ctx' with
                  var_map=
                    StringMap.filter
                      (fun name _ ->
                        List.exists (fun arg_name -> arg_name = name) arg_names
                        )
                      ctx'.var_map }
              in
              let* ret_val, ctx' = exec_function func_finded (return ctx') in
              return (return_type, ret_val, ctx')
          | _ ->
              fail Unreachable )
        | None ->
            fail
              (UnknownVariable
                 ("Call undefined function with name - " ^ func_name) ) )
    | Var_name name -> (
        let* variable = take_var name ctx.var_map in
        match variable with
        | {var_type= t; var_value= Some v; var_addr= -1} ->
            return (t, v, ctx)
        | _ ->
            fail NotImplemented )
    | _ ->
        fail NotImplemented

  and exec_declaration var_t var_name sts (ctx : context) =
    match sts with
    | Some (Expression x) ->
        let* return_type, return_value, ctx = exec_expression x ctx in
        let* return_value = cast_val return_value var_t in
        return
          { ctx with
            var_map=
              StringMap.add var_name
                { var_type= var_t
                ; var_value= Option.some return_value
                ; var_addr= -1 }
                ctx.var_map }
    | _ ->
        fail NotImplemented

  and exec_statement (st : statement) (ctx : context) : (context, error) t =
    match st with
    | Var_decl (var_type, name, sts) ->
        exec_declaration var_type name sts ctx
    | Return expr ->
        let* return_type, return_value, ctx = exec_expression expr ctx in
        return {ctx with last_value= return_value; return_flag= true}
    | _ ->
        fail NotImplemented

  and exec_function func ctx =
    match func with
    | Func_def (Func_decl (return_type, func_name, args), body) -> (
      match body with
      | Compound sts ->
          let* ctx =
            List.fold_left
              (fun ctx st ->
                let* ctx = ctx in
                if ctx.return_flag = true then return ctx
                else
                  let* ctx = exec_statement st ctx in
                  return ctx )
              ctx sts
          in
          return (ctx.last_value, ctx)
      | _ ->
          fail Unreachable )
    | _ ->
        fail Unreachable

  let exec_program (program : program_function list) =
    match find_necessary_func "main" program with
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
    | Ok (value, ctx) ->
        printf "%a" InterpretTypes.pp_value value
    | Error err ->
        printf "%a" InterpretTypes.pp_error err )
  | Error _ ->
      print_endline "Parsing Error!"

let%expect_test _ =
  let _ =
    parse_and_run
      {|

      int sum(int x, int y) {
        return x + y;
      }
      
      int main() {
        int x = 30;
        int nastya = 20;
        return sum (x + 10, nastya * 20 << 1);
      }
      |}
  in
  [%expect {| 840 |}]

let%expect_test _ =
  let _ =
    parse_and_run
      {|
      int main() {
        uint32_t x = 30;
        return x;
      }
      |}
  in
  [%expect {| 30 |}]
