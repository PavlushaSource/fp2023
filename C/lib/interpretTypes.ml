open Format
open Stdint
open Ast

let check_types_equality left right = left = right

type value =
  | I_Int of int32
  | I_Int32 of int32
  | I_Int16 of int16
  | I_Int8 of int8
  | I_Uint32 of uint32
  | I_Uint16 of uint16
  | I_Uint8 of uint8
  | I_Char of char
  | I_Bool of bool
  | I_Null

type error =
  | ArithmeticsError
  | UndefinedTypesConst
  | Unreachable
  | ReturnTypeMismatch of string
  | FuncHasNoBody of string
  | NotImplemented
  | ParsingFail
  | UnknownVariable of string

let pp_value fmt = function
  | I_Int num ->
      fprintf fmt "%s" @@ Int32.to_string num
  | I_Int32 num ->
      fprintf fmt "%s" @@ Int32.to_string num
  | I_Int16 num ->
      fprintf fmt "%s" @@ Int16.to_string num
  | I_Int8 num ->
      fprintf fmt "%s" @@ Int8.to_string num
  | I_Uint32 num ->
      fprintf fmt "%s" @@ Uint32.to_string num
  | I_Uint16 num ->
      fprintf fmt "%s" @@ Uint16.to_string num
  | I_Uint8 num ->
      fprintf fmt "%s" @@ Uint8.to_string num
  | I_Char ch ->
      fprintf fmt "%c" ch
  | I_Bool bool ->
      fprintf fmt "%b" bool
  | _ -> failwith "Hoh"

let pp_error fmt = function
  | Unreachable ->
      fprintf fmt "Unreachable"
  | ArithmeticsError ->
      fprintf fmt "Arith Error"
  | UndefinedTypesConst ->
      fprintf fmt "Const Error"
  | ReturnTypeMismatch str ->
      fprintf fmt "Return type uncorrect - %s" str
  | FuncHasNoBody str ->
      fprintf fmt "Function has no body - %s" str
  | NotImplemented ->
      fprintf fmt "Not implemented now!"
  | ParsingFail -> 
      fprintf fmt "Parsing fail!"
  | UnknownVariable str ->
      fprintf fmt "Unknown variable with name - %s" str

type h_value =
  | H_explicit_var of string * value  (** format for variables which have name*)
  | H_implicit_var of int * value  (** format for array elements*)


