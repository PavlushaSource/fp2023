open Format
open Stdint

let check_types_equality left right = left = right

type value =
  | I_Int32 of int32
  | I_Int16 of int16
  | I_Int8 of int8
  | I_Char of char
  | I_Bool of bool
  | I_Null

type error =
  | NoFunctionDeclaration of string
  | ArithmeticsError
  | UndefinedTypesConst
  | Unreachable
  | ReturnTypeMismatch of string
  | InvalidFunctionCall of string
  | FuncHasNoBody of string
  | NotImplemented
  | ParsingFail
  | UnknownVariable of string
  | DivisionByZero
  | StackOverflow
  | CheckValue of value

let pp_value fmt = function
  | I_Int32 num ->
      fprintf fmt "%s" @@ Int32.to_string num
  | I_Int16 num ->
      fprintf fmt "%s" @@ Int16.to_string num
  | I_Int8 num ->
      fprintf fmt "%s" @@ Int8.to_string num
  | I_Char ch ->
      fprintf fmt "%c" ch
  | I_Bool bool ->
      fprintf fmt "%b" bool
  | I_Null ->
      fprintf fmt "Null value"

let pp_error fmt = function
  | CheckValue value ->
      pp_value fmt value
  | InvalidFunctionCall str ->
      fprintf fmt "Invalid function call - %s" str
  | StackOverflow ->
      fprintf fmt "Stack overflow!"
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
  | DivisionByZero ->
      fprintf fmt "Division by zero!"
  | NoFunctionDeclaration str ->
      fprintf fmt "Declaration function with name - %s miss" str
