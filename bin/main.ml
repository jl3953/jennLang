open Mylib.Ast
open Mylib

(* let parse (s : string) : prog =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.program Lexer.token lexbuf in
  ast *)

let parse_file (filename : string) : prog =
  let ic = open_in filename in
  let lexbuf = Lexing.from_channel ic in
  let ast = Parser.program Lexer.token lexbuf in
  close_in ic;
  ast

let eval (a, agg) : class list =
  []

(** [interp] interprets [f] by parsing
    and evaluating it with the big-step model. *)
let interp (f : string) : prog =
  let a = parse_file f in
  eval a [];;

interp "/Users/jenniferlam/jennLang/bin/client.jenn"
let () = print_endline "Program recognized as valid!"