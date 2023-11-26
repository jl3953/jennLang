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
  ast;;

parse_file "/Users/jenniferlam/jennLang/bin/hello.jenn" 
let () = print_endline "Program recognized as valid!"