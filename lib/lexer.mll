{
  (* open Core *)
  open Lexing
  open Parser

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = lexbuf.lex_curr_pos;
        pos_lnum = pos.pos_lnum + 1
      }
(* 

  module StringMap = Map.Make(String)
  let keyword_table = StringMap.of_alist_exn [
    "func", FUNC;
    "if", IF;
    "elseif", ELSEIF;
    "else", ELSE;
    "map", MAP;
    "Options", OPTIONS;
    "return", RETURN;
    "rpc_call", RPC_CALL;
    (* "true", true;
    "false", false; *)
  ]

    
  let find_token s =
    match StringMap.find_opt s keyword_table with
    | Some kw -> kw
    | None -> ID s *)

}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let digit = ['0'-'9']
let integer = digit+

rule comment = parse
  | "*/" { token lexbuf }
  | _ { comment lexbuf }


and token = parse 
  | white { token lexbuf }
  | newline { next_line lexbuf; token lexbuf }
  | "//" [^ '\n']* { token lexbuf } (* ignore comments *)
  | "/*" { comment lexbuf }
  | "->" { ARROW }
  | ',' { COMMA }
  | '=' { EQUALS }
  | integer as i { INT (int_of_string i)}
  | '<' {LEFT_ANGLE_BRACKET}
  | '>' {RIGHT_ANGLE_BRACKET}
  | '!' {BANG}
  | '{' {LEFT_CURLY_BRACE}
  | '}' {RIGHT_CURLY_BRACE}
  | '(' {LEFT_PAREN}
  | ')' {RIGHT_PAREN}
  | '[' {LEFT_SQUARE_BRACKET}
  | ']' {RIGHT_SQUARE_BRACKET}
  (* | '.' {DOT} *)
  | ':' {COLON}
  | ';' {SEMICOLON}
  | '"' {QUOTE}
  | "==" {EQUALS_EQUALS}
  | "!=" {NOT_EQUALS}
  | "&&" {AND}
  | "||" {OR}
  | "await" { AWAIT }
  | "true" { TRUE true }
  | "false" { FALSE false }
  | "func" { FUNC }
  | "if" { IF }
  | "else if" { ELSEIF }
  | "else" { ELSE }
  | "for" { FOR }
  | "in" { IN }
  | "map" { MAP }
  | "Options" { OPTIONS }
  | "return" { RETURN }
  | "rpc_async_call" { RPC_ASYNC_CALL}
  | "rpc_call" { RPC_CALL }
  | "ClientInterface" { CLIENT_INTERFACE }
  | id as s { ID s }
  | eof { EOF }
  (* | _ as c 
    { raise (SyntaxError ("Unexpected character: " ^ Char.escaped c)) } *)
