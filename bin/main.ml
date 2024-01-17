open Mylib.Ast
open Mylib
open Mylib.Simulator

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

(** [interp] interprets [f] by parsing
    and evaluating it with the big-step model. *)
let interp (f : string) : prog =
  let a = parse_file f in a;;

interp "/Users/jenniferlam/jennLang/bin/client.jenn"
let () = print_endline "Program recognized as valid!"

let () = 
  let cfg = CFG.empty () in
  let ret_vert = CFG.fresh_vertex cfg in 
  CFG. set_label cfg ret_vert (Return (EBool true));
  let write_vert = CFG.fresh_vertex cfg in 
  CFG.set_label cfg write_vert (Instr(Write, ret_vert));
  let read_vert = CFG.fresh_vertex cfg in
  CFG.set_label cfg read_vert Read;
  let write_function_info = 
    { entry = write_vert
    ; name = "Write"
    ; formals = [("key", TString); ("value", TInt)]
    ; locals = [] } in
  let read_function_info = 
    { entry = read_vert
    ; name = "Read"
    ; formals = [("key", TString)]
    ; locals = [] } in
  let rpcCalls = Env.create 91 in
  Env.add rpcCalls "Write" write_function_info;
  Env.add rpcCalls "Read" read_function_info;
  let myProgram = 
    { cfg = cfg
    ; rpc = rpcCalls
    ; client_ops = [Env.find rpcCalls "Write"; Env.find rpcCalls "Read"] } in
  let globalState = 
      { nodes = Array.make 1 (Env.create 91)  (* Replace 10 with the desired number of nodes *)
      ; records = []
      ; history = DA.create ()  (* Assuming DA.create creates an empty dynamic array *)
      ; free_clients = [0] }  (* Replace with the actual list of free client IDs *) in
  let write = 0 in 
  schedule_client globalState myProgram write [VString "birthday"; VInt 214];
  schedule_record globalState myProgram;
  let read = 1 in 
  schedule_client globalState myProgram read [VString "birthday"];
  schedule_record globalState myProgram;
  DA.iter (fun op -> 
    print_string op.op_action
    ; begin match op.kind with 
      | Response -> print_string " Response"
      | Invocation -> print_string " Invocation"
  end
    ; List.iter (fun v -> print_string " "
    ; match v with
      | VInt i -> print_int i;
      | VBool b -> print_string (string_of_bool b)
      | VString s -> print_string s
      | _ -> failwith "Type error!") 
      op.payload
    ; print_endline "") 
      globalState.history;;

let () = print_endline "Program ran successfully!"



