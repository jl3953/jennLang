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
let interp (f : string) : unit =
  let ast = parse_file f in
  match ast with 
  | Prog(roles, clientIntf) -> print_endline "Prog";
    (* process roles*) 
    List.iter (fun role -> 
      match role with
      (* | RoleDef(roleName, params, initVars, func_defs) -> print_endline "" *)
      | RoleDef(roleName, _, _, _) -> print_endline ("RoleDef: " ^ roleName)
      (* | _ -> failwith "Type error!" *)
    ) roles;
    (* process clientIntf *)
    match clientIntf with
    | ClientDef(func_defs) -> print_endline "ClientDef ";
      List.iter (fun func_def -> 
        match func_def with
        (* | FuncDef(funcCall, retType, body) -> 
          match funcCall with FuncCall(funcName, args) -> 
            print_endline funcName)
          func_defs *)
        | FuncDef(funcCall, retType, _) -> 
          (* process func call*)
          begin match funcCall with 
          | FuncCall(funcName, params) -> 
            print_endline ("FuncCall: " ^ funcName);
            List.iter (fun param -> 
              begin match param with Param(rhs)->
                begin match rhs with
                | VarRHS(formal) -> print_endline formal
                | _ -> failwith "Type error!"
                end
              end
            ) params
          end;
          (* process retType*)
          begin match retType with
          | _ -> print_endline "jenndbg assume retType int"
          end;
      ) func_defs
        (* | _ -> failwith "Type error!" *)
    (* | _ -> failwith "Type error!" *)
  (* | _ -> failwith "Type error!" *)
;;

interp "/Users/jenniferlam/jennLang/bin/simple_spec.jenn"
let () = print_endline "Program recognized as valid!"

let () = 
  let cfg = CFG.empty () in
  let ret_vert = CFG.fresh_vertex cfg in 
  CFG. set_label cfg ret_vert (Return (EBool true));
  let write_vert = CFG.fresh_vertex cfg in 
  CFG.set_label cfg write_vert (Instr(Assign (LAccess (LVar "db", EVar "key"), EVar "value"), ret_vert));
  let read_vert = CFG.fresh_vertex cfg in
  CFG.set_label cfg read_vert (Return(EFind ("db", EVar "key")));
  let init_vert = CFG.fresh_vertex cfg in 
  CFG.set_label cfg init_vert (Instr(Assign (LVar "db", EMap), ret_vert));
  let write_function_info = 
    { entry = write_vert
    ; name = "Write"
    ; formals = [("key", TString); ("value", TInt)]
    ; locals = [] } 
  and read_function_info = 
    { entry = read_vert
    ; name = "Read"
    ; formals = [("key", TString)]
    ; locals = [] } 
  and init_func_info = 
    { entry = init_vert
    ; name = "Init"
    ; formals = []
    ; locals = []
    } in
  let rpcCalls = Env.create 91 in
  Env.add rpcCalls "Write" write_function_info;
  Env.add rpcCalls "Read" read_function_info;
  Env.add rpcCalls "Init" init_func_info;
  let myProgram = 
    { cfg = cfg
    ; rpc = rpcCalls
    ; client_ops = [Env.find rpcCalls "Write"; Env.find rpcCalls "Read"; Env.find rpcCalls "Init"] } in
  let globalState = 
      { nodes = Array.make 1 (Env.create 91)  (* Replace 10 with the desired number of nodes *)
      ; records = []
      ; history = DA.create ()  (* Assuming DA.create creates an empty dynamic array *)
      ; free_clients = [0] }  (* Replace with the actual list of free client IDs *) in
  let write = 0 
  and read = 1
  and init = 2 in
  schedule_client globalState myProgram init [];
  schedule_record globalState myProgram;
  schedule_client globalState myProgram write [VString "birthday"; VInt 214];
  schedule_record globalState myProgram;
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



