open Mylib.Ast
open Mylib
open Mylib.Simulator

(*Parametrize first*)
(* TOPOLOGIES = ["LINEAR"; "STAR"; "RING"; "FULL"] *)
let num_servers = 5
let num_clients = 3
let topology = "LINEAR"
let data = 
  let tbl = Hashtbl.create 91 in
  Hashtbl.add tbl (VString "birthday") (VInt 214);
  Hashtbl.add tbl (VString "epoch") (VInt 1980);
  tbl

let global_state = 
      { nodes = Array.init (num_servers + num_clients) (fun _ -> Env.create 91) 
      ; records = []
      ; history = DA.create () 
      ; free_clients = List.init num_clients (fun i -> num_servers + i) }

let process_role (_ : role_def) (_ : CFG.t) : function_info list = 
  []

let process_client_intf (_: client_def) (_ : CFG.t) : function_info list = 
  []

let process_program (prog : prog) : program =
  match prog with
  | Prog(single_role, clientIntf) ->
    let cfg = CFG.empty()
    and rpc_calls = Env.create 91
    and client_calls = Env.create 91 in
    let func_infos = process_role single_role cfg 
    and client_func_infos = process_client_intf clientIntf cfg in
    List.iter (fun func_info ->
      Env.add rpc_calls func_info.name func_info
      ) func_infos;
    List.iter (fun func_info -> 
      Env.add client_calls func_info.name func_info
      ) client_func_infos;
    { cfg = cfg
    ; rpc = rpc_calls
    ; client_ops = client_calls
    }

let sync_exec (global_state : state) (prog : program) : unit = 
  while not ((List.length global_state.records) = 0) do
    schedule_record global_state prog
  done

let parse_file (filename : string) : prog =
  let ic = open_in filename in
  let lexbuf = Lexing.from_channel ic in
  let ast = Parser.program Lexer.token lexbuf in
  close_in ic;
  ast

let init_topology (topology : string) (global_state : state) (prog : program) : unit =
  match topology with
  | "LINEAR" -> 
    let head_idx = 0
    and tail_idx = num_servers - 1 in
    schedule_client global_state prog "init_head" [
      VNode head_idx
    ; VNode (head_idx + 1)
    ; VNode tail_idx
    ; VMap data];
    sync_exec global_state prog;

    schedule_client global_state prog "init_tail" [
      VNode tail_idx
    ; VNode (tail_idx - 1)
    ; VNode head_idx
    ; VMap data];
    sync_exec global_state prog;

    for i = 1 to num_servers - 2 do
      schedule_client global_state prog "init_mid" [
        VNode i
      ; VNode (i - 1)
      ; VNode (i + 1)
      ; VNode head_idx
      ; VNode tail_idx
      ; VMap data];
      sync_exec global_state prog
    done

  | "STAR" -> raise (Failure "Not implemented STAR topology")
  | "RING" -> raise (Failure "Not implemented RING topology")
  | "FULL" -> raise (Failure "Not implemented FULL topology")
  | _ -> raise (Failure "Invalid topology")

let interp (f : string) : unit =
  (* Load the program into the simulator *)
  let _ = parse_file f in ();
  let prog = 
    let ast = parse_file f in 
    process_program ast in 
  init_topology topology global_state prog;
  print_endline "Program recognized as valid!";
;;
  
interp "/home/jennifer/jennLang/bin/CRAQ.jenn"
let () = print_endline "Program recognized as valid!"
let () = print_endline "Program ran successfully!"