open Mylib.Ast
open Mylib
open Mylib.Simulator

(*Parametrize first*)
(* TOPOLOGIES = ["LINEAR"; "STAR"; "RING"; "FULL"] *)

let num_servers = 5
let num_clients = 3
let chain_len = 3
let head_idx = 0
let tail_idx = chain_len - 1
let topology = "LINEAR"
let data () : (value, value) Hashtbl.t = 
  let tbl = Hashtbl.create 91 in
  Hashtbl.add tbl (VString "birthday") (VInt 214);
  Hashtbl.add tbl (VString "epoch") (VInt 1980);
  Hashtbl.add tbl (VString "name") (VString "Jennifer");
  tbl

let mod_op (i : int) (m : int): int = 
  if i < 0 then
    i + m
  else
    i mod m

let jenns_birthday_counter = ref 214
let increment_birthday () : int = 
  jenns_birthday_counter := !jenns_birthday_counter + 1;
  !jenns_birthday_counter

let global_state = 
  { nodes = Array.init (num_servers + num_clients) (fun _ -> Env.create 91) 
  ; records = []
  ; history = DA.create () 
  ; free_clients = List.init num_clients (fun i -> num_servers + i) }

let convert_lhs(lhs : Ast.lhs) : Simulator.lhs =
  match lhs with 
  | VarLHS (var_name) -> LVar(var_name)
  | MapAccessLHS (map_name, key) -> LAccess(LVar(map_name), EVar(key))
  | FieldAccessLHS (_, _) -> failwith "TODO what on earth is FieldAccessLHS again?"
  | TupleLHS lefts -> LTuple lefts

let rec convert_rhs (rhs : rhs) : Simulator.expr =
  match rhs with
  | VarRHS var -> EVar(var)
  | MapAccessRHS(map, key) -> EFind(map, EVar(key))
  | FuncCallRHS func_call ->
    begin match func_call with
      | FuncCall(func_name, _) -> failwith ("Didn't implement FuncCallRHS yet func: " ^ func_name)
    end
  | LiteralRHS literal -> 
    begin match literal with
      | Options _ -> failwith "Didn't implement Options yet"
      | String s -> EString(s)
      | Int i -> EInt(i)
    end
  | FieldAccessRHS _ -> failwith "Didn't implement FieldAccessRHS yet"
  | BoolRHS boolean ->
    begin match boolean with
      | Bool b -> EBool(b)
      | Not rhs -> ENot (convert_rhs rhs)
      | Or (rhs1, rhs2) -> EOr(convert_rhs rhs1, convert_rhs rhs2)
      | And (b1, b2) -> EAnd(convert_rhs b1, convert_rhs b2)
      | EqualsEquals (rhs1, rhs2) -> EEqualsEquals(convert_rhs rhs1, convert_rhs rhs2)
      | NotEquals (b1, b2) -> ENot(EEqualsEquals(convert_rhs b1, convert_rhs b2))
    end 
  | CollectionRHS collection_lit ->
    begin match collection_lit with
      | MapLit kvpairs -> EMap (List.map (fun (k, v) -> (k, convert_rhs v)) kvpairs);
      | ListLit items -> EList (List.map (fun (v) -> convert_rhs v) items)
    end
  | RpcCallRHS _ -> failwith "Didn't implement RpcCallRHS yet"

let rec generate_cfg_from_stmts (stmts : statement list) (cfg : CFG.t) (last_vert : CFG.vertex) : CFG.vertex =
  match stmts with
  | [] -> last_vert
  | stmt :: rest ->
    let next_vert = generate_cfg_from_stmts rest cfg last_vert in
    begin match stmt with 
      | CondList (cond_stmts) ->
        begin
          let next = generate_cfg_from_stmts rest cfg last_vert in
          generate_cfg_from_cond_stmts cond_stmts cfg next
        end
      | Assignment (lhs, exp) -> 
        let lhs_vert = CFG.create_vertex cfg (Instr(Assign(convert_lhs lhs, EVar "ret"), next_vert)) in
        generate_cfg_from_stmts [Expr exp] cfg lhs_vert
      | Expr expr -> 
        begin match expr with
          | RpcCallRHS rpc_call -> 
            begin match rpc_call with
              | RpcCall(node, func_call) -> 
                begin match func_call with
                  | FuncCall(func_name, actuals) -> 
                    let actuals = List.map (fun actual -> 
                        match actual with Param(rhs) -> convert_rhs rhs
                      ) actuals in
                    let assign_vert = CFG.create_vertex cfg (Instr(Assign(LVar "ret", EVar "dontcare"), next_vert)) in
                    let await_vertex = CFG.create_vertex cfg (Await(LVar("dontcare"), EVar "async_future", assign_vert)) in
                    let async_vertex = CFG.create_vertex cfg (Instr(Async(LVar "async_future", EVar node, func_name, actuals), await_vertex)) in
                    CFG.create_vertex cfg (Pause async_vertex)
                end
              | RpcAsyncCall (node, func_call) -> 
                begin match func_call with
                  | FuncCall(func_name, actuals) ->
                    let actuals = List.map (fun actual -> 
                        match actual with Param(rhs) -> convert_rhs rhs
                      ) actuals in
                    let async_vertex = CFG.create_vertex cfg (Instr(Async(LVar "ret", EVar node, func_name, actuals), next_vert)) in
                    CFG.create_vertex cfg (Pause async_vertex)
                end
            end
          | rhs -> CFG.create_vertex cfg (Instr(Assign(LVar "ret", convert_rhs rhs), next_vert))
        end
      | Return exp -> 
        let ret_vert = CFG.create_vertex cfg (Return (EVar "ret")) in
        generate_cfg_from_stmts [Expr exp] cfg ret_vert
      | ForLoopIn (idx, collection, body) -> 
        let for_vert = CFG.fresh_vertex cfg in
        (* let ret_vert = CFG.create_vertex cfg (Return(EBool true)) in *)
        let body_vert = generate_cfg_from_stmts body cfg for_vert in
        CFG.set_label cfg for_vert (ForLoopIn(convert_lhs idx, EVar "local_copy", body_vert, next_vert));
        let local_copy_vert = CFG.create_vertex cfg (Instr(Copy (LVar "local_copy", convert_rhs collection), for_vert)) in
        local_copy_vert
      | Comment -> generate_cfg_from_stmts rest cfg last_vert
      | Await exp -> CFG.create_vertex cfg (Await(LVar "ret", convert_rhs exp, next_vert))
    end

and generate_cfg_from_cond_stmts (cond_stmts : cond_stmt list) (cfg : CFG.t) (next : CFG.vertex) : CFG.vertex =
  begin match cond_stmts with
    | [] -> next
    | cond_stmt :: rest ->
      let elseif_vert = generate_cfg_from_cond_stmts rest cfg next in
      begin match cond_stmt with
        | IfElseIf(cond, stmts) ->
          let body_vert = generate_cfg_from_stmts stmts cfg next in
          CFG.create_vertex cfg (Cond(convert_rhs cond, body_vert, elseif_vert))
      end
  end

let process_func_def (func_def : func_def) (cfg : CFG.t) : function_info =
  match func_def with
  | FuncDef(func_call, _, body) ->
    let last_vertex = CFG.create_vertex cfg (Return(EBool true)) in
    let entry = generate_cfg_from_stmts body cfg last_vertex in
    begin match func_call with
      | FuncCall(func_name, params) ->
        let formals = List.map (fun param ->
            match param with Param(rhs)->
              begin match rhs with
                | VarRHS(formal) -> (formal, TString)
                | _ -> failwith "what param is this?"
              end
          ) params in
        { entry = entry
        ; name = func_name
        ; formals = formals
        ; locals = []
        }
    end

let rec process_inits (inits : var_init list) (cfg : CFG.t) : CFG.vertex =
  match inits with 
  | [] -> CFG.create_vertex cfg (Return(EBool true))
  | init :: rest -> 
    let next_vert = process_inits rest cfg in
    begin match init with
      | VarInit(_, var_name, rhs) -> 
        CFG.create_vertex cfg (Instr(Assign(LVar var_name, convert_rhs rhs), next_vert))
    end

let process_role (role_def : role_def) (cfg : CFG.t) : function_info list = 
  match role_def with
  | RoleDef(_, _, inits, func_defs) -> 
    let init_vert = process_inits inits cfg
    and init_func_name = "BASE_NODE_INIT" in
    let init_func_info = 
      { entry = init_vert
      ; name = init_func_name
      ; formals = []
      ; locals = []
      } 
    and func_infos = List.map (fun func_def -> process_func_def func_def cfg) func_defs in
    init_func_info :: func_infos


let process_client_intf (client_intf: client_def) (cfg : CFG.t) : function_info list = 
  match client_intf with
  | ClientDef(func_defs) ->
    List.map(fun func_def -> process_func_def func_def cfg) func_defs

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

let sync_exec (global_state : state) (prog : program) 
    (randomly_drop_msgs : bool) 
    (partition_away_node_one : bool)
    (cut_tail_from_mid : bool)
    (sever_all_to_tail_but_mid : bool) : unit = 
  while not ((List.length global_state.records) = 0) do
    schedule_record global_state prog 
      randomly_drop_msgs 
      partition_away_node_one 
      cut_tail_from_mid 
      sever_all_to_tail_but_mid
  done

let bootlegged_sync_exec (global_state : state) (prog : program) 
    (randomly_drop_msgs: bool) 
    (partition_away_node : bool) 
    (cut_tail_from_mid : bool)
    (sever_all_to_tail_but_mid : bool): unit = 
  for _ = 0 to 100000 do
    schedule_record global_state prog 
      randomly_drop_msgs 
      partition_away_node 
      cut_tail_from_mid 
      sever_all_to_tail_but_mid
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
    for i = 0 to num_servers - 1 do
      schedule_client global_state prog "init" [
        VNode i (* dest *)
      ; VString "Mid" (* name *)
      ; VNode (mod_op (i-1) num_servers) (* pred *)
      ; VNode (mod_op (i-2) num_servers) (* pred_pred *)
      ; VNode (mod_op (i+1) num_servers) (* succ *)
      ; VNode (mod_op (i+2) num_servers) (* succ_succ *)
      ; VNode head_idx
      ; VNode tail_idx
      ; VNode i
      ; VMap (data ())] 0;
      sync_exec global_state prog false false false false;
      (* Hashtbl.iter (fun _ _ -> print_endline "+1") data; *)
      print_endline "init mid";
    done;
    schedule_client global_state prog "init" [
      VNode head_idx (* dest *)
    ; VString "Head" (* name *)
    ; VNode (mod_op (head_idx-1) num_servers) (* pred *)
    ; VNode (mod_op (head_idx-2) num_servers) (* pred_pred *)
    ; VNode (mod_op (head_idx+1) num_servers) (* succ *)
    ; VNode (mod_op (head_idx+2)num_servers) (* succ_succ *)
    ; VNode head_idx (* head *)
    ; VNode tail_idx (* tail *)
    ; VNode head_idx
    ; VMap (data ())] 0;
    print_endline "init head";
    (* Hashtbl.iter (fun _ _ -> print_endline "+1") data; *)
    sync_exec global_state prog false false false false;
    schedule_client global_state prog "init" [
      VNode tail_idx (* dest *)
    ; VString "Tail" (* name *)
    ; VNode (mod_op (tail_idx-1) num_servers) (* pred *)
    ; VNode (mod_op (tail_idx-2) num_servers) (* pred_pred *)
    ; VNode (mod_op (tail_idx+1) num_servers) (* succ *)
    ; VNode (mod_op (tail_idx+2) num_servers) (* succ_succ *)
    ; VNode head_idx
    ; VNode tail_idx
    ; VNode tail_idx
    ; VMap (data ())] 0;
    print_endline "init tail";
    (* Hashtbl.iter (fun _ _ -> print_endline "+1") data; *)
    sync_exec global_state prog false false false false;
  | "STAR" -> raise (Failure "Not implemented STAR topology")
  | "RING" -> raise (Failure "Not implemented RING topology")
  | "FULL" -> raise (Failure "Not implemented FULL topology")
  | _ -> raise (Failure "Invalid topology")

let print_single_node (node : (value Env.t)) = 
  Env.iter (fun key value ->
      match value with 
      | VInt i -> print_endline (key ^ ": " ^ (string_of_int i))
      | VBool b -> print_endline (key ^ ": " ^ (string_of_bool b))
      | VString s -> print_endline (key ^ ": " ^ s)
      | VNode n -> print_endline (key ^ ": " ^ (string_of_int n))
      | VFuture _ -> print_endline (key ^ ": VFuture")
      | VMap m -> 
        print_endline (key ^ ": VMap iterations");
        Hashtbl.iter (fun k_str v -> 
            let k = match k_str with
              | VString s -> s
              | _ -> failwith "Key is not a string" in
            match v with
            | VInt i -> print_endline ("\t" ^ k ^ ": " ^ (string_of_int i))
            | VBool b -> print_endline ("\t" ^ k ^ ": " ^ (string_of_bool b)) 
            | VString s -> print_endline ("\t" ^ k ^ ": " ^ s)
            | VNode n -> print_endline ("\t" ^ k ^ ": " ^ (string_of_int n))
            | VFuture _ -> print_endline ("\t" ^ k ^ ": VFuture")
            | VMap _ -> print_endline ("\t" ^ k ^ ": VMap")
            | VOption _ -> print_endline ("\t" ^ k ^ ": VOptions")
            | VList _ -> print_endline ("\t" ^ k ^ ": VList")
          ) m;
      | VOption _ -> print_endline (key ^ ": VOptions")
      | VList _ -> print_endline (key ^ ": VList")
    ) node

let print_global_nodes (nodes : (value Env.t) array) = 
  Array.iter (fun node ->
      print_endline ("Node has:");
      print_single_node node;
      print_endline "";
    ) nodes

let interp (spec : string) (intermediate_output : string) : unit =
  (* Load the program into the simulator *)
  let _ = parse_file spec in ();
  let prog = 
    let ast = parse_file spec in 
    process_program ast in 
  init_topology topology global_state prog;

  schedule_client global_state prog "write" [VNode 0; VString "birthday"; VInt (increment_birthday())] 0;
  sync_exec global_state prog false false false false;
  print_endline "wrote 215";

  schedule_client global_state prog "write" [VNode 0; VString "birthday"; VInt (increment_birthday())] 0;
  bootlegged_sync_exec global_state prog false false false true;

  schedule_client global_state prog "write" [VNode 0; VString "birthday"; VInt (increment_birthday())] 0;
  bootlegged_sync_exec global_state prog false false false true;

  (* for _ = 0 to 100 do
     if (List.length global_state.free_clients > 0) then 
      begin
        let choose_client_threshold = chain_len + 1 in (* possible reads + a possible write *)
        let random_int = Random.self_init(); Random.int (List.length global_state.records + choose_client_threshold) in
        if (random_int == 0) then 
          schedule_client global_state prog "write" [VNode 0; VString "birthday"; VInt (increment_birthday())] 0
        else if (random_int < choose_client_threshold) then
          (* let read_node = Random.self_init(); Random.int chain_len in *)
          (* Printf.printf "Reading from node %d\n" read_node; *)
          (* schedule_client global_state prog "read" [VNode read_node; VString "birthday"] 0 *)
          schedule_client global_state prog "write" [VNode 0; VString "birthday"; VInt (increment_birthday())] 0
        else 
          schedule_record global_state prog false false false true
      end
     else if (List.length global_state.records > 0) then
      schedule_record global_state prog false false false true
     done; *)

  (* bootlegged_sync_exec global_state prog false false false true; *)

  let oc = open_out intermediate_output in
  Printf.fprintf oc "ClientID,Kind,Action,Node,Payload,Value\n";
  DA.iter (fun op -> 
      Printf.fprintf oc "%d," op.client_id
    ; begin match op.kind with 
      | Response -> Printf.fprintf oc "Response,"
      | Invocation -> Printf.fprintf oc "Invocation,"
    end
    ; Printf.fprintf oc "%s," op.op_action
    ; List.iter ( fun v -> match v with
        | VInt i -> Printf.fprintf oc "%d," i
        | VBool b -> Printf.fprintf oc "%s," (string_of_bool b)
        | VString s -> Printf.fprintf oc "%s," s
        | VNode n -> Printf.fprintf oc "%d," n
        | VFuture _ -> Printf.fprintf oc "TODO implement VFuture"
        | VMap _ -> Printf.fprintf oc "TODO implement VMap"
        | VOption _ -> Printf.fprintf oc "TODO implement VOptions"
        | VList _ -> Printf.fprintf oc "TODO implement VList"
      ) 
        op.payload
    ; Printf.fprintf oc "\n"
    ) global_state.history;
  print_global_nodes global_state.nodes

let handle_arguments () : string * string = 
  if Array.length Sys.argv < 3 then
    begin
      Printf.printf "Usage: %s <spec> <intermediate_output>\n" Sys.argv.(0);
      exit 1
    end
  else
    begin
      let spec = Sys.argv.(1) in
      let intermediate_output = Sys.argv.(2) in
      Printf.printf "Input spec: %s, intermediate output %s\n" spec intermediate_output;
      (spec, intermediate_output)
    end
;;

let () = 
  let spec, intermediate_output = handle_arguments () in 
  interp spec intermediate_output;
  print_endline "Program recognized as valid!";
  print_endline "Program ran successfully!"