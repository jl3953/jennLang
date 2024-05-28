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

let global_state = 
      { nodes = Array.init (num_servers + num_clients) (fun _ -> Env.create 91) 
      ; records = []
      ; history = DA.create () 
      ; free_clients = List.init num_clients (fun i -> num_servers + i) }

let rec convert_lhs(lhs : Ast.lhs) : Simulator.lhs =
  match lhs with 
  | VarLHS (var_name) -> LVar(var_name)
  | MapAccessLHS (map_name, key) -> LAccess(convert_lhs map_name, convert_rhs key)
  | FieldAccessLHS (_, _) -> failwith "TODO what on earth is FieldAccessLHS again?"
  | TupleLHS lefts -> LTuple lefts

and convert_rhs (rhs : rhs) : Simulator.expr =
  match rhs with
  | VarRHS var -> EVar(var)
  | MapAccessRHS(map, key) -> EFind(map, EVar(key))
  | ListAccessRHS(list, idx) -> EIdx(convert_rhs list, convert_rhs idx)
  | FuncCallRHS func_call ->
    begin match func_call with
    | FuncCall(func_name, _) -> failwith ("Didn't implement FuncCallRHS yet func: " ^ func_name)
    end
  | StringRHS s_rhs -> 
    begin match s_rhs with 
    | String s -> EString s 
    end
  | IntRHS i ->
    begin match i with
    | Int i -> EInt i
    | PlusInt (rhs1, rhs2) -> EPlusInt(convert_rhs rhs1, convert_rhs rhs2)
    | MinusInt (rhs1, rhs2) -> EMinusInt(convert_rhs rhs1, convert_rhs rhs2)
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
    | Contains (rhs1, rhs2) -> EContains(convert_rhs rhs1, convert_rhs rhs2)
    end 
  | CollectionRHS collection_lit ->
    begin match collection_lit with
    | MapLit kvpairs -> EMap (List.map (fun (k, v) -> print_endline ("jenndebug k " ^ k); (k, convert_rhs v)) kvpairs);
    | ListLit items -> EList (List.map (fun (v) -> convert_rhs v) items)
    end
  | RpcCallRHS _ -> failwith "Didn't implement RpcCallRHS yet"
  | Append (rhs1, rhs2) -> EAppend(convert_rhs rhs1, convert_rhs rhs2)
  | Len (rhs) -> ELen(convert_rhs rhs)

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
              CFG.create_vertex cfg (Instr(Async(LVar "async_future", EVar node, func_name, actuals), await_vertex))
            end
          | RpcAsyncCall (node, func_call) -> 
            begin match func_call with
            | FuncCall(func_name, actuals) ->
              let actuals = List.map (fun actual -> 
                match actual with Param(rhs) -> convert_rhs rhs
                ) actuals in
                CFG.create_vertex cfg (Instr(Async(LVar "ret", EVar node, func_name, actuals), next_vert))
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

let sync_exec (global_state : state) (prog : program) : unit = 
  while not ((List.length global_state.records) = 0) do
    schedule_record global_state prog (-1)
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
      sync_exec global_state prog;
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
    sync_exec global_state prog;
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
    sync_exec global_state prog;

  | "STAR" -> raise (Failure "Not implemented STAR topology")
  | "RING" -> raise (Failure "Not implemented RING topology")
  | "FULL" -> raise (Failure "Not implemented FULL topology")
  | _ -> raise (Failure "Invalid topology")


let rec to_string (prefix : string) (value : value) (suffix : string) =
  begin match value with 
  | VInt i -> print_string (prefix ^ "VInt " ^ string_of_int i ^ suffix)
  | VBool b -> print_string (prefix ^ "VBool " ^ string_of_bool b ^ suffix)
  | VString s -> print_string (prefix ^ "VString " ^ s ^ suffix)
  | VNode n -> print_string(prefix ^ "VNode " ^ string_of_int n ^ suffix)
  | VFuture _ -> print_string (prefix ^ "VFuture" ^ suffix)
  | VMap m -> print_endline (prefix ^ "VMap::");
    Hashtbl.iter (fun k v -> to_string (prefix ^ "\t mapkey ") k "->"; to_string "" v "\n"
    ) m;
    print_string suffix
  | VOption _ -> print_string (prefix ^ "VOption" ^ suffix)
  | VList m_list -> print_endline (prefix ^ "List::"); 
    mutable_iter (fun v -> to_string (prefix ^ "\t") v "\n") m_list;
    print_string suffix
  end

let print_single_node (node : (value Env.t)) = 
  Env.iter (fun key value -> 
    print_string ("key " ^ key ^ "->"); 
    to_string "" value "\n"
    ) node

let print_global_nodes (nodes : (value Env.t) array) = 
  Array.iter (fun node ->
    print_endline ("Node has:");
    print_single_node node;
    print_endline "";
  ) nodes

let interp (f : string) : unit =
  (* Load the program into the simulator *)
  let _ = parse_file f in ();
  let prog = 
    let ast = parse_file f in 
    process_program ast in 
  init_topology topology global_state prog;
  schedule_client global_state prog "write" [VNode 0; VString "birthday"; VInt 812] 0;
  sync_exec global_state prog;
  schedule_client global_state prog "read" [VNode 0; VString "birthday"] 0;
  sync_exec global_state prog; 
  print_global_nodes global_state.nodes;
  (* schedule_client global_state prog "triggerFailover" [VNode 0; VNode 1; VNode 3] 0;
  sync_exec global_state prog;
  schedule_client global_state prog "triggerFailover" [VNode 2; VNode 1; VNode 3] 0;
  sync_exec global_state prog;
  schedule_client global_state prog "triggerFailover" [VNode 3; VNode 1; VNode 3] 0;
  sync_exec global_state prog; *)
  (* schedule_client global_state prog "write" [VNode 0; VString "university"; VString "Princeton"] 0; *)
  (* sync_exec global_state prog; *)
  (* schedule_client global_state prog "read" [VNode 0; VString "university"] 0;
  sync_exec global_state prog; *)
  
  let oc = open_out "output.csv" in
  Printf.fprintf oc "ClientID,Kind,Action,Payload,Value\n";
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
    print_global_nodes global_state.nodes;
;;
  
interp "/Users/jenniferlam/jennLang/bin/CRAQ.jenn"
let () = print_endline "Program recognized as valid!"
let () = print_endline "Program ran successfully!"