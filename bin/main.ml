open Mylib.Ast
open Mylib
open Mylib.Simulator

let parse_file (filename : string) : prog =
  let ic = open_in filename in
  let lexbuf = Lexing.from_channel ic in
  let ast = Parser.program Lexer.token lexbuf in
  close_in ic;
  ast

let roleNames = ["Head"; "Mid"; "Tail"]
let topology_config = Env.create (List.length roleNames)
let () = for i = 0 to (List.length roleNames) - 1 do
  Env.add topology_config (List.nth roleNames i) i
done
let topology_config (role : string) : Simulator.value = 
  VNode (Env.find topology_config role)

let convertLHS(lhs : Ast.lhs) : Simulator.lhs =
  match lhs with 
  | VarLHS (var_name) -> LVar(var_name)
  | MapAccessLHS (map_name, key) -> LAccess(LVar(map_name), EVar(key))
  | FieldAccessLHS (_, _) -> failwith "TODO what on earth is FieldAccessLHS again?"

let convertRHS(rhs: rhs) : Simulator.expr = 
  match rhs with 
  | Bool(b) -> EBool(b)
  | VarRHS(var) -> EVar(var)
  | MapAccessRHS(map_name, key) -> EFind(map_name, EVar(key))
  | FuncCallRHS(_) -> failwith "TODO didn't implement FuncCallRHS yet"
  | DefValRHS(_) -> failwith "TODO didn't implement DefValRHS yet"
  | FieldAccessRHS (_, _) -> failwith "TODO what on earth is FieldAccessRHS again?"

let rec generateCFGFromStmtList (stmts : statement list) (cfg : CFG.t) : CFG.vertex = 
  match stmts with
  | [] -> CFG.create_vertex cfg (Return(EBool true))
  | stmt :: rest -> 
    begin match stmt with 
    | CondList (_) -> failwith "TODO implement CondList labels"
    | Return (expr) -> 
      begin match expr with
      | RHS(rhs) -> CFG.create_vertex cfg (Return(convertRHS rhs))
      | RpcCallRHS(rpc_call) ->
        let return_vertex = CFG.create_vertex cfg (Return(EVar "ret")) in
        let await_vertex = CFG.create_vertex cfg (Await(LVar "ret", EVar "async_future", return_vertex)) in
        begin match rpc_call with
        | RpcCall(node, func_call) -> 
          begin match func_call with
          | FuncCall(func_name, actuals) -> 
            let actuals = List.map (fun actual -> 
              match actual with Param(rhs) -> convertRHS rhs
              ) actuals 
            (* in begin match node with 
            | EVar n -> CFG.create_vertex cfg (Instr(Async(LVar("async_future"), n, func_name, actuals), await_vertex))
            | _ -> CFG.create_vertex cfg (Instr(Async(LVar("async_future"), (EVar node), func_name, actuals), await_vertex))
            end *)
            in CFG.create_vertex cfg (Instr(Async(LVar("async_future"), (EVar node), func_name, actuals), await_vertex))
          end
        end
      | Assignment(_, _) -> failwith "Don't return an Assignment"
      end
    | Expr (expr) -> 
      let next = generateCFGFromStmtList rest cfg in
      begin match expr with 
      | Assignment(lhs, exp) -> 
        begin match exp with
        | RHS(rhs) -> 
          let next = generateCFGFromStmtList rest cfg in 
          CFG.create_vertex cfg (Instr(Assign(convertLHS lhs, convertRHS rhs), next))
        | RpcCallRHS(rpc_call) ->
            begin match rpc_call with
            | RpcCall(node, func_call) -> 
              begin match func_call with
              | FuncCall(func_name, actuals) -> 
                let actuals = List.map (fun actual -> 
                  match actual with Param(rhs) -> convertRHS rhs
                  ) actuals in
                let assign_vert = CFG.create_vertex cfg (Instr(Assign(convertLHS lhs, EVar "dontcare"), next)) in
                let await_vertex = CFG.create_vertex cfg (Await(LVar("dontcare"), EVar "async_future", assign_vert)) in
                CFG.create_vertex cfg (Instr(Async(LVar("async_future"), EVar node, func_name, actuals), await_vertex))
              end
            end
        | Assignment(_, _) -> failwith "Don't assign an Assignment"
        end
      | RpcCallRHS(rpc_call) -> 
          begin match rpc_call with
          | RpcCall(node, func_call) -> 
            begin match func_call with
            | FuncCall(func_name, actuals) -> 
              let actuals = List.map (fun actual -> 
                match actual with Param(rhs) -> convertRHS rhs
              ) actuals in
              let await_vert = CFG.create_vertex cfg (Await(LVar("dontcare"), EVar "async_future", next)) in
              CFG.create_vertex cfg (Instr(Async(LVar("async_future"), EVar node, func_name, actuals), await_vert)) 
            end
          end
      | RHS(_) -> failwith "No standalone RHS"
      end
    end
    
let processFuncDef (func_def : func_def) (cfg : CFG.t) (suffix : string) : function_info =
  match func_def with 
  | FuncDef(funcCall, _, body) -> 
    let entry = generateCFGFromStmtList body cfg in
    begin match funcCall with 
    | FuncCall(funcName, params) -> 
      let formals = List.map (fun param -> 
        match param with Param(rhs) -> 
          begin match rhs with
          | VarRHS(formal) -> (formal, TString)
          | _ -> failwith "Type error!"
          end
      ) params in
      { entry = entry
      ; name = funcName ^ suffix
      ; formals = formals
      ; locals = [] }
    end
  
let rec processInits (inits : var_init list) (cfg : CFG.t)  : CFG.vertex = 
  match inits with
  | [] -> CFG.create_vertex cfg (Return(EBool true))
  | init::rest -> 
    let next = processInits rest cfg  in
    let label = match init with VarInit(_, var_name, default_value) -> 
      begin match default_value with 
        | EmptyMap -> Instr(Assign(LVar(var_name), EMap), next)
        | String var -> Instr(Assign(LVar(var_name), EString(var)), next)
        | Options _ -> failwith "TODO implement Options"
      end
    in CFG.create_vertex cfg label

let processRoleDef (role_def : role_def) (cfg : CFG.t) : function_info list =
  match role_def with 
  | RoleDef(role_name, _, inits, func_defs) ->
    let init_on_func_info = 
      let func_name = "init_on_" ^ role_name in
      let init_vertex = processInits inits cfg in
      { entry = init_vertex
      ; name = func_name
      ; formals = []
      ; locals = [] } in
    let init_func_info =
      let ret_vert = CFG.create_vertex cfg (Return(EBool true)) in
      let await_vert = CFG.create_vertex cfg (Await(LVar("dontcare"), EVar("dontcare"), ret_vert)) in
      let async_label = Instr(Async(LVar("dontcare"), EVar role_name, "init_on", []), await_vert) in
      let async_vert = CFG.create_vertex cfg async_label in
      { entry = async_vert
    ; name = "init_" ^ role_name
    ; formals = []
    ; locals = []} in
    let func_infos = List.map (fun func_def -> processFuncDef func_def cfg ("_" ^ role_name)) func_defs
    in init_func_info :: init_on_func_info :: func_infos

let processRoles (roles : role_def list) (cfg : CFG.t) : function_info list =
  List.concat (List.map (fun role_def -> processRoleDef role_def cfg) roles)

let processClientIntf (clientIntf : client_def) (cfg: CFG.t) : function_info list =
  match clientIntf with
  | ClientDef(func_defs) -> 
    List.map (fun func_def -> processFuncDef func_def cfg "_client") func_defs

let printSingleNode (node : (value Env.t)) = 
  Env.iter (fun key value ->
    match value with 
    | VInt i -> print_endline (key ^ ": " ^ (string_of_int i))
    | VBool b -> print_endline (key ^ ": " ^ (string_of_bool b))
    | VString s -> print_endline (key ^ ": " ^ s)
    | VNode n -> print_endline (key ^ ": " ^ (string_of_int n))
    | VFuture _ -> print_endline (key ^ ": VFuture")
    | VMap _ -> print_endline (key ^ ": VMap")
    | VOption _ -> print_endline (key ^ ": VOptions")
  ) node
let print_global_nodes (nodes : (value Env.t) array) = 
  Array.iter (fun node ->
    print_endline ("Node has:");
    printSingleNode node;
    print_endline "";
  ) nodes

let processProgram (prog : prog) : program =
  match prog with 
  | Prog(roles, clientIntf) -> 
    let cfg = CFG.empty () in
    let rpcCalls = Env.create 91 in
    let clientCalls = Env.create 91 in
    let role_func_infos = processRoles roles cfg in
    let client_func_infos = processClientIntf clientIntf cfg in
    let func_infos = role_func_infos @ client_func_infos in
    let _ = List.iter (fun func_info ->
       Env.add rpcCalls func_info.name func_info
       ) func_infos in
    for i = 0 to (List.length roles) - 1 do
      let init_funcname = "init_" ^ (List.nth roleNames i) in
      Env.add clientCalls init_funcname (Env.find rpcCalls init_funcname)
    done;
    List.iter (fun func_info -> Env.add clientCalls func_info.name func_info) client_func_infos;
    let myProgram = 
      { cfg = cfg
      ; rpc = rpcCalls
      ; client_ops = clientCalls } in
    myProgram

let interp (f : string) : unit =
  let globalState = 
      { nodes = Array.init 4 (fun _ -> Env.create 91)  (* Replace 10 with the desired number of nodes *)
      ; records = []
      ; history = DA.create ()  (* Assuming DA.create creates an empty dynamic array *)
      ; free_clients = [3] } in
  (* Load the topology into every node *)
  for node = 0 to ((Array.length globalState.nodes) - 1) do
    for i = 0 to (List.length roleNames) - 1 do
      let roleName = List.nth roleNames i in
      let node_map = globalState.nodes.(node) in
      Env.add node_map roleName (topology_config roleName);
    done;
  done;
  (* Load the program into the simulator *)
  let myProgram = 
    let ast = parse_file f 
  in processProgram ast in
  print_endline "attempt to execute init...";
  List.iter (fun roleName -> 
    schedule_client globalState myProgram ("init_" ^ roleName) [];
    while not (List.is_empty globalState.records) do
      schedule_record globalState myProgram;
    done) roleNames;
  print_endline "...executed init";
  print_endline "attempt to execute write...";
  schedule_client globalState myProgram "write_client" [VString "birthday"; VInt 214];
  while not (List.is_empty globalState.records) do
    schedule_record globalState myProgram;
  done;
  print_endline "...executed write";
  print_endline "attempt to execute read...";
  schedule_client globalState myProgram "read_client" [VString "birthday"];
  while not (List.is_empty globalState.records) do
    schedule_record globalState myProgram;
  done;
  print_endline "...executed read";
  let oc = open_out "output.csv" in
  Printf.fprintf oc "ClientID,Kind,Action,Server,Payload,Value\n";
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
      | _ -> failwith "Type error!") 
      op.payload
    ; Printf.fprintf oc "\n"
    ) globalState.history;
    print_global_nodes globalState.nodes;
  ;;

(* When changing config, remember to:
1. change roleNames variable
2. change the number of nodes in global state
3. change the client idx
*)
interp "/Users/jenniferlam/jennLang/bin/CR.jenn"
let () = print_endline "Program recognized as valid!"
let () = print_endline "Program ran successfully!"