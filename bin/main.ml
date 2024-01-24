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
            in CFG.create_vertex cfg (Instr(Async(LVar("async_future"), node, func_name, actuals), await_vertex))
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
                CFG.create_vertex cfg (Instr(Async(convertLHS lhs, node, func_name, actuals), next))
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
              CFG.create_vertex cfg (Instr(Async(LVar("ret"), node, func_name, actuals), next)) 
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
  
let rec processInits (inits : var_init list) (cfg : CFG.t): CFG.vertex = 
  match inits with
  | [] -> CFG.create_vertex cfg (Return(EBool true))
  | init::rest -> 
    let next = processInits rest cfg in
    let label = match init with VarInit(_, var_name, default_value) -> 
      begin match default_value with 
        | EmptyMap -> Instr(Assign(LVar(var_name), EMap), next)
        | Options _ -> failwith "TODO implement Options"
      end
    in CFG.create_vertex cfg label

let processRoleDef (role_def : role_def) (cfg : CFG.t) : function_info list =
  match role_def with 
  | RoleDef(_, _, inits, func_defs) ->
    let init_func_info = 
      let init_vertex = processInits inits cfg in 
      { entry = init_vertex
      ; name = "init"
      ; formals = []
      ; locals = [] }
    and func_infos = List.map (fun func_def -> processFuncDef func_def cfg "") func_defs
    in init_func_info :: func_infos

let processRoles (roles : role_def list) (cfg : CFG.t) : function_info list =
  List.concat (List.map (fun role_def -> processRoleDef role_def cfg) roles)

let processClientIntf (clientIntf : client_def) (cfg: CFG.t) : function_info list =
  match clientIntf with
  | ClientDef(func_defs) -> 
    List.map (fun func_def -> processFuncDef func_def cfg "") func_defs


let processProgram (prog : prog) : program =
  match prog with 
  | Prog(roles, clientIntf) -> 
    let cfg = CFG.empty () in
    let rpcCalls = Env.create 91 in
    let clientCalls = Env.create 91 in
    let role_func_infos = processRoles roles cfg in
    let client_func_infos = processClientIntf clientIntf cfg in
    let func_infos = role_func_infos @ client_func_infos in
    let _ = List.iter (fun func_info -> print_endline ("add to rpcnames " ^ func_info.name);Env.add rpcCalls func_info.name func_info) func_infos in
    List.iter (fun func_info -> Env.add clientCalls func_info.name func_info) ((Env.find rpcCalls "init")::client_func_infos);
    (* List.iter (fun func_info -> Env.add clientCalls func_info.name func_info) func_infos; *)
    let myProgram = 
      { cfg = cfg
      ; rpc = rpcCalls
      ; client_ops = clientCalls } in
    myProgram

let interp (f : string) : unit =
  let globalState = 
      { nodes = Array.make 1 (Env.create 91)  (* Replace 10 with the desired number of nodes *)
      ; records = []
      ; history = DA.create ()  (* Assuming DA.create creates an empty dynamic array *)
      ; free_clients = [0] } 
  and myProgram = 
    let ast = parse_file f 
  in processProgram ast in
  print_endline "attempt to execute init...";
  schedule_client globalState myProgram "init" [];
  schedule_record globalState myProgram;
  print_endline "...executed init";
  print_endline "attempt to execute write...";
  schedule_client globalState myProgram "write" [VNode 0; VString "birthday"; VInt 214];
  while not (List.is_empty globalState.records) do
    schedule_record globalState myProgram;
  done;
  print_endline "...executed write";
  print_endline "attempt to execute read...";
  schedule_client globalState myProgram "read" [VNode 0; VString "birthday"];
  while not (List.is_empty globalState.records) do
    schedule_record globalState myProgram;
  done;
  print_endline "...executed read";
  let oc = open_out "output.csv" in
  Printf.fprintf oc "ClientID,Kind,Action,Server,Payload,Value\n";
  DA.iter (fun op -> 
    Printf.fprintf oc "%d," op.client_id
    (* print_string op.op_action *)
    ; begin match op.kind with 
      (* | Response -> print_string " Response" *)
      | Response -> Printf.fprintf oc "Response,"
      (* | Invocation -> print_string " Invocation" *)
      | Invocation -> Printf.fprintf oc "Invocation,"
    end
    ; Printf.fprintf oc "%s," op.op_action
    (* ; List.iter (fun v -> print_string " " *)
    ; List.iter ( fun v -> match v with
      (* | VInt i -> print_int i *)
      | VInt i -> Printf.fprintf oc "%d," i
      (* | VBool b -> print_string (string_of_bool b) *)
      | VBool b -> Printf.fprintf oc "%s," (string_of_bool b)
      (* | VMap m -> print_string (string_of_map m) *)
      | VString s -> Printf.fprintf oc "%s," s
      | VNode n -> Printf.fprintf oc "%d," n
      | VFuture _ -> Printf.fprintf oc "TODO implement VFuture"
      | _ -> failwith "Type error!") 
      op.payload
    (* ; print_endline "")  *)
    ; Printf.fprintf oc "\n"
    )
      globalState.history;;

interp "/Users/jenniferlam/jennLang/bin/simple_spec.jenn"
let () = print_endline "Program recognized as valid!"
let () = print_endline "Program ran successfully!"



