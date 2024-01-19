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

(* let rec processExpr (expr : expr) : expr = 
  match expr with 
  | EFind (map_name, key) -> EFind (map_name, processExpr key)
  | _ -> expr *)

(* let rec processLHS (lhs : lhs) : lhs = 
  match lhs with 
  | LAccess (left, expr) -> LAccess (processLHS left, processExpr expr)
  | _ -> lhs
 *)
(* let processInstr (inst : instr) : instr =
  match inst with 
  | Assign (lhs, expr) -> Assign(processLHS lhs, processExpr expr)
  | Async (lhs, node, funcName, actuals) -> Async(processLHS lhs, node, funcName, actuals) *)

(* let rec expandRHSNodes (rhs : rhs) : rhs = 
  match rhs with 
  | FieldAccessRHS (right, field) -> FieldAccessRHS (expandRHSNodes right, field)
  | _ -> rhs *)

(* let expandLHSNodes(lhs : Ast.lhs) : Ast.lhs = 
  match lhs with
  | FieldAccessLHS (rhs, field) -> FieldAccessLHS (expandRHSNodes rhs, field)
  | _ -> lhs
 *)
(* let expandExprNodes(expr : Ast.expr) : Ast.expr = 
  match expr with 
  | Assignment (lhs, rhs) -> Assignment (expandLHSNodes lhs, expandRHSNodes rhs)
  | RHS (rhs) -> RHS (expandRHSNodes rhs) 
 *)
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
  | RpcCallRHS(_) -> failwith "TODO I don't think RPC is supposed to be here"
  | FuncCallRHS(_) -> failwith "TODO didn't implement FuncCallRHS yet"
  | DefValRHS(_) -> failwith "TODO didn't implement DefValRHS yet"
  | FieldAccessRHS (_, _) -> failwith "TODO what on earth is FieldAccessRHS again?"

(* let convertExpr(expr : Ast.expr) : Simulator.expr =
  match expr with
  | RHS(rhs) -> print_endline "convertExpr"; convertRHS(rhs)
  | Assignment(_, _) -> failwith "TODO I don't think Assignment is where it's supposed to be" *)

(* let generateLabelFromStmt (stmt : statement) (next : CFG.vertex) : CFG.vertex label = 
  match stmt with 
  | CondList (_) -> failwith "TODO implement CondList labels"
  | Return (expr) -> let next = Return(convertExpr expr) in 
  | Expr (expr) -> 
    match expr with 
    | Assignment(lhs, rhs) -> 
      begin match rhs with 
      | RpcCallRHS(rpc_call) ->
        begin match rpc_call with
        | RpcCall(node, func_call) -> 
            begin match func_call with
            | FuncCall(func_name, actuals) -> 
              let actuals = List.map (fun actual -> 
                match actual with Param(rhs) -> print_endline "generateLabelFromStmt"; convertRHS rhs
              ) actuals in
              Instr(Async(convertLHS lhs, node, func_name, actuals), next)
            end
        end
      | _ -> print_endline "Expr not an RPC"; Instr(Assign(convertLHS lhs, convertRHS rhs), next)
      end
    | RHS(rhs) -> 
      match rhs with
      | RpcCallRHS(rpc_call) -> 
        begin match rpc_call with
        | RpcCall(node, func_call) -> 
            begin match func_call with
            | FuncCall(func_name, actuals) -> 
              let actuals = List.map (fun actual -> 
                match actual with
                | Param(rhs) -> print_endline "what?"; convertRHS rhs
              ) actuals in
              Instr(Async(LVar("ret"), node, func_name, actuals), next)
            end
        end
      | _ -> failwith "TODO what else is there?" *)

let rec generateCFGFromStmtList (stmts : statement list) (cfg : CFG.t) : CFG.vertex = 
  match stmts with
  | [] -> CFG.create_vertex cfg (Return(EBool true))
  | stmt :: rest -> 
    begin match stmt with 
    | CondList (_) -> failwith "TODO implement CondList labels"
    | Return (expr) -> 
      begin match expr with
      | RHS(rhs) ->
        let return_vertex = CFG.create_vertex cfg (Return(EVar "ret")) in 
        begin match rhs with
        | RpcCallRHS(rpc_call) -> 
          begin match rpc_call with
          | RpcCall(node, func_call) -> 
            begin match func_call with
            | FuncCall(func_name, actuals) -> 
              let actuals = List.map (fun actual -> 
                match actual with Param(rhs) -> convertRHS rhs 
                ) actuals 
              in CFG.create_vertex cfg (Instr(Async(LVar("ret"), node, func_name, actuals), return_vertex))
            end
          end
        | _ -> CFG.create_vertex cfg (Return(convertRHS rhs))
        end
      | Assignment(_, _) -> failwith "Don't return an Assignment"
      end
    | Expr (expr) -> 
      let next = generateCFGFromStmtList rest cfg in
      begin match expr with 
      | Assignment(lhs, rhs) -> 
        begin match rhs with 
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
        | _ -> CFG.create_vertex cfg (Instr(Assign(convertLHS lhs, convertRHS rhs), next))
        end
      | RHS(rhs) -> 
        begin match rhs with
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
        | _ -> failwith "TODO what else is there?"
        end
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
  (* | RoleDef(_, params, inits, func_defs) -> 
    let role = match List.hd params with Param(rhs) -> 
      begin match rhs with
      | VarRHS(role_name) -> role_name
      | _ -> failwith "There shouldn't be more types here"
      end in *)
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
    List.map (fun func_def -> processFuncDef func_def cfg "client") func_defs


let processProgram (prog : prog) : program =
  match prog with 
  | Prog(roles, clientIntf) -> 
    let cfg = CFG.empty () in
    let rpcCalls = Env.create 91 in
    let clientCalls = Env.create 91 in
    let role_func_infos = processRoles roles cfg in
    let client_func_infos = processClientIntf clientIntf cfg in
    let func_infos = role_func_infos @ client_func_infos in
    let _ = List.iter (fun func_info -> Env.add rpcCalls func_info.name func_info) func_infos in
    (* List.iter (fun func_info -> Env.add clientCalls func_info.name func_info) ((Env.find rpcCalls "init")::client_func_infos); *)
    List.iter (fun func_info -> Env.add clientCalls func_info.name func_info) func_infos;
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
  schedule_client globalState myProgram "write" [VString "birthday"; VInt 214];
  schedule_record globalState myProgram;
  print_endline "...executed write";
  print_endline "read";
  schedule_client globalState myProgram "read" [VString "birthday"];
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


(* 
let processClientIntf (clientIntf : client_def) (cfg: CFG.t) : function_info list =
  match clientIntf with
  | ClientDef(func_defs) -> 
    List.map (fun func_def -> 
      match func_def with
      | FuncDef(funcCall, retType, body) -> 
        begin match retType with
        | _ -> print_endline "jenndbg assume retType int"
        end;
        List.map (fun stmt -> 
          match stmt with
          | Return(rhs) -> 
            begin match rhs with
            | VarRHS(var) -> 
              begin match var with
              | Var(varName) -> 
                let ret_vert = CFG.fresh_vertex cfg in 
                CFG.set_label cfg ret_vert (Return (EVar varName));
                ret_vert
              | _ -> failwith "Type error!"
              end
            | _ -> failwith "Type error!"
            end
          | Instr(instr) -> 
            begin match instr with
            | Assign(lhs, rhs) -> 
              begin match lhs with
              | LVar(varName) -> 
                begin match rhs with
                | EVar(varName) -> 
                  let assign_vert = CFG.fresh_vertex cfg in 
                  CFG.set_label cfg assign_vert (Instr(Assign (LVar varName, EVar varName)));
                  assign_vert
                | _ -> failwith "Type error!"
                end
              | _ -> failwith "Type error!"
              end
            | _ -> failwith "Type error!"
            end
        ) body;
        begin match funcCall with 
        | FuncCall(funcName, params) -> 
          let formals = List.map (fun param -> 
            match param with Param(rhs) -> 
              begin match rhs with
              | VarRHS(formal) -> (formal, TString)
              | _ -> failwith "Type error!"
              end
          ) params in
          { entry = 0
          ; name = funcName
          ; formals = formals
          ; locals = [] }
        end
    ) func_defs *)

(** [interp] interprets [f] by parsing
    and evaluating it with the big-step model. *)
(* let interp (f : string) : program =
  let ast = parse_file f in
  match ast with 
  | Prog(roles, clientIntf) -> print_endline "Prog";
    (* process roles *) 
    List.iter (fun role -> 
      match role with
      (* | RoleDef(roleName, params, initVars, func_defs) -> print_endline "" *)
      | RoleDef(role_name, params, inits, func_defs) ->
        print_endline ("RoleDef: " ^ role_name);
        (* process params *)
        List.iter (fun param -> 
          begin match param with Param(rhs) -> 
            begin match rhs with
            | VarRHS(formal) -> print_endline formal
            | _ -> failwith "Type error!"
            end
          end
        ) params;
        (* process inits *)
        List.iter (fun init -> 
          begin match init with VarInit(typ, name, rhs) -> 
            print_endline "typ is something";
            begin match rhs with 
            | EmptyMap -> Instr(Assign(LVar(name), EMap))
            | Options _ -> failswith "TODO"
            end
          end
        ) inits;
        (* process func_defs *)
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
;; *)
(* let interp (f : string) : prog = 
  let ast = parse_file f in ast;; *)

interp "/Users/jenniferlam/jennLang/bin/simple_spec.jenn"
let () = print_endline "Program recognized as valid!"

(* let () = 
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
    ; client_ops = [
      Env.find rpcCalls "Write"
      ; Env.find rpcCalls "Read"
      ; Env.find rpcCalls "Init"] } in
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
      globalState.history;; *)

let () = print_endline "Program ran successfully!"



