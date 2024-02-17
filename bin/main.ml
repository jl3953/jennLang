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

let convert_lhs(lhs : Ast.lhs) : Simulator.lhs =
  match lhs with 
  | VarLHS (var_name) -> LVar(var_name)
  | MapAccessLHS (map_name, key) -> LAccess(LVar(map_name), EVar(key))
  | FieldAccessLHS (_, _) -> failwith "TODO what on earth is FieldAccessLHS again?"

let rec convert_rhs (rhs : rhs) : Simulator.expr =
  match rhs with
  | VarRHS var -> EVar(var)
  | MapAccessRHS(map, key) -> EFind(map, EVar(key))
  | FuncCallRHS _ -> failwith "Didn't implement FuncCallRHS yet"
  | Literal literal -> 
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
    | Expr expr -> 
      begin match expr with
      | Assignment (lhs, exp) -> 
        begin match exp with
        | RHS(rhs) -> 
          CFG.create_vertex cfg (Instr(Assign(convert_lhs lhs, convert_rhs rhs), next_vert))
        | RpcCallRHS(rpc_call) ->
            begin match rpc_call with
            | RpcCall(node, func_call) -> 
              begin match func_call with
              | FuncCall(func_name, actuals) -> 
                let actuals = List.map (fun actual -> 
                  match actual with Param(rhs) -> convert_rhs rhs
                  ) actuals in
                let assign_vert = CFG.create_vertex cfg (Instr(Assign(convert_lhs lhs, EVar "dontcare"), next_vert)) in
                let await_vertex = CFG.create_vertex cfg (Await(LVar("dontcare"), EVar "async_future", assign_vert)) in
                CFG.create_vertex cfg (Instr(Async(LVar("async_future"), EVar node, func_name, actuals), await_vertex))
              end
            | RpcAsyncCall (node, func_call) -> 
              begin match func_call with
              | FuncCall(func_name, actuals) ->
                let actuals = List.map (fun actual -> 
                  match actual with Param(rhs) -> convert_rhs rhs
                  ) actuals in
                CFG.create_vertex cfg (Instr(Async(LVar("async_future"), EVar node, func_name, actuals), next_vert))
              end
            end
        | Assignment(_, _) -> failwith "Don't assign an Assignment"
        end
      | RHS _ -> failwith "Not implemented rhs"
      | RpcCallRHS _ -> failwith "Not implemented rpc call"
      end
    | Return (_) -> failwith "Not implemented return"
    | ForLoop (_) -> failwith "Not implemented for loop"
    | Comment -> generate_cfg_from_stmts rest cfg last_vert
    | Await (_) -> failwith "Not implemented await"
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

let process_role (_ : role_def) (_ : CFG.t) : function_info list = 
  []

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
  
interp "/Users/jenniferlam/jennLang/bin/CRAQ.jenn"
let () = print_endline "Program recognized as valid!"
let () = print_endline "Program ran successfully!"