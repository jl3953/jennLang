module DA = BatDynArray

(* A couple of features of the language in ast.ml make it difficult to
   implement directly:
   - RPCs and function calls in RHSs are complicated (e.g., consider an RPC as
     an argument of an RPC).  If there's a need for such constructs, the usual
     solution is to translate them away -- e.g.,
       y = f(g(x))
     gets translated to the IR
       tmp = g(x)
       y = f(tmp)
   - An RPC to a func that nominally returns (say) a string cannot evaluate to
     an string -- otherwise, the only way to execute the program is to preempt
     the current activation record and wait until the RPC returns to resume.  In
     particular, this makes it very difficult to implement fault-tolerant
     protocols -- if node A calls an RPC on node B and node B fails, then node
     A's activation record is blocked forever.  The proposed alternative is that
     an RPC that nomially returns a string evaluates to Future<string>.  We can
     manipulate a valute of type Future<string> by
   - checking whether its value is available (e.g. fut.isAvailable() -> bool)
       (nonpreemptible)
   - retrieving its value (e.g. fut.isValue() -> string) (preemptible)
   - In general, I do not understand how "Roles" should be implemented
*)

type expr =
  | EVar of string
  | EFind of expr * expr
  | EInt of int
  | EBool of bool
  | ENot of expr
  | EAnd of expr * expr
  | EOr of expr * expr
  | EEqualsEquals of expr * expr
  | EMap of (string * expr) list
  | EList of expr list
  | EListPrepend of expr * expr
  | EListAppend of expr * expr
  | EString of string
  | ELessThan of expr * expr
  | ELessThanEquals of expr * expr
  | EGreaterThan of expr * expr
  | EGreaterThanEquals of expr * expr
  | EListLen of expr
  | EListAccess of expr * int
[@@deriving ord]

type lhs =
  | LVar of string
  | LAccess of lhs * expr
  | LTuple of string list
[@@deriving ord]

type instr =
  | Assign of lhs * expr (* jenndbg probably assigning map values? *)
  | Async of lhs * expr * string * (expr list) (* jenndbg RPC*) 
  | Copy of lhs * expr
  (* | Write of string * string (*jenndbg write a value *) *)
[@@deriving ord]

(* Static types *)
type typ =
  | TInt
  | TBool
  | TMap of typ * typ
  | TOption of typ
  | TFuture of typ
  | TNode
  | TString

(* Run-time values *)
type value =
  | VInt of int
  | VBool of bool
  | VMap of (value, value) Hashtbl.t
  | VList of value list
  | VOption of (value option)
  | VFuture of (value option) ref
  | VNode of int
  | VString of string

(* Run-time value of a left-hand-side *)
type lvalue =
  | LVVar of string
  | LVAccess of (value * (value, value) Hashtbl.t)
  | LVTuple of string list

module Env = Hashtbl.Make(struct
    type t = string
    let hash = Hashtbl.hash
    let equal = (=)
  end)

type 'a label =
  | Instr of instr * 'a (* jenndbg assignments or RPCs *)
  | Pause of 'a   (* Insert pause to allow the scheduler to interrupt! *)
  | Await of lhs * expr * 'a
  | Return of expr (* jenndbg return...I guess? *)
  (*| Read (* jenndbg read a value *)*)
  | Cond of expr * 'a * 'a
  | ForLoopIn of lhs * expr * 'a * 'a

let to_string(l: 'a label) : string =
  match l with
  | Instr (i, _) -> 
    begin
      match i with 
      | Async (_, _, f, _) -> "instr async to " ^ f
      | Assign (_, _) -> "instr assign"
      | Copy (_, _) -> "instr copy"
    end
  | Pause _ -> "Pause"
  | Await _ -> "Await"
  | Return _ -> "Return"
  | Cond _ -> "Cond"
  | ForLoopIn _ -> "ForLoopIn"

module CFG : sig
  type t (* jenndbg: control flow graph type *)
  type vertex (* jenndbg: vertex of the control flow graph *)
  val empty : unit -> t (* jenndbg: create an empty control flow graph *)
  val label : t -> vertex -> vertex label (* jenndbg: gets vertex label of vertex*)
  val set_label : t -> vertex -> vertex label -> unit (* jenndbg: sets vertex label of vertex *)
  val create_vertex : t -> vertex label -> vertex (* jenndbg: creates a vertex with label *)
  val fresh_vertex : t -> vertex (* jenndbg creates an empty vertex without passing in a label*)
end = struct
  type vertex = int
  type t = (vertex label) DA.t
  let empty = DA.create
  let label = DA.get (* jenndbg includes an instruction + PC *)
  let set_label = DA.set
  let create_vertex cfg label =
    let id = DA.length cfg in
    DA.add cfg label;
    id
  let fresh_vertex cfg =
    let id = DA.length cfg in
    DA.add cfg (Instr (Assign (LVar "Skip", EVar "skip"), id)); (*jenndbg so this is how you create a vertex*)
    id
end

(* Activation records *)
(* jenndbg I think nodes are uniquely identified by their IDs *)
(* jenndbg I think a record is a type of vertex*)
type record =
  { mutable pc : CFG.vertex
  ; node : int
  ; continuation : value -> unit (* Called when activation record returns
                                    For RPCs, this writes to the associate future;
                                    For client operations it appends to the history *)
  ; env : value Env.t 
  ; id : int 
  ; mutable x : float (* threshold for being chosen to be executed, when scheduler is implementing a delay. *)
  ; f : float -> float (* updates x every time this record is not chosen *)
  }

type op_kind = Invocation | Response

type operation =
  { client_id : int
  ; op_action : string
  ; kind : op_kind
  ; payload : value list 
  ; unique_id : int }

(* Global state *)
type state =
  { nodes : (value Env.t) array
  ; mutable records : record list
  ; history : operation DA.t
  ; mutable free_clients : int list (* client ids should be valid indexes into nodes *)
  ; mutable free_sys_threads : int list (* internal systems threads *)
  }

(* Execution environment of an activation record: local variables +
   node-scoped variables. *)
type record_env =
  { local_env : value Env.t
  ; node_env : value Env.t }

type function_info =
  { entry : CFG.vertex
  ; name : string
  ; formals : (string * typ) list
  ; locals : (string * typ * expr) list }

(* Representation of program syntax *)
type program =
  { cfg : CFG.t (* jenndbg this is its control flow *)
  ; rpc : function_info Env.t 
  ; client_ops : function_info Env.t }(* jenndbg why does an RPC handler need a list of function info *)

let load (var : string) (env : record_env) : value =
  try begin 
    Env.find env.local_env var
  end
  with Not_found -> begin 
      Env.find env.node_env var
    end

(* Evaluate an expression in the context of an environment. *)
let rec eval (env : record_env) (expr : expr) : value =
  match expr with
  | EInt i -> VInt i
  | EBool b -> VBool b
  | EVar v -> load v env
  | EFind (c, k) ->
    begin match eval env c with
    | VMap map -> Hashtbl.find map (eval env k)
    | VList l -> 
      begin match l with 
        | [] -> failwith "Cannot index into empty list"
        | _ ->
          begin match eval env k with 
          | VInt i -> 
            if i < 0 || i >= List.length l then 
              failwith "idx out of range"
            else
            List.nth l i
          | _ -> failwith "Cannot index into a list with non-integer"
          end
      end
    | VString s -> 
      begin match load s env with
        | VMap map -> Hashtbl.find map (eval env k)
        | _ -> failwith "EFind eval fail"
      end
    | _ -> failwith "EFind eval fail"
    end
  | ENot e -> 
    begin match eval env e with
      | VBool b -> VBool (not b)
      | _ -> failwith "ENot eval fail"
    end
  | EAnd (e1, e2) ->
    begin match eval env e1, eval env e2 with
      | VBool b1, VBool b2 -> VBool (b1 && b2)
      | _ -> failwith "EAnd eval fail"
    end
  | EOr (e1, e2) ->
    begin match eval env e1, eval env e2 with
      | VBool b1, VBool b2 -> VBool (b1 || b2)
      | _ -> failwith "EOr eval fail"
    end
  | EEqualsEquals (e1, e2) ->
    begin match eval env e1, eval env e2 with
      | VInt i1, VInt i2 -> VBool (i1 = i2)
      | VBool b1, VBool b2 -> VBool (b1 = b2)
      | VString s1, VString s2 -> VBool (s1 = s2)
      | VNode n1, VNode n2 -> VBool (n1 = n2)
      | _ -> failwith "EEqualsEquals eval fail"
    end
  | EMap kvpairs -> 
    let rec makemap (kvpairs : (string * expr) list) : (value, value) Hashtbl.t =
      begin match kvpairs with
        | [] -> Hashtbl.create 91
        | (k, v) :: rest ->
          let tbl = makemap rest in
          Hashtbl.add (makemap rest) (VString k) (eval env v); 
          tbl
      end in 
    VMap (makemap kvpairs)
  | EList exprs ->
    let rec makelist (exprs : expr list) : value list =
      begin match exprs with
        | [] -> []
        | e :: rest -> (eval env e) :: (makelist rest)
      end in
    VList (makelist exprs)
  | EListPrepend (item, ls) ->
    begin match eval env item, eval env ls with
      | v, VList l -> VList (v :: l)
      | _ -> failwith "EListPrepend eval fail"
    end
  | EListAppend (ls, item) ->
    begin match eval env ls, eval env item with
      | VList l, v -> VList (l @ [v])
      | _ -> failwith "EListAppend eval fail"
    end
  | EString s -> VString s
  | ELessThan (e1, e2) ->
    begin match eval env e1, eval env e2 with
      | VInt i1, VInt i2 -> VBool (i1 < i2)
      | _ -> failwith "ELessThan eval fail"
    end
  | ELessThanEquals (e1, e2) ->
    begin match eval env e1, eval env e2 with
      | VInt i1, VInt i2 -> VBool (i1 <= i2)
      | _ -> failwith "ELessThanEquals eval fail"
    end
  | EGreaterThan (e1, e2) ->
    begin match eval env e1, eval env e2 with
      | VInt i1, VInt i2 -> VBool (i1 > i2)
      | _ -> failwith "EGreaterThan eval fail"
    end
  | EGreaterThanEquals (e1, e2) ->
    begin match eval env e1, eval env e2 with
      | VInt i1, VInt i2 -> VBool (i1 >= i2)
      | _ -> failwith "EGreaterThanEquals eval fail"
    end
  | EListLen e ->
    begin match eval env e with
      | VList l -> VInt (List.length l)
      | _ -> failwith "Can't get length of non-list data structure"
    end
  | EListAccess (ls, idx) ->
    begin match eval env ls with
      | VList l -> 
        begin match l with 
          | [] -> failwith "EListAccess eval fail on empty list"
          | _ ->
            if List.length l <= idx || idx < 0 then 
              failwith "idx out of range"
            else
              List.nth l idx
        end
      | _ -> failwith "Can't index into something that isn't a list"
    end

let rec eval_lhs (env : record_env) (lhs : lhs) : lvalue =
  match lhs with
  | LVar var -> LVVar var
  | LAccess (lhs, exp) ->
    begin match eval_lhs env lhs with
      | LVVar var ->
        begin match load var env with
          | VMap map -> LVAccess (eval env exp, map)
          | _ -> failwith "LVVar eval_lhs fail"
        end
      | LVAccess (key, table) ->
        begin match Hashtbl.find table key with
          | VMap map -> LVAccess (eval env exp, map)
          | _ -> failwith "LVAccess eval_lhs fail"
        end
      | LVTuple _ -> failwith "Stop accessing maps with tuples"
    end
  | LTuple strs -> LVTuple strs

let store (lhs : lhs) (vl : value) (env : record_env) : unit =
  match eval_lhs env lhs with
  | LVVar var -> 
    if Env.mem env.local_env var then
      Env.replace env.local_env var vl
    else
      Env.replace env.node_env var vl
  | LVAccess (key, table) ->
    Hashtbl.replace table key vl
  | LVTuple _ -> failwith "how to store LVTuples?"

exception Halt

let copy (lhs : lhs) (vl : value) (env : record_env) : unit =
  match eval_lhs env lhs with 
  | LVVar var ->
    begin match vl with
      | VMap m -> 
        let temp = Hashtbl.copy m in
        Env.replace env.local_env var (VMap temp)
      | VList l ->
        let temp = List.map (fun x -> x) l in
        Env.replace env.local_env var (VList temp)
      | _ -> failwith "no copying non-collections"
    end
  | _ -> failwith "copying only to local_copy"

let function_info name program = Env.find program.rpc name

(* Execute record until pause/return.  Invariant: record does *not* belong to
   state.records *)
let exec (state : state) (program : program) (record : record)  =
  let env =
    { local_env = record.env; node_env = state.nodes.(record.node) }
  in
  let rec loop () =
    match CFG.label program.cfg record.pc with
    | Instr (instr, next) -> 
      record.pc <- next;
      begin match instr with
        | Async (lhs, node, func, actuals) -> 
          begin match eval env node with
            | VNode node_id ->
              Printf.printf "executing async to from node %d to node %d %s \n" record.node node_id func;
              let new_future = ref None in
              let { entry; formals; _ } = function_info func program in
              let new_env = Env.create 91 in
              List.iter2 (fun (formal, _) actual ->
                  Env.add new_env formal (eval env actual)) formals actuals;
              let new_record =
                { node = node_id
                ; pc = entry
                ; continuation = (fun value -> new_future := Some value)
                ; env = new_env
                ; id = record.id
                ; x = record.x
                ; f = record.f }
              in
              store lhs (VFuture new_future) env
            ; state.records <- new_record::state.records
            | VBool _ -> failwith "Type error bool"
            | VInt _ -> failwith "Type error int"
            | VMap _ -> failwith "Type error map"
            | VList _ -> failwith "Type error list"
            | VOption _ -> failwith "Type error option"
            | VFuture _ -> failwith "Type error future"
            | VString role -> 
              begin match load role env with 
                | VNode node_id ->
                  let new_future = ref None in
                  let { entry; formals; _ } = function_info func program in
                  let new_env = Env.create 91 in
                  List.iter2 (fun (formal, _) actual ->
                      Env.add new_env formal (eval env actual))
                    formals
                    actuals;
                  let new_record =
                    { node = node_id
                    ; pc = entry
                    ; continuation = (fun value -> new_future := Some value)
                    ; env = new_env 
                    ; id = record.id
                    ; x = record.x
                    ; f = record.f }
                  in
                  store lhs (VFuture new_future) env
                ; state.records <- new_record::state.records
                | _ -> failwith "Type error idk what you are anymore"
              end
          end
        | Assign (lhs, rhs) -> 
          store lhs (eval env rhs) env;
        | Copy (lhs, rhs) -> copy lhs (eval env rhs) env;
      end;
      loop ()
    | Cond (cond, bthen, belse) -> 
      begin match eval env cond with
        | VBool true ->
          record.pc <- bthen
        | VBool false ->
          record.pc <- belse
        | _ -> failwith "Type error!"
      end;
      loop ()
    | Await (lhs, expr, next) -> 
      begin match eval env expr with
        | VFuture fut -> 
          begin match !fut with
            | Some value -> 
              record.pc <- next;
              store lhs value env;
              loop ()
            | None -> 
              (* Still waiting.  TODO: should keep blocked records in a
                 different data structure to avoid scheduling records that
                 can't do any work. *)
              state.records <- record::state.records
          end
        | VBool b -> 
          if b then 
            begin
              record.pc <- next; 
              loop()
            end
          else 
            state.records <- record::state.records
        | _ -> failwith "Type error!"
      end
    | Return expr -> 
      record.continuation (eval env expr)
    | Pause next -> 
      record.pc <- next;
      state.records <- record::state.records
    | ForLoopIn (lhs, expr, body, next) -> 
      begin match eval env expr with
        | VMap map -> 
          (* First remove the pair being processed from the map. *)
          if (Hashtbl.length map) == 0 then 
            begin
              record.pc <- next;
              loop()
            end
          else
            let single_pair = 
              let result_ref = ref None in Hashtbl.iter (fun key value ->
                  match !result_ref with
                    Some _ -> ()  (* We already found a pair, so do nothing *)
                  | None -> result_ref := Some (key, value)
                ) map;
              !result_ref in
            Hashtbl.remove map (fst (Option.get single_pair));
            store (LVar "local_copy") (VMap map) env;
            begin match lhs with
              | LTuple [key; value] -> 
                let (k, v) = Option.get single_pair in
                Env.add env.node_env key k;
                Env.add env.node_env value v;
                record.pc <- body;
                loop () 
              | _ -> failwith "Cannot iterate through map with anything other than a 2-tuple"
            end
        | _ -> failwith "Type error!"
      end
  in
  loop ()

let schedule_record (state : state) (program : program) 
    (randomly_drop_msgs: bool) 
    (cut_tail_from_mid : bool)
    (sever_all_but_mid : bool)
    (partition_away_nodes : int list)
    (randomly_delay_msgs : bool)
  : unit =
  begin
    if false then
      Printf.printf "%b %b %b %b\n" randomly_drop_msgs cut_tail_from_mid sever_all_but_mid (List.length partition_away_nodes = 0);
  end;
  let rec pick n before after =
    match after with
    | [] ->  raise Halt
    | (r::rs) -> 
      if n == 0 then begin
        let env =
          { local_env = r.env; node_env = state.nodes.(r.node) } in
        state.records <- List.rev_append before rs;
        begin 
          match CFG.label program.cfg r.pc with
          | Instr (i,_) ->
            begin match i with 
              | Async (_, node, f, _) -> 
                let node_id = match eval env node with 
                  | VNode n_id -> n_id
                  | _ -> failwith "Type error!" in
                let src_node = r.node in
                let dest_node = node_id in
                let should_execute = ref true in
                begin
                  if randomly_drop_msgs && (Random.self_init(); Random.float 1.0 < 0.3) then
                    begin
                      Printf.printf "drop msg to node %d\n" node_id;
                      should_execute := false
                    end
                end;
                begin
                  if cut_tail_from_mid && (
                      (src_node = 2 && dest_node = 1) || (dest_node = 2 && src_node = 1)) then
                    begin
                      Printf.printf "sever msgs from node %d to %d\n" src_node dest_node;
                      should_execute := false
                    end
                end;
                begin
                  if Printf.printf "should sever all but mid? %b\n" sever_all_but_mid; sever_all_but_mid then
                    begin
                      if dest_node = 2 && not (src_node = 1) then
                        begin
                          Printf.printf "sever all msgs to tail except from mid. srcnode %d destnode %d %s\n" src_node dest_node f;
                          should_execute := false
                        end
                      else if src_node = 2 && not (dest_node = 1) then
                        begin
                          Printf.printf "sever all msgs from tail except from mid. srcnode %d destnode %d %s\n" src_node dest_node f;
                          should_execute := false
                        end
                    end
                end;
                begin
                  if List.mem src_node partition_away_nodes || 
                     List.mem dest_node partition_away_nodes then
                    begin
                      Printf.printf "partition away msgs from node %d to %d func %s\n" 
                        src_node dest_node f;
                      should_execute := false
                    end
                end;
                begin
                  if Printf.printf "randomly delay msgs %b\n" randomly_delay_msgs; randomly_delay_msgs then
                    begin
                      if Random.self_init(); Random.float 1.0 < r.x then
                        begin
                          r.x <- r.f r.x;
                          should_execute := false
                        end 
                    end
                end;
                begin
                  if !should_execute then
                    exec state program r
                end
              | _ -> exec state program r
            end
          | _ -> exec state program r
        end
      end else
        pick (n-1) (r::before) rs
  in
  let idx = (Random.self_init(); Random.int (List.length state.records)) in
  (* let chosen_record = List.nth state.records idx in *)
  (* let vert = chosen_record.pc in  *)
  let chosen_idx = idx
  (* match (CFG.label program.cfg vert) with *)
  (* | Pause _ *)
  (* | Await (_, _, _) -> if (List.length state.records) == 1 then 0 else idx *)
  (* | _ -> idx *)
  in
  pick chosen_idx [] state.records

(* Choose a client without a pending operation, create a new activation record
   to execute it, and append the invocation to the history *)
let schedule_client (state : state) (program : program) (func_name : string) (actuals : value list) (unique_id : int): unit =
  let rec pick n before after =
    match after with
    | [] -> raise Halt 
    | (c::cs) ->
      if n == 0 then begin
        let op = Env.find program.client_ops func_name
        in
        let env = Env.create 91 in
        List.iter2 (fun (formal, _) actual ->
            Env.add env formal actual
          ) op.formals actuals;
        let invocation =
          { client_id = c
          ; op_action = op.name
          ; kind = Invocation
          ; payload = actuals
          ; unique_id = unique_id }
        in
        let continuation value =
          (* After completing the operation, add response to the history and
             allow client to be scheduled again. *)
          let response =
            { client_id = c
            ; op_action = op.name
            ; kind = Response
            ; payload = [value]
            ; unique_id = unique_id }
          in
          DA.add state.history response;
          state.free_clients <- c::state.free_clients
        in
        let record =
          { pc = op.entry
          ; node = c
          ; continuation = continuation
          ; env = env 
          ; id = unique_id
          ; x = 0.4
          ; f = (fun x -> x /. 2.0) }
        in
        state.free_clients <- List.rev_append before cs;
        DA.add state.history invocation;
        state.records <- record::state.records
      end else
        pick (n-1) (c::before) cs
  in
  pick (Random.self_init(); Random.int (List.length state.free_clients)) [] state.free_clients


let schedule_sys_thread (state : state) (program : program) (func_name : string) (actuals : value list) (unique_id : int): unit =
  let rec pick n before after =
    match after with
    | [] -> raise Halt 
    | (c::cs) ->
      if n == 0 then begin
        let op = Env.find program.client_ops func_name
        in
        let env = Env.create 91 in
        List.iter2 (fun (formal, _) actual ->
            Env.add env formal actual
          ) op.formals actuals;
        let invocation =
          { client_id = c
          ; op_action = op.name
          ; kind = Invocation
          ; payload = actuals
          ; unique_id = unique_id }
        in
        let continuation value =
          (* After completing the operation, add response to the history and
             allow client to be scheduled again. *)
          let response =
            { client_id = c
            ; op_action = op.name
            ; kind = Response
            ; payload = [value]
            ; unique_id = unique_id }
          in
          DA.add state.history response;
          state.free_sys_threads <- c::state.free_sys_threads
        in
        let record =
          { pc = op.entry
          ; node = c
          ; continuation = continuation
          ; env = env 
          ; id = unique_id
          ; x = 0.4
          ; f = (fun x -> x /. 2.0) }
        in
        state.free_sys_threads <- List.rev_append before cs;
        DA.add state.history invocation;
        state.records <- record::state.records
      end else
        pick (n-1) (c::before) cs
  in
  pick (Random.self_init(); Random.int (List.length state.free_sys_threads)) [] state.free_sys_threads
