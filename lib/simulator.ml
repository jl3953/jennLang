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
  | EFind of string * expr
  | EInt of int
  | EBool of bool
  | EMap
  | EString of string
[@@deriving ord]

type lhs =
  | LVar of string
  | LAccess of lhs * expr
[@@deriving ord]

type instr =
  | Assign of lhs * expr (* jenndbg probably assigning map values? *)
  | Async of lhs * expr * string * (expr list) (* jenndbg RPC*) 
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
  | VOption of (value option)
  | VFuture of (value option) ref
  | VNode of int
  | VString of string

(* Run-time value of a left-hand-side *)
type lvalue =
  | LVVar of string
  | LVAccess of (value * (value, value) Hashtbl.t)

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
  ; env : value Env.t }

type op_kind = Invocation | Response

type operation =
  { client_id : int
  ; op_action : string
  ; kind : op_kind
  ; payload : value list }

(* Global state *)
type state =
  { nodes : (value Env.t) array
  ; mutable records : record list
  ; history : operation DA.t
  ; mutable free_clients : int list (* client ids should be valid indexes into nodes *)
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
    let v = Env.find env.local_env var in 
    (* let _ = print_endline ("Found local " ^ var) in *)
    v
  end
  with Not_found -> begin 
    let v = Env.find env.node_env var in
    (* let _ = print_endline ("Found node " ^ var) in  *)
    v
  end

(* Evaluate an expression in the context of an environment. *)
let rec eval (env : record_env) (expr : expr) : value =
  match expr with
  | EInt i -> VInt i
  | EBool b -> VBool b
  | EVar v -> load v env
  | EFind (m, k) ->
    begin match load m env with
      | VMap map -> Hashtbl.find map (eval env k)
      | _ -> failwith "Type error!"
    end
  | EMap -> 
    (* print_endline "EMap"; *)
    let map = Hashtbl.create 91 in
    VMap map
  | EString s -> 
    (* print_endline ("VString " ^ s);  *)
    VString s

let rec eval_lhs (env : record_env) (lhs : lhs) : lvalue =
  match lhs with
  | LVar var -> LVVar var
  | LAccess (lhs, exp) ->
    begin match eval_lhs env lhs with
      | LVVar var ->
        begin match load var env with
          | VMap map -> LVAccess (eval env exp, map)
          | _ -> failwith "Type error!"
        end
      | LVAccess (key, table) ->
        begin match Hashtbl.find table key with
          | VMap map -> LVAccess (eval env exp, map)
          | _ -> failwith "Type error!"
        end
    end

let store (lhs : lhs) (vl : value) (env : record_env) : unit =
  match eval_lhs env lhs with
  | LVVar var -> 
    if Env.mem env.local_env var then begin
      (* print_endline ("Replacing local " ^ var); *)
      Env.replace env.local_env var vl
    end
    else
      begin
        (* print_endline ("Replacing node " ^ var); *)
        Env.replace env.node_env var vl
      end
  | LVAccess (key, table) ->
    Hashtbl.add table key vl

exception Halt

let function_info name program = 
  (* print_endline ("rpc name: " ^ name);  *)
  Env.find program.rpc name

(* Execute record until pause/return.  Invariant: record does *not* belong to
   state.records *)
let exec (state : state) (program : program) (record : record) =
  let env =
    { local_env = record.env; node_env = state.nodes.(record.node) }
  in
  let rec loop () =
    match CFG.label program.cfg record.pc with
    | Instr (instr, next) -> 
      print_endline "Instr";
      record.pc <- next;
      begin match instr with
        | Async (lhs, node, func, actuals) -> 
          let roleName = match node with 
          | EVar v -> v
          | EString s -> s
          | _ -> failwith "Type error!" in
          let () = print_endline ("\tAsync " ^ roleName) in 
          (* let node = 
            begin match (eval env nodeVar) with
            | VString s -> s
            | VBool _ -> failwith "Type error bool"
            | VInt _ -> failwith "Type error int"
            | VMap _ -> failwith "Type error map"
            | VOption _ -> failwith "Type error option"
            | VFuture _ -> failwith "Type error future"
            | VNode _ -> failwith "Type error node"
            end in *)
          (* print_endline ("\tAsync node " ^ node); *)
          begin match eval env node with
            | VNode node_id ->
              let new_future = ref None in
              let { entry; formals; _ } = function_info (func ^ "_" ^ roleName) program in
              let new_env = Env.create 91 in
              List.iter2 (fun (formal, _) actual ->
                  Env.add new_env formal (eval env actual))
                formals
                actuals;
              let new_record =
                { node = node_id
                ; pc = entry
                ; continuation = (fun value -> new_future := Some value)
                ; env = new_env }
              in
              store lhs (VFuture new_future) env
              ; state.records <- new_record::state.records
            | VBool _ -> failwith "Type error bool"
            | VInt _ -> failwith "Type error int"
            | VMap _ -> failwith "Type error map"
            | VOption _ -> failwith "Type error option"
            | VFuture _ -> failwith "Type error future"
            | VString role -> 
              begin match load role env with 
              | VNode node_id ->
                let new_future = ref None in
                let { entry; formals; _ } = function_info (func ^ "_" ^ role) program in
                let new_env = Env.create 91 in
                List.iter2 (fun (formal, _) actual ->
                    Env.add new_env formal (eval env actual))
                  formals
                  actuals;
                let new_record =
                  { node = node_id
                  ; pc = entry
                  ; continuation = (fun value -> new_future := Some value)
                  ; env = new_env }
                in
                store lhs (VFuture new_future) env
                ; state.records <- new_record::state.records
              | _ -> failwith "Type error!"
              end
          end
        | Assign (lhs, rhs) -> 
          print_endline ("\tAssign executing on node " ^ string_of_int record.node);
          store lhs (eval env rhs) env
      end;
      loop ()
    | Cond (cond, bthen, belse) -> 
      (* print_endline "Cond"; *)
      begin match eval env cond with
        | VBool true ->
          record.pc <- bthen
        | VBool false ->
          record.pc <- belse
        | _ -> failwith "Type error!"
      end;
      loop ()
    | Await (lhs, expr, next) -> 
      print_endline "Await"; 
      (* begin match expr with 
      | EVar v -> print_endline ("EVar " ^ v)
      | EInt i -> print_endline ("EInt " ^ string_of_int i)
      | EBool b -> print_endline ("EBool " ^ string_of_bool b)
      | EFind (_, _) -> print_endline "EFind"
      | EMap -> print_endline "EMap"
      | EString s -> print_endline ("EString " ^ s)
      end;  *)
      begin match eval env expr with
        | VFuture fut -> 
          print_endline "\tVFuture";
          begin match !fut with
            | Some value -> 
              print_endline "\t\tSome";
              record.pc <- next;
              store lhs value env;
              loop ()
            | None -> 
              print_endline "\t\tNone";
              (* Still waiting.  TODO: should keep blocked records in a
                 different data structure to avoid scheduling records that
                 can't do any work. *)
              state.records <- record::state.records
          end
        | _ -> failwith "Type error!"
      end
    | Return expr -> 
      print_endline "Return";
      (* begin match expr with
      | EVar v -> print_endline ("\tEVar " ^ v)
      | EInt i -> print_endline ("\tEInt " ^ string_of_int i)
      | EBool b -> print_endline ("\tEBool " ^ string_of_bool b)
      | EFind (m, k) -> 
        begin match k with
        | EVar v -> print_endline ("\tEFind " ^ m ^ ", " ^ v)
        | EInt i -> print_endline ("\tEFind " ^ m ^ ", " ^ string_of_int i)
        | EBool b -> print_endline ("\tEFind " ^ m ^ ", " ^ string_of_bool b)
        | EMap -> print_endline ("\tEFind " ^ m ^ ", EMap")
        | EFind (_, _) -> print_endline ("\tEFind " ^ m ^ ", EFind ")
        | EString s -> print_endline ("\tEString " ^ s)
        end
      | EMap -> print_endline ("\tEMap");
      | EString s -> print_endline ("\tEString " ^ s)
      end; *)
      record.continuation (eval env expr)
    (*| Read -> print_endline "Read";
      let expr = match Env.find record.env "key" with
        | VString s -> EVar s
        | _ -> failwith "Type error!" in 
      record.continuation(eval env expr)*)
    | Pause next -> 
      (* print_endline "Pause"; *)
      record.pc <- next;
      state.records <- record::state.records

  in
  loop ()

let schedule_record (state : state) (program : program): unit =
  print_int (List.length state.records);
  print_endline " scheduling records left";
  let rec pick n before after =
    match after with
    | [] -> print_endline "Halt"; raise Halt
    | (r::rs) -> 
      if n == 0 then begin
        state.records <- List.rev_append before rs;
        exec state program r
      end else
        pick (n-1) (r::before) rs
  in
  (* let rando = Random.int (List.length state.records) in *)
  let head = List.hd state.records in
  let vert = head.pc in 
  let rando = 
    match (CFG.label program.cfg vert) with
    | Instr (_, _) -> 0
    | Pause _ -> 
      begin match (List.length state.records) with
      | 1 -> 0
      |__ -> 1
      end
    | Await (_, _, _) -> 
      begin match (List.length state.records) with
      | 1 -> 0
      |__ -> 1
      end
    | Return _ -> 0
    | Cond (_, _, _) -> 0
  in
  print_int rando;
  print_endline "";
  pick rando [] state.records
  (* pick 0 [] state.records *)

(* Choose a client without a pending operation, create a new activation record
   to execute it, and append the invocation to the history *)
let schedule_client (state : state) (program : program) (func_name : string) (actuals : value list): unit =
  let rec pick n before after =
    match after with
    | [] -> raise Halt 
    | (c::cs) ->
      if n == 0 then begin
        let op =
          Env.find program.client_ops func_name
          (* List.nth program.client_ops (Random.int (List.length program.client_ops)) *)
        in
        let env = Env.create 91 in
          List.iter2 (fun (formal, _) actual ->
              Env.add env formal actual
          ) op.formals actuals;
        (* let params =
          List.map (fun (formal, _) ->
              (* TODO: generate random parameters *)
              let value = (VInt 0) in
              Env.add env formal value;
              value)
            op.formals *)
        let invocation =
          { client_id = c
          ; op_action = op.name
          ; kind = Invocation
          ; payload = actuals }
        in
        let continuation value =
          (* After completing the operation, add response to the history and
             allow client to be scheduled again. *)
          let response =
            { client_id = c
            ; op_action = op.name
            ; kind = Response
            ; payload = [value] }
          in
          DA.add state.history response;
          state.free_clients <- c::state.free_clients
        in
        let record =
          { pc = op.entry
          ; node = c
          ; continuation = continuation
          ; env = env }
        in
        state.free_clients <- List.rev_append before cs;
        DA.add state.history invocation;
        state.records <- record::state.records
      end else
        pick (n-1) (c::before) cs
  in
  pick (Random.int (List.length state.free_clients)) [] state.free_clients
