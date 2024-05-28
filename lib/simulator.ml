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


type 'a mutable_list = 
{ mutable head : 'a option
; mutable next : 'a mutable_list option }

let rec length_aux len = function
    {head = None; next = None} -> len
  | {head = Some _; next = None} -> len + 1
  | {head = Some _; next = Some n} -> length_aux (len + 1) n
  | {head = None; next = Some _ } -> failwith "length_aux head can't be None if next is Some"

let mutable_length l = length_aux 0 l

let mutable_nth m_list n =
  if n < 0 then invalid_arg "mutable_nth" 
  else let rec nth_aux l n =
    match l with
    | {head = None; next = None} -> failwith "nth"
    | {head = Some h; next = None} -> if n = 0 then h else failwith "nth"
    | {head = Some h; next = Some nx} -> if n = 0 then h else nth_aux nx (n-1)
    | {head = None; next = Some _} -> failwith "mutable_nth head can't be None if next is Some"
  in nth_aux m_list n

let append m_list value =
  let rec append_aux l value =
    match l with
    | {head = None; next = None} -> l.head <- Some value
    | {head = Some _; next = None} -> l.next <- Some {head = Some value; next = None}
    | {head = Some _; next = Some nx} -> append_aux nx value
    | {head = None; next = Some _} -> failwith "append head can't be None if next is Some"
  in append_aux m_list value

let rec mutable_mem x = function
    {head = None; next = None } -> false
  | {head = Some h; next = None } -> h = x
  | {head = Some h; next = Some nx} -> h = x || mutable_mem x nx
  | {head = None; next = Some _} -> failwith "mutable_mem head can't be None if next is Some"

let rec mutable_map f = function
    {head = None; next = None} -> {head = None; next = None}
  | {head = Some h; next = None} -> {head = Some (f h); next = None}
  | {head = Some h; next = Some nx} -> {head = Some (f h); next = Some (mutable_map f nx)}
  | {head = None; next = Some _} -> failwith "mutable_map head can't be None if next is Some"

let rec mutable_iter f = function
    {head = None; next = None} -> ()
  | {head = Some h; next = None} -> f h
  | {head = Some h; next = Some nx} -> f h; mutable_iter f nx
  | {head = None; next = Some _} -> failwith "mutable_iter head can't be None if next is Some"

type expr =
  | EVar of string
  | EFind of string * expr
  | EIdx of expr * expr
  | EInt of int
  | EPlusInt of expr * expr
  | EMinusInt of expr * expr
  | EBool of bool
  | ENot of expr
  | EAnd of expr * expr
  | EOr of expr * expr
  | EEqualsEquals of expr * expr
  | EMap of (string * expr) list
  | EList of expr list
  | EString of string
  | EContains of expr * expr
  | EAppend of expr * expr
  | ELen of expr
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
  | VList of value mutable_list
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
  ; id : int }

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

let printmaps (prefix : string) (m : (value, value) Hashtbl.t) =
  Hashtbl.iter (fun k v -> 
    begin match k with
    | VInt i -> print_string (prefix ^ "key " ^ string_of_int i ^ "->")
    | VString s -> print_string (prefix ^ "key " ^ s ^ "->")
    | VBool b -> print_string (prefix ^ "key " ^ string_of_bool b ^ "->")
    | VNode n -> print_string (prefix ^ "key " ^ string_of_int n ^ "->")
    | VOption _ -> print_endline (prefix ^ "key VOption" ^ "->")
    | VFuture _ -> print_endline (prefix ^ "key VFuture" ^ "->")
    | VMap _ -> print_endline (prefix ^ "key VMap" ^ "->")
    | VList _ -> print_endline (prefix ^ "key VList" ^ "->")
    end;
    begin match v with
    | VInt i -> print_endline ("value " ^ string_of_int i)
    | VString s -> print_endline ("value " ^ s)
    | VBool b -> print_endline ("value " ^ string_of_bool b)
    | VNode n -> print_endline ("value " ^ string_of_int n)
    | VOption _ -> print_endline "value VOption"
    | VFuture _ -> print_endline "value VFuture"
    | VMap _ -> print_endline "value VMap"
    | VList _ -> print_endline "value VList"
    end
  ) m

(* Evaluate an expression in the context of an environment. *)
let rec eval (env : record_env) (expr : expr) : value =
  match expr with
  | EInt i -> VInt i
  | EPlusInt (e1, e2) ->
    begin match eval env e1, eval env e2 with
      | VInt i1, VInt i2 -> VInt (i1 + i2)
      | _ -> failwith "EPlusInt eval fail"
    end
  | EMinusInt (e1, e2) ->
    begin match eval env e1, eval env e2 with
      | VInt i1, VInt i2 -> VInt (i1 - i2)
      | _ -> failwith "EMinusInt eval fail"
    end
  | EBool b -> VBool b
  | EVar v -> load v env
  | EFind (m, k) ->
    begin match load m env with
      | VMap map -> Hashtbl.find map (eval env k)
      | _ -> failwith "EFind eval fail"
    end
  | EIdx (collection, key) ->
    begin match eval env collection with 
    | VList m_list -> print_endline ("EIdx on list " ^ string_of_int (mutable_length m_list));
      begin match eval env key with 
      | VInt idx -> print_endline ("List.nth " ^ string_of_int idx); mutable_nth m_list idx
      | VBool _ -> failwith "VBool idx"
      | VString s -> failwith ("VString idx " ^ s)
      | VFuture _ -> failwith "VFuture idx"
      | VNode _ -> failwith "VNode idx"
      | VOption _ -> failwith "VOption idx"
      | VMap _ -> failwith "VMap idx"
      | VList _ -> failwith "VList idx"
      end
    | VMap map -> print_endline ("EIdx on map " ^ string_of_int (Hashtbl.length map) ^ " keys");
      printmaps "EIdx " map;
        begin match eval env key with
        | VInt i -> print_endline ("EIdxkey on int " ^ string_of_int i)
        | VString s -> print_endline ("EIdxkey on string " ^ s)
        | VBool b -> print_endline ("EIdxkey on bool " ^ string_of_bool b)
        | VNode n -> print_endline ("EIdxkey on node " ^ string_of_int n)
        | VOption _ -> print_endline "EIdxkey on option"
        | VFuture _ -> print_endline "EIdxkey on future"
        | VMap m -> print_endline "EIdxkey on map"; printmaps "EIdxkey " m
        | VList _ -> print_endline "EIdxkey on list"
       end;
      Hashtbl.find map (eval env key)
    | VString _ -> failwith "EIdx on string"
    | VBool _ -> failwith "EIdx on bool"
    | VNode _ -> failwith "EIdx on node"
    | VOption _ -> failwith "EIdx on option"
    | VFuture _ -> failwith "EIdx on future"
    | VInt _ -> failwith "EIdx on int"
    end
    (* begin match eval env collection with
      | VList list -> print_endline "EIdx Vlist";
        begin match eval env key with 
        | VInt idx -> print_endline "VInt"; List.nth list idx
        | _ -> failwith "what the hell"
        end
      | _ -> failwith "EIdx eval fail"
    end *)
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
        Hashtbl.add tbl (VString k) (eval env v); 
        tbl
      end in 
      VMap (makemap kvpairs)
  | EList exprs ->
    let rec makelist (exprs : expr list) : value mutable_list =
      begin match exprs with
      | [] -> { head = None; next = None}
      | e :: [] -> { head = Some (eval env e); next = None}
      (* | e :: rest -> (eval env e) :: (makelist rest) *)
      | e :: rest -> { head = Some (eval env e); next = Some (makelist rest)}
      end in
      VList (makelist exprs)
  | EString s -> VString s
  | EContains (e1, e2) ->
    begin match eval env e1, eval env e2 with
      | VMap map, key -> VBool (Hashtbl.mem map key)
      | VList m_list, value -> VBool (mutable_mem value m_list)
      | _ -> failwith "EContains only operates on collections"
    end
  | EAppend (e1, e2) ->
    begin match eval env e1, eval env e2 with
      | VList m_list, value -> VList (append m_list value; m_list)
      | _ -> failwith "EAppend only operates on collections"
    end
  | ELen (e) ->
    begin match eval env e with
      | VMap map -> VInt (Hashtbl.length map)
      | VList m_list -> VInt (mutable_length m_list)
      | _ -> failwith "ELen only operates on collections"
    end

let rec eval_lhs (env : record_env) (lhs : lhs) : lvalue =
  match lhs with
  | LVar var -> LVVar var
  | LAccess (lhs, exp) ->
    begin match eval_lhs env lhs with
      | LVVar var ->
        (* print_endline ("Accessing " ^ var); *)
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
    | VList m_list ->
      let mutable_temp = mutable_map (fun x -> x) m_list in
      Env.replace env.local_env var (VList mutable_temp)
    | _ -> failwith "no copying non-collections"
    end
  | _ -> failwith "copying only to local_copy"

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
      (* print_endline "Instr"; *)
      record.pc <- next;
      begin match instr with
        | Async (lhs, node, func, actuals) -> 
          let roleName = match node with 
          | EVar v -> v
          | EString s -> s
          | _ -> failwith "Async type fail" in
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
              let { entry; formals; _ } = function_info func program in
              let new_env = Env.create 91 in
              List.iter2 (fun (formal, _) actual ->
                  print_endline ("formal: " ^ formal);
                  begin match actual with
                  | EVar v -> print_endline ("EVar " ^ v)
                  | EInt i -> print_endline ("EInt " ^ string_of_int i)
                  | EBool b -> print_endline ("EBool " ^ string_of_bool b)
                  | EFind (_, _) -> print_endline "EFind"
                  | EMap _ -> print_endline "EMap"
                  | EString s -> print_endline ("EString " ^ s)
                  | _ -> failwith "what type are you"
                  end;
                  Env.add new_env formal (eval env actual))
                formals
                actuals;
              let new_record =
                { node = node_id
                ; pc = entry
                ; continuation = (fun value -> new_future := Some value)
                ; env = new_env
                ; id = record.id}
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
                print_endline ("Find func " ^ func ^ " for node " ^ string_of_int node_id);
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
                  ; id = record.id}
                in
                store lhs (VFuture new_future) env
                ; state.records <- new_record::state.records
              | _ -> failwith "Type error idk what you are anymore"
              end
          end
        | Assign (lhs, rhs) -> 
          (*print_endline ("\tAssign executing on node " ^ string_of_int record.node); 
          begin match lhs with
          | LVar v -> print_endline ("LVar " ^ v)
          | LAccess (map, key)  ->
            begin match map with 
            | LVar map_name -> 
              begin match eval env key with
              | VString k -> print_endline ("LAccess " ^ map_name ^ "[" ^ k ^ "]")
              | VInt k -> print_endline ("LAccess " ^ map_name ^ "[" ^ string_of_int k ^ "]")
              | _ -> print_endline "What are you doing hurdur"
              end
            | _ -> print_endline "What are you doing"
            end
          | LTuple _ -> print_endline "LTuple"
          end;
          begin match (eval env rhs) with
          | VInt i -> print_endline ("\t\tVInt " ^ string_of_int i)
          | VBool b -> print_endline ("\t\tVBool " ^ string_of_bool b)
          | VMap m -> print_endline "\t\tVMap"; print_endline "jenndebug";
          Hashtbl.iter (fun k v -> 
            begin match k with
            | VInt i -> print_endline ("\t\t\t" ^ string_of_int i)
            | VBool b -> print_endline ("\t\t\t" ^ string_of_bool b)
            | VString s -> print_endline ("\t\t\t" ^ s)
            | VFuture _ -> print_endline "\t\t\tVFuture"
            | VNode n -> print_endline ("\t\t\t" ^ string_of_int n)
            | VOption _ -> print_endline "\t\t\tVOption"
            | VList _ -> print_endline "\t\t\tVList"
            | VMap _ -> print_endline "\t\t\tVMap"
            end;
            begin match v with
            | VInt i -> print_endline ("\t\t\t" ^ string_of_int i)
            | VBool b -> print_endline ("\t\t\t" ^ string_of_bool b)
            | VString s -> print_endline ("\t\t\t" ^ s)
            | VFuture _ -> print_endline "\t\t\tVFuture"
            | VNode n -> print_endline ("\t\t\t" ^ string_of_int n)
            | VOption _ -> print_endline "\t\t\tVOption"
            | VList _ -> print_endline "\t\t\tVList"
            | VMap _ -> print_endline "\t\t\tVMap"
            end
          ) m
          | VList _ -> print_endline "\t\tVList"
          | VOption _ -> print_endline "\t\tVOption"
          | VFuture _ -> print_endline "\t\tVFuture"
          | VString s -> print_endline ("\t\tVString " ^ s)
          | VNode n -> print_endline ("\t\tVNode " ^ string_of_int n)
          end;*)
          store lhs (eval env rhs) env;
        | Copy (lhs, rhs) -> copy lhs (eval env rhs) env;
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
      (* print_endline "Await"; 
      begin match expr with 
      | EVar v -> print_endline ("EVar " ^ v)
      | EInt i -> print_endline ("EInt " ^ string_of_int i)
      | EBool b -> print_endline ("EBool " ^ string_of_bool b)
      | EFind (_, _) -> print_endline "EFind"
      | EMap _ -> print_endline "EMap"
      | EString s -> print_endline ("EString " ^ s)
      | ENot _ -> print_endline "ENot"
      | EAnd _ -> print_endline "EAnd"
      | EOr _ -> print_endline "EOr"
      | EEqualsEquals _ -> print_endline "EEqualsEquals"
      | EList _ -> print_endline "EList"
      | EContains _ -> print_endline "EContains"
      | EAppend _ -> print_endline "EAppend"
      end;
      print_endline ("On node " ^ string_of_int record.node);*)
      begin match eval env expr with
        | VFuture fut -> 
          (* print_endline "\tVFuture"; *)
          begin match !fut with
            | Some value -> 
              (* print_endline "\t\tSome"; *)
              record.pc <- next;
              store lhs value env;
              loop ()
            | None -> 
              (* print_endline "\t\tNone"; *)
              (* Still waiting.  TODO: should keep blocked records in a
                 different data structure to avoid scheduling records that
                 can't do any work. *)
              state.records <- record::state.records
          end
        | VBool b -> 
          begin match b with
          | true -> 
            (* print_endline "\tVBool true"; *)
            record.pc <- next;
            loop ()
          | false -> 
            (* print_endline "\tVBool false"; *)
            state.records <- record::state.records
          end
        | _ -> failwith "Type error!"
      end
    | Return expr -> 
      (* print_endline "Return"; *)
      record.continuation (eval env expr)
    | Pause next -> 
      (* print_endline "Pause"; *)
      record.pc <- next;
      state.records <- record::state.records
    | ForLoopIn (lhs, expr, body, next) -> 
      begin match eval env expr with
      | VMap map -> 
        (* First remove the pair being processed from the map. *)
        if (Hashtbl.length map) == 0 then 
          begin
          (* print_endline "jenndebug made it here"; *)
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
          (* let new_env = 
            let create_env = Env.create 91 in
            Env.iter (fun k v ->
            Env.add create_env k v) 
            env.local_env; create_env in *)
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

let schedule_record (state : state) (program : program) (unique_id: int) : unit =
  print_int (List.length state.records);
  (* print_endline " scheduling records left"; *)
  if unique_id > 0 then
    begin
    (* print_endline ("unique_id " ^ string_of_int unique_id); *)
    let rec pick before after =
      match after with
      | [] -> print_endline "Halt"; raise Halt
      | (r::rs) -> 
        if r.id == unique_id then begin
          state.records <- List.rev_append before rs;
          exec state program r
        end else
          pick (r::before) rs
    in
    pick [] state.records
  end
  else
    begin
    (* print_endline "no unique_id"; *)
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
      | Pause _ -> if (List.length state.records) == 1 then 0 else 1
      | Await (_, _, _) -> if (List.length state.records) == 1 then 0 else 1
      | Return _ -> 0
      | Cond (_, _, _) -> 0
      | ForLoopIn (_, _, _, _) -> 0
    in
    (* print_endline ("chosen idx " ^ string_of_int rando);
    print_endline "";*)
    pick rando [] state.records
    (* pick 0 [] state.records *)
  end

(* Choose a client without a pending operation, create a new activation record
   to execute it, and append the invocation to the history *)
let schedule_client (state : state) (program : program) (func_name : string) (actuals : value list) (unique_id : int): unit =
  let rec pick n before after =
    match after with
    | [] -> raise Halt 
    | (c::cs) ->
      if n == 0 then begin
        let op =
          (* print_endline ("func_name: " ^ func_name); *)
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
          ; id = unique_id }
        in
        state.free_clients <- List.rev_append before cs;
        DA.add state.history invocation;
        state.records <- record::state.records
      end else
        pick (n-1) (c::before) cs
  in
  pick (Random.int (List.length state.free_clients)) [] state.free_clients
