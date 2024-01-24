(* open Core *)

type option = Option of string

type type_def =
  | CustomType of string
  | MapType of type_def * type_def
(* 
type lhs =
  | VarLHS of string
  | MapAccessLHS of string * string *)

(* type rhs = *)
type rhs = 
  | Bool of bool
  | VarRHS of string
  | MapAccessRHS of string * string
  | FuncCallRHS of func_call
  | DefValRHS of default_value
  | FieldAccessRHS of rhs * string

and param = Param of rhs 

and default_value =
  (* | Map of (default_value * default_value) list *)
  | Options of option list
  | EmptyMap

and func_call = FuncCall of string * param list

and rpc_call = RpcCall of string * func_call

and lhs = 
  | VarLHS of string
  | MapAccessLHS of string * string
  | FieldAccessLHS of rhs * string

and expr =
  | Assignment of lhs * expr
  | RHS of rhs 
  | RpcCallRHS of rpc_call


type cond_stmt = IfElseIf of rhs * statement list 

and statement =
  | CondList of cond_stmt list 
  | Expr of expr
  | Return of expr

type func_def = FuncDef of func_call * type_def * statement list

type var_init = VarInit of type_def * string * default_value

type role_def = RoleDef of string * param list * var_init list * func_def list

type client_def = ClientDef of func_def list

type prog = Prog of role_def list * client_def