(* open Core *)

type option = Option of string

type type_def =
  | CustomType of string
  | MapType of type_def * type_def
(* 
type lhs =
  | VarLHS of string
  | MapAccessLHS of string * string *)

type boolean =
| Bool of bool
| Not of rhs
| And of boolean * boolean
| Or of boolean * boolean
| EqualsEquals of rhs * rhs
| NotEquals of rhs * rhs

(* type rhs = *)
and rhs = 
  | VarRHS of string
  | MapAccessRHS of string * string
  | FuncCallRHS of func_call
  | Literal of literal 
  | FieldAccessRHS of rhs * string
  | Map of (string * rhs) list
  | List of rhs list
  | BoolRHS of boolean
  | CollectionRHS of collection_literal

and collection_literal = 
  | MapLit of (string * rhs) list
  | ListLit of rhs list

and param = Param of rhs 

and literal = 
  | Options of option list
  | String of string
  | Int of int

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

type iterator = 
  | Iterator of string * string

(* list of condition to be evaluated * statement body, else condition is just true*)
type cond_stmt = IfElseIf of boolean * statement list 

and statement =
  | CondList of cond_stmt list 
  | Expr of expr
  | Return of expr
  | ForLoop of iterator * rhs * statement list
  | Comment

type func_def = FuncDef of func_call * type_def * statement list

type var_init = VarInit of type_def * string * rhs

type role_def = RoleDef of string * param list * var_init list * func_def list

type client_def = ClientDef of func_def list

type prog = Prog of role_def list * client_def