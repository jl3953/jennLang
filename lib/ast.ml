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
| And of rhs * rhs
| Or of rhs * rhs
| EqualsEquals of rhs * rhs
| NotEquals of rhs * rhs

and rhs = 
  | VarRHS of string
  | MapAccessRHS of string * string
  | FuncCallRHS of func_call
  | LiteralRHS of literal 
  | FieldAccessRHS of rhs * string
  | BoolRHS of boolean
  | CollectionRHS of collection
  | RpcCallRHS of rpc_call
  | Head of rhs
  | Tail of rhs
  | Len of rhs

and collection = 
  | MapLit of (string * rhs) list
  | ListLit of rhs list
  | ListPrepend of rhs * rhs
  | ListAppend of rhs * rhs

and param = Param of rhs 

and literal = 
  | Options of option list
  | String of string
  | Int of int

and func_call = FuncCall of string * param list

and rpc_call = 
  | RpcCall of string * func_call
  | RpcAsyncCall of string * func_call

and lhs = 
  | VarLHS of string
  | MapAccessLHS of string * string
  | FieldAccessLHS of rhs * string
  | TupleLHS of string list

(* list of condition to be evaluated * statement body, else condition is just true*)
type cond_stmt = IfElseIf of rhs * statement list 

and statement =
  | CondList of cond_stmt list 
  | Assignment of lhs * rhs
  | Expr of rhs
  | Return of rhs
  | ForLoopIn of lhs * rhs * statement list
  | Comment
  | Await of rhs

type func_def = FuncDef of func_call * type_def * statement list

type var_init = VarInit of type_def * string * rhs

type role_def = RoleDef of string * param list * var_init list * func_def list

type client_def = ClientDef of func_def list

type prog = Prog of role_def * client_def