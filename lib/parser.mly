%{
  open Core
  open Ast
%}

%token <string> ID
%token <bool> TRUE FALSE
%token <int> INT
%token AND
%token APPEND
%token ARROW
%token AWAIT
%token BANG
%token CLIENT_INTERFACE
%token COLON
%token COMMA
%token EQUALS
%token EQUALS_EQUALS
%token CONTAINS
%token FOR
%token FUNC
%token IF ELSEIF ELSE
%token IN
%token LEFT_ANGLE_BRACKET RIGHT_ANGLE_BRACKET
%token LEFT_CURLY_BRACE RIGHT_CURLY_BRACE 
%token LEFT_PAREN RIGHT_PAREN 
%token LEFT_SQUARE_BRACKET RIGHT_SQUARE_BRACKET
%token LEN
%token MAP
%token MINUS
%token NOT_EQUALS
%token OR
%token PLUS
%token RETURN
%token RPC_ASYNC_CALL
%token RPC_CALL
%token SEMICOLON
%token QUOTE
%token EOF

%left BANG
%left AND
%left OR
%nonassoc EQUALS_EQUALS NOT_EQUALS
// %left COMMA

%type <Ast.prog> program

%start program

%%

program:
  | r = role_def c = client_def EOF
    { Prog(r, c) }
  // | r = role_def p = program
  //   { match p with
  //     | Prog(roles, client) -> Prog(r::roles, client)}

  
func_call: 
  | name = ID LEFT_PAREN RIGHT_PAREN 
    { FuncCall(name, []) }
  | name = ID LEFT_PAREN params = params RIGHT_PAREN 
    { FuncCall(name, params) }

func_def: FUNC func_call = func_call ARROW retval = type_def LEFT_CURLY_BRACE 
          body = statements
          RIGHT_CURLY_BRACE
  { 
    FuncDef(func_call, retval, body)
  }

func_defs:
  | { [] }
  | f = func_def fs = func_defs
    { f :: fs }

statements:
  | s = statement 
    { s :: [] }
  | s = statement ss = statements
    { s :: ss }

if_stmt:
  | IF LEFT_PAREN cond = right_side RIGHT_PAREN LEFT_CURLY_BRACE 
    body = statements
    RIGHT_CURLY_BRACE
    { IfElseIf (cond, body) }

elseif_stmts:
  | ELSEIF LEFT_PAREN cond = right_side RIGHT_PAREN LEFT_CURLY_BRACE 
    body = statements
    RIGHT_CURLY_BRACE
    { IfElseIf(cond, body) :: []}
  | ELSEIF LEFT_PAREN cond = right_side RIGHT_PAREN LEFT_CURLY_BRACE 
    body = statements
    RIGHT_CURLY_BRACE el = elseif_stmts
    { IfElseIf(cond, body) :: el}

cond_stmts:
  | i = if_stmt
    { i :: []}
  | i = if_stmt el = elseif_stmts
    { i :: el }
  | i = if_stmt ELSE LEFT_CURLY_BRACE
    else_body = statements
    RIGHT_CURLY_BRACE
    { i :: [IfElseIf(BoolRHS(Bool(true)), else_body)] }
  | i = if_stmt el = elseif_stmts ELSE LEFT_CURLY_BRACE
    else_body = statements
    RIGHT_CURLY_BRACE
    { i :: el @ [IfElseIf(BoolRHS(Bool(true)), else_body)] }

rpc_call:
  | RPC_CALL LEFT_PAREN host = ID COMMA func_call = func_call RIGHT_PAREN
    { RpcCall(host, func_call) }
  | RPC_CALL LEFT_PAREN QUOTE host = ID QUOTE COMMA func_call = func_call RIGHT_PAREN
    { RpcCall(host, func_call) }
  | RPC_ASYNC_CALL LEFT_PAREN host = ID COMMA func_call = func_call RIGHT_PAREN
    { RpcAsyncCall(host, func_call) }
  | RPC_ASYNC_CALL LEFT_PAREN QUOTE host = ID QUOTE COMMA func_call = func_call RIGHT_PAREN
    { RpcAsyncCall(host, func_call) }

type_def:
  | id = ID
    { CustomType(id) }
  | MAP LEFT_ANGLE_BRACKET key = type_def COMMA value = type_def RIGHT_ANGLE_BRACKET
    { MapType(key, value) }

kv_pairs:
  | key = ID COLON value = right_side
    { (key, value) :: []}
  | key = ID COLON value = right_side COMMA kvs = kv_pairs
    { (key, value)::kvs }

items:
  | rhs = right_side
    { rhs :: [] }
  | rhs = right_side COMMA rest = items
    { rhs :: rest }

collection_literal:
  | LEFT_CURLY_BRACE RIGHT_CURLY_BRACE
    { MapLit([]) }
  | LEFT_CURLY_BRACE kvs = kv_pairs RIGHT_CURLY_BRACE
    { MapLit(kvs) }
  | LEFT_SQUARE_BRACKET RIGHT_SQUARE_BRACKET
    { ListLit([]) }
  | LEFT_SQUARE_BRACKET items = items RIGHT_SQUARE_BRACKET
    { ListLit(items) }
  
string:
  | QUOTE QUOTE
    { String("") }
  | QUOTE s = ID QUOTE
    { String(s) }

int:
| i = INT
  { Int(i) }
| i1 = right_side PLUS i2 = right_side
  { PlusInt(i1, i2)}
| i1 = right_side MINUS i2 = right_side
  { MinusInt(i1, i2)}

var_init:
  | typ = type_def id = ID EQUALS right_side = right_side
    { VarInit(typ, id, right_side) }

var_inits:
  | v = var_init SEMICOLON
    {v :: []}
  | v = var_init SEMICOLON vs = var_inits
    {v :: vs}

l_items:
  | id1 = ID COMMA id2 = ID
    { [id1; id2] }
  | id = ID COMMA rest = l_items
    { id::rest }

collection_access:
  | name = ID LEFT_SQUARE_BRACKET key = right_side RIGHT_SQUARE_BRACKET
    { MapAccess(name, key) }
  | name = collection_access LEFT_SQUARE_BRACKET key = right_side RIGHT_SQUARE_BRACKET
    { MapAccess(name, key) }

left_side:
  | id = ID
    { VarLHS(id) }
  | access = collection_access
    { CollectionAccessLHS(access) }
    // { MapAccessLHS(mapName, key) }
  | l_items = l_items
    { TupleLHS(l_items) }


boolean:
  | TRUE 
    { Bool true }
  | FALSE
    { Bool false }
  | BANG rhs = right_side
    { Not rhs }
  | b1 = right_side AND b2 = right_side
    { And (b1, b2) }
  | b1 = right_side OR b2 = right_side
    { Or (b1, b2) }
  | rhs1 = right_side EQUALS_EQUALS rhs2 = right_side
    { EqualsEquals (rhs1, rhs2)}
  | rhs1 = right_side NOT_EQUALS rhs2 = right_side
    { NotEquals (rhs1, rhs2)}
  | LEFT_PAREN b = boolean RIGHT_PAREN
    { b }
  | CONTAINS LEFT_PAREN map = right_side COMMA key = right_side RIGHT_PAREN
    { Contains(map, key) }

right_side:
  | id = ID
    { VarRHS(id) }
  | mapAccess = collection_access
    { CollectionAccessRHS(mapAccess) }
    // { ListAccessRHS(list, idx) }
  | func_call = func_call
    { FuncCallRHS(func_call)}
  | s = string
    { StringRHS s}
  | i = int
    { IntRHS i }
  | b = boolean
    { BoolRHS b }
  | c = collection_literal
    { CollectionRHS c }
  | rpc_call = rpc_call
    { RpcCallRHS rpc_call }
  | APPEND LEFT_PAREN list = right_side COMMA item = right_side RIGHT_PAREN
    { Append(list, item) }
  | LEN LEFT_PAREN list = right_side RIGHT_PAREN
    { Len(list) }

statement:
  | cond_stmts = cond_stmts
    { CondList(cond_stmts)}
  | left = left_side EQUALS right = right_side SEMICOLON
    { Assignment(left, right)}
  | r = right_side SEMICOLON
    { Expr(r) }
  | RETURN r = right_side SEMICOLON
    { Return(r) }
  | FOR LEFT_PAREN idx = left_side IN collection = right_side RIGHT_PAREN LEFT_CURLY_BRACE
    body = statements
    RIGHT_CURLY_BRACE
    { ForLoopIn(idx, collection, body) }
  | AWAIT r = right_side SEMICOLON
    { Await(r) }

params:
  | rhs = right_side
    { Param(rhs) :: []}
  | rhs = right_side COMMA ps = params
    { Param(rhs) :: ps }

role_def:
  | id = ID LEFT_CURLY_BRACE
    var_inits = var_inits
    func_defs = func_defs
    RIGHT_CURLY_BRACE
    { RoleDef(id, [], var_inits, func_defs) }

client_def:
  | CLIENT_INTERFACE LEFT_CURLY_BRACE
    func_defs = func_defs
    RIGHT_CURLY_BRACE
    { ClientDef(func_defs) }
