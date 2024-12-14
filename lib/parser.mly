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
(*%token DOT*)
%token EQUALS
%token EQUALS_EQUALS
%token FOR
%token FUNC
%token HEAD
%token IF ELSEIF ELSE
%token IN
%token LEFT_ANGLE_BRACKET RIGHT_ANGLE_BRACKET
%token LEFT_ANGLE_BRACKET_EQUALS RIGHT_ANGLE_BRACKET_EQUALS
%token LEFT_CURLY_BRACE RIGHT_CURLY_BRACE 
%token LEFT_PAREN RIGHT_PAREN 
%token LEFT_SQUARE_BRACKET RIGHT_SQUARE_BRACKET
%token LEN
%token MAP
%token MINUS
%token NOT_EQUALS
%token OPTIONS
%token OR
%token PLUS
%token PREPEND
%token PRINT
%token POLL_FOR_RESPS 
%token POLL_FOR_ANY_RESP
%token NEXT_RESP
%token RETURN
%token RPC_ASYNC_CALL
%token RPC_CALL
%token SEMICOLON
%token SLASH
%token STAR
%token TAIL
%token QUOTE
%token EOF

%left LEFT_SQUARE_BRACKET
%right BANG
%left AND
%left OR
%left STAR SLASH
%left PLUS MINUS
%nonassoc EQUALS_EQUALS NOT_EQUALS LEFT_ANGLE_BRACKET RIGHT_ANGLE_BRACKET LEFT_ANGLE_BRACKET_EQUALS RIGHT_ANGLE_BRACKET_EQUALS
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

options:
  | id = ID
    { Option(id) :: [] }
  | id = ID COMMA opts = options
    { Option(id) :: opts }

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

collection:
  | LEFT_CURLY_BRACE RIGHT_CURLY_BRACE
    { MapLit([]) }
  | LEFT_CURLY_BRACE kvs = kv_pairs RIGHT_CURLY_BRACE
    { MapLit(kvs) }
  | l = list_lit
    { l}

collection_access:
  | collection_type = right_side LEFT_SQUARE_BRACKET key = right_side RIGHT_SQUARE_BRACKET
    { CollectionAccess(collection_type, key) }
  
literals:
  | OPTIONS LEFT_PAREN opts = options RIGHT_PAREN
    { Options(opts) }
  | QUOTE s = ID QUOTE
    { String(s) }
  | QUOTE QUOTE
    { String("") }
  | i = integer
    { i }

integer:
  | i = INT
    { Int(i) }
  | MINUS i = INT
    { Int(-i) }
  (*| i1 = INT PLUS i2 = INT
    { Int(i1 + i2) }  
  | i1 = INT MINUS i2 = INT
    { Int(i1 - i2) }
  // | i = INT PLUS PLUS
  //   { Int(i + 1) }
  // | i = INT MINUS MINUS
  //   { Int(i - 1) }*)

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

left_side:
  | id = ID
    { VarLHS(id) }
  | ca = collection_access
    { CollectionAccessLHS(ca) }
  // | rhs = right_side DOT key = ID
  //   { FieldAccessLHS(rhs, key) } 
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
  | rhs1 = right_side LEFT_ANGLE_BRACKET rhs2 = right_side
    { LessThan (rhs1, rhs2)}
  | rhs1 = right_side LEFT_ANGLE_BRACKET_EQUALS rhs2 = right_side
    { LessThanEquals (rhs1, rhs2)}
  | rhs1 = right_side RIGHT_ANGLE_BRACKET rhs2 = right_side
    { GreaterThan (rhs1, rhs2)}
  | rhs1 = right_side RIGHT_ANGLE_BRACKET_EQUALS rhs2 = right_side
    { GreaterThanEquals (rhs1, rhs2)}
  | LEFT_PAREN b = boolean RIGHT_PAREN
    { b }

list_lit:
  | LEFT_SQUARE_BRACKET RIGHT_SQUARE_BRACKET
    { ListLit([]) }
  | LEFT_SQUARE_BRACKET items = items RIGHT_SQUARE_BRACKET
    { ListLit(items) }
  | APPEND LEFT_PAREN ls = right_side COMMA item = right_side RIGHT_PAREN
    { ListAppend(ls, item) }
  | PREPEND LEFT_PAREN item = right_side COMMA ls = right_side RIGHT_PAREN
    { ListPrepend(item, ls) }

list_ops:
  | HEAD LEFT_PAREN ls = right_side RIGHT_PAREN
    { Head(ls) }
  | TAIL LEFT_PAREN ls = right_side RIGHT_PAREN
    { Tail(ls) }
  | LEN LEFT_PAREN ls = right_side RIGHT_PAREN
    { Len(ls) }

right_side:
  | id = ID
    { VarRHS(id) }
  // | mapName = ID LEFT_SQUARE_BRACKET key = ID RIGHT_SQUARE_BRACKET
  //   { MapAccessRHS(mapName, key) }
  // | ls = right_side LEFT_SQUARE_BRACKET idx = INT RIGHT_SQUARE_BRACKET
  //   { ListAccess(ls, idx) }
  | ca = collection_access
    { CollectionAccessRHS(ca) } 
  | func_call = func_call
    { FuncCallRHS(func_call)}
  | literal = literals
    { LiteralRHS(literal) }
  | b = boolean
    { BoolRHS b }
  | c = collection
    { CollectionRHS c }
  | rpc_call = rpc_call
    { RpcCallRHS rpc_call }
  | lo = list_ops
    { lo }
  | i1 = right_side PLUS i2 = right_side
    { Plus(i1, i2) }
  | i1 = right_side MINUS i2 = right_side
    { Minus(i1, i2) }
  | i1 = right_side STAR i2 = right_side
    { Times(i1, i2) }
  | i1 = right_side SLASH i2 = right_side
    { Div(i1, i2) }
  | POLL_FOR_RESPS LEFT_PAREN resps = right_side COMMA rhs2 = right_side RIGHT_PAREN
    { PollForResps(resps, rhs2) }
  | POLL_FOR_ANY_RESP LEFT_PAREN resps = right_side RIGHT_PAREN
    { PollForAnyResp(resps) }
  | NEXT_RESP LEFT_PAREN resps = right_side RIGHT_PAREN
    { NextResp(resps) }
  (*| rhs = right_side DOT key = ID
    { FieldAccessRHS(rhs, key) }*)

assignment:
  | lhs = left_side EQUALS rhs = right_side
    { Assignment(lhs, rhs) }

statement:
  | cond_stmts = cond_stmts
    { CondList(cond_stmts)}
  | a = assignment SEMICOLON
    { AssignmentStmt(a) }
  | r = right_side SEMICOLON
    { Expr(r) }
  | RETURN r = right_side SEMICOLON
    { Return(r) }
  | FOR LEFT_PAREN init = assignment SEMICOLON
    cond = right_side SEMICOLON 
    progress = assignment RIGHT_PAREN
    LEFT_CURLY_BRACE
    body = statements
    RIGHT_CURLY_BRACE
    { ForLoop(init, cond, progress, body) }
  | FOR LEFT_PAREN idx = left_side IN col = right_side RIGHT_PAREN LEFT_CURLY_BRACE
    body = statements
    RIGHT_CURLY_BRACE
    { ForLoopIn(idx, col, body) }
  | AWAIT r = right_side SEMICOLON
    { Await(r) }
  | PRINT LEFT_PAREN r = right_side RIGHT_PAREN SEMICOLON
    { Print(r) }

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
  // | id = ID LEFT_PAREN params = params RIGHT_PAREN LEFT_CURLY_BRACE
  //   var_inits = var_inits
  //   func_defs = func_defs
  //   RIGHT_CURLY_BRACE
  //   { RoleDef(id, params, var_inits, func_defs) }

client_def:
  | CLIENT_INTERFACE LEFT_CURLY_BRACE
    func_defs = func_defs
    RIGHT_CURLY_BRACE
    { ClientDef(func_defs) }
