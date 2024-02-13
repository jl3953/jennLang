%{
  open Core
  open Ast
%}

%token <string> ID
%token <bool> TRUE FALSE
%token ARROW
%token CLIENT_INTERFACE
%token COMMA
%token EQUALS
%token FUNC
%token IF ELSEIF ELSE
%token LEFT_ANGLE_BRACKET RIGHT_ANGLE_BRACKET
%token LEFT_CURLY_BRACE RIGHT_CURLY_BRACE 
%token LEFT_PAREN RIGHT_PAREN 
%token LEFT_SQUARE_BRACKET RIGHT_SQUARE_BRACKET
%token MAP
%token OPTIONS
%token DOT
%token RETURN
%token RPC_CALL
%token SEMICOLON
%token QUOTE
%token EOF

%type <Ast.prog> program
// %type <if_stmt> if_stmt
// %type <elseif_stmts> elseif_stmts
// %type <exp> exp
// %type <func_call> func_call
// %type <left_side> left_side
// %type <right_side> right_side
// %type <map_expr> map_expr
// %type <statement> statement
// %type <params> params
// %type <role_def> role_def
// %type <Ast.prog> statements
// %type <Ast.rpc_call> rpc_call
// %type <Ast.func_def> func_def
// %type <Ast.func_defs> func_defs
//%type <var_inits> var_inits
// %type <Ast.type_def> type_def
// %type <Ast.default_val> default_val
// %type <cond_stmts> cond_stmts
// %type <var_init> var_init
// %type <assignment_expr> assignment_expr


%start program

%%

program:
  | r = role_def c = client_def EOF
    { Prog(r::[], c) }
  | r = role_def p = program
    { match p with
      | Prog(roles, client) -> Prog(r::roles, client)}

  
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
    {i :: []}
  | i = if_stmt el = elseif_stmts
    { i :: el }
  | i = if_stmt ELSE LEFT_CURLY_BRACE
    else_body = statements
    RIGHT_CURLY_BRACE
    { i :: [IfElseIf(Bool(true), else_body)] }
  | i = if_stmt el = elseif_stmts ELSE LEFT_CURLY_BRACE
    else_body = statements
    RIGHT_CURLY_BRACE
    { i :: el @ [IfElseIf(Bool(true), else_body)] }

rpc_call:
  | RPC_CALL LEFT_PAREN host = ID COMMA func_call = func_call RIGHT_PAREN
    { RpcCall(host, func_call) }
  | RPC_CALL LEFT_PAREN QUOTE host = ID QUOTE COMMA func_call = func_call RIGHT_PAREN
    { RpcCall(host, func_call) }

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

default_val:
  | LEFT_CURLY_BRACE RIGHT_CURLY_BRACE
    { EmptyMap }
  | OPTIONS LEFT_PAREN opts = options RIGHT_PAREN
    { Options(opts) }
  | QUOTE s = ID QUOTE
    { String(s) }

var_init:
  | typ = type_def id = ID EQUALS default = default_val
    { VarInit(typ, id, default) }

var_inits:
  | v = var_init SEMICOLON
    {v :: []}
  | v = var_init SEMICOLON vs = var_inits
    {v :: vs}

left_side:
  | id = ID
    { VarLHS(id) }
  | mapName = ID LEFT_SQUARE_BRACKET key = ID RIGHT_SQUARE_BRACKET
    { MapAccessLHS(mapName, key) }
  | rhs = right_side DOT key = ID
    { FieldAccessLHS(rhs, key) } 

right_side:
  | TRUE
    { Bool true }
  | FALSE
    { Bool false }
  | id = ID
    { VarRHS(id) }
  | mapName = ID LEFT_SQUARE_BRACKET key = ID RIGHT_SQUARE_BRACKET
    { MapAccessRHS(mapName, key) }
  | rhs = right_side DOT key = ID
    { FieldAccessRHS(rhs, key) }
  | func_call = func_call
    { FuncCallRHS(func_call)}
  | default_val = default_val
    { DefValRHS(default_val) }
    | BANG rhs = right_side
    { Not(rhs) }
  | left = right_side EQUALS_EQUALS right = right_side
    { EqualsEquals(left, right) }
  | left = right_side NOT_EQUALS right = right_side
    { NotEquals(left, right) }
  | left = right_side AND right = right_side
    { And(left, right) }
  | left = right_side OR right = right_side
    { Or(left, right) }

  exp:
  | left = left_side EQUALS right = exp
    { Assignment(left, right)}
  | rhs = right_side  
    { RHS(rhs) }
  | rpc_call = rpc_call
    { RpcCallRHS(rpc_call) }

statement:
  | cond_stmts = cond_stmts
    { CondList(cond_stmts)}
  | e = exp SEMICOLON
    { Expr(e) }
  | RETURN e = exp SEMICOLON
    { Return(e) }

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
  | id = ID LEFT_PAREN params = params RIGHT_PAREN LEFT_CURLY_BRACE
    var_inits = var_inits
    func_defs = func_defs
    RIGHT_CURLY_BRACE
    { RoleDef(id, params, var_inits, func_defs) }

client_def:
  | CLIENT_INTERFACE LEFT_CURLY_BRACE
    func_defs = func_defs
    RIGHT_CURLY_BRACE
    { ClientDef(func_defs) }
