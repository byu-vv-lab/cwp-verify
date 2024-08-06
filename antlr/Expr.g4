grammar State;

state
  : (enum_type_decl)* (const_var_decl)* (var_decl)+ EOF
  ;

enum_type_decl
  : ENUM ID LCURLY (ID)+ RCURLY
  ;

const_var_decl
  : CONST ID COLON ID EQUALS ID
  ;

var_decl
  : VAR ID COLON ID EQUALS ID (LCURLY (ID)+ RCURLY)?
  ;

// ---------------------------------------------------------------------------
// Lexer Rules
// ---------------------------------------------------------------------------

COLON
  : ':'
  ;

CONST
  : 'const'
  ;

ENUM
  : 'enum'
  ;

EQUALS
  : '='
  ;

LCURLY
  : '{'
  ;

RCURLY
  : '}'
  ;

VAR
  : 'var'
  ;

ID
  : [a-zA-Z0-9_]+
  ;

WS : [ \t\n\r]+ -> skip ;

ANDOR   : '&' '&' | '|' '|';

BINARYOP    : '+' | '-' | '*' | '/' | '%' | '&' | '^' | '|'
    | '>' | '<' | '>' '=' | '<' '=' | '=' '=' | '!' '='
    | '<' '<' | '>' '>' | ANDOR;
