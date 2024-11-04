grammar Expr;
prog: expr;

expr
  : (numeric_computational_expr | numeric_relational_expr | binary_expr | implies_expr) + EOF
  ;

numeric_computational_expr
  : (ID | MINUS ID) (MINUS | NUMERIC_COMPUTATION) (ID | MINUS ID)
  ;

numeric_relational_expr
  : (ID | MINUS ID) (NUMERIC_RELATIONAL) (ID | MINUS ID)
  ;

binary_expr
  : (ID | NOT ID | numeric_relational_expr | NOT numeric_relational_expr) BINARYOP (ID | NOT ID | numeric_relational_expr | NOT numeric_relational_expr)
  ;

implies_expr
  : (ID | NOT ID | binary_expr) IMPLIESOP (ID | NOT ID | binary_expr)
  ;

// ---------------------------------------------------------------------------
// Lexer Rules
// ---------------------------------------------------------------------------
ID
  : [a-zA-Z0-9_]+
  ;

WS : [ \t\n\r]+ -> skip ;

NOT : '!';

MINUS : '-';

NUMERIC_COMPUTATION : '*' | '/' | '//' | '%' | '+' ;

NUMERIC_RELATIONAL: '>' | '<' | '>' '=' | '<' '=';

BINARYOP    :  '&' '&' | '|' '|' | '=' '=' | '!' '=';

IMPLIESOP   : '=' '=' '>' | '<' '=' '=' | '<' '=' '=' '>';

NEWLINE: [\r\n]+ ;

INT: [0-9]+ ;
