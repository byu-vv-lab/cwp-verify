grammar Expr;
prog: expr EOF;

expr
  : expr IMPLIESOP expr
  | binary_expr
  ;

binary_expr
  : binary_expr BINARYOP binary_expr
  | relational_expr
  | '(' binary_expr ')'
  ;

relational_expr
  : NOT relational_comparison
  | relational_comparison
  ;

relational_comparison
  : numeric_computational_expr NUMERIC_RELATIONAL numeric_computational_expr
  ;

numeric_computational_expr
  : numeric_computational_expr (NUMERIC_COMPUTATION | MINUS) numeric_computational_expr
  | (ID | MINUS ID)
  | '(' numeric_computational_expr ')'
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

NUMERIC_COMPUTATION : '*' | '/' | '//' | '%' | '+';

NUMERIC_RELATIONAL: '>' | '<' | '>' '=' | '<' '=';

BINARYOP    :  '&' '&' | '|' '|' | '=' '=' | '!' '=';

IMPLIESOP   : '=' '=' '>' | '<' '=' '=' | '<' '=' '=' '>';

NEWLINE: [\r\n]+ ;

INT: [0-9]+ ;
