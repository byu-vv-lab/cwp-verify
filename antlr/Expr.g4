grammar Expr;

expr
  : (strictly_math_expr)* (binary_expr)* (implies_expr) + EOF
  ;

strictly_math_expr
  : (ID | MINUS ID) (MINUS | STRICTLY_MATH) (ID | MINUS ID)
  ;

binary_expr
  : (ID | NOT ID) BINARYOP (ID | NOT ID)
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

STRICTLY_MATH : '*' | '/' | '//' | '%' | '+' | '>' | '<' | '>' '=' | '<' '=';

BINARYOP    :  '&' '&' | '|' '|' | '=' '=' | '!' '=';

IMPLIESOP   : '=' '=' '>' | '<' '=' '=' | '<' '=' '=' '>';
