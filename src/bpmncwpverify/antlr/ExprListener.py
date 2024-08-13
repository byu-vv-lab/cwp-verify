# Generated from antlr/Expr.g4 by ANTLR 4.13.2
from antlr4 import *
if "." in __name__:
    from .ExprParser import ExprParser
else:
    from ExprParser import ExprParser

# This class defines a complete listener for a parse tree produced by ExprParser.
class ExprListener(ParseTreeListener):

    # Enter a parse tree produced by ExprParser#binary_expr.
    def enterBinary_expr(self, ctx:ExprParser.Binary_exprContext):
        pass

    # Exit a parse tree produced by ExprParser#binary_expr.
    def exitBinary_expr(self, ctx:ExprParser.Binary_exprContext):
        pass



del ExprParser