# Generated from antlr/Expr.g4 by ANTLR 4.13.2
from antlr4 import *
if "." in __name__:
    from .ExprParser import ExprParser
else:
    from ExprParser import ExprParser

# This class defines a complete listener for a parse tree produced by ExprParser.
class ExprListener(ParseTreeListener):

    # Enter a parse tree produced by ExprParser#expr.
    def enterExpr(self, ctx:ExprParser.ExprContext):
        pass

    # Exit a parse tree produced by ExprParser#expr.
    def exitExpr(self, ctx:ExprParser.ExprContext):
        pass


    # Enter a parse tree produced by ExprParser#strictly_math_expr.
    def enterStrictly_math_expr(self, ctx:ExprParser.Strictly_math_exprContext):
        pass

    # Exit a parse tree produced by ExprParser#strictly_math_expr.
    def exitStrictly_math_expr(self, ctx:ExprParser.Strictly_math_exprContext):
        pass


    # Enter a parse tree produced by ExprParser#binary_expr.
    def enterBinary_expr(self, ctx:ExprParser.Binary_exprContext):
        pass

    # Exit a parse tree produced by ExprParser#binary_expr.
    def exitBinary_expr(self, ctx:ExprParser.Binary_exprContext):
        pass


    # Enter a parse tree produced by ExprParser#implies_expr.
    def enterImplies_expr(self, ctx:ExprParser.Implies_exprContext):
        pass

    # Exit a parse tree produced by ExprParser#implies_expr.
    def exitImplies_expr(self, ctx:ExprParser.Implies_exprContext):
        pass



del ExprParser