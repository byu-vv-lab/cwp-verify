# Generated from antlr/Expr.g4 by ANTLR 4.13.2
from antlr4 import *
if "." in __name__:
    from .ExprParser import ExprParser
else:
    from ExprParser import ExprParser

# This class defines a complete listener for a parse tree produced by ExprParser.
class ExprListener(ParseTreeListener):

    # Enter a parse tree produced by ExprParser#prog.
    def enterProg(self, ctx:ExprParser.ProgContext):
        pass

    # Exit a parse tree produced by ExprParser#prog.
    def exitProg(self, ctx:ExprParser.ProgContext):
        pass


    # Enter a parse tree produced by ExprParser#expr.
    def enterExpr(self, ctx:ExprParser.ExprContext):
        pass

    # Exit a parse tree produced by ExprParser#expr.
    def exitExpr(self, ctx:ExprParser.ExprContext):
        pass


    # Enter a parse tree produced by ExprParser#binary_expr.
    def enterBinary_expr(self, ctx:ExprParser.Binary_exprContext):
        pass

    # Exit a parse tree produced by ExprParser#binary_expr.
    def exitBinary_expr(self, ctx:ExprParser.Binary_exprContext):
        pass


    # Enter a parse tree produced by ExprParser#relational_expr.
    def enterRelational_expr(self, ctx:ExprParser.Relational_exprContext):
        pass

    # Exit a parse tree produced by ExprParser#relational_expr.
    def exitRelational_expr(self, ctx:ExprParser.Relational_exprContext):
        pass


    # Enter a parse tree produced by ExprParser#relational_comparison.
    def enterRelational_comparison(self, ctx:ExprParser.Relational_comparisonContext):
        pass

    # Exit a parse tree produced by ExprParser#relational_comparison.
    def exitRelational_comparison(self, ctx:ExprParser.Relational_comparisonContext):
        pass


    # Enter a parse tree produced by ExprParser#numeric_computational_expr.
    def enterNumeric_computational_expr(self, ctx:ExprParser.Numeric_computational_exprContext):
        pass

    # Exit a parse tree produced by ExprParser#numeric_computational_expr.
    def exitNumeric_computational_expr(self, ctx:ExprParser.Numeric_computational_exprContext):
        pass



del ExprParser