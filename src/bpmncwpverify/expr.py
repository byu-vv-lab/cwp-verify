from typing import List
from bpmncwpverify import typechecking
from bpmncwpverify.antlr.ExprListener import ExprListener
from bpmncwpverify.antlr.ExprLexer import ExprLexer
from bpmncwpverify.antlr.ExprParser import ExprParser
from antlr4 import CommonTokenStream, InputStream, ParseTreeWalker
from antlr4.error.ErrorStrategy import ParseCancellationException
from antlr4.error.ErrorListener import ConsoleErrorListener, ErrorListener

from returns.result import Failure, Result, Success
from returns.pipeline import flow, is_successful
from returns.pointfree import bind_result
from returns.curry import partial
from bpmncwpverify.state import SymbolTable
from bpmncwpverify.error import Error


def _get_parser(file_contents: str) -> Result[ExprParser, Error]:
    input_stream = InputStream(file_contents)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)
    parser.removeErrorListener(ConsoleErrorListener.INSTANCE)
    parser.addErrorListener(ErrorListener())
    return Success(parser)


def _parse_expressions(parser: ExprParser) -> Result[ExprParser.ExprContext, Error]:
    try:
        tree: ExprParser.ExprContext = parser.expr()
        return Success(tree)
    except ParseCancellationException as exception:
        msg = str(exception)
        failure_value = Exception(msg)
        return Failure(failure_value)


class ExpressionListener(ExprListener):  # type: ignore
    def __init__(self, symbol_table: SymbolTable) -> None:
        self.symbol_table = symbol_table
        self.type_stack: List[str] = []

    def check_and_push_type(self, left_type: str, right_type: str) -> None:
        if not is_successful(
            result := typechecking.get_type_assign(left_type, right_type)
        ):
            raise TypeError(f"Type mismatch: {left_type} != {right_type}")
        self.type_stack.append(result.unwrap())

    def exitOr(self, ctx: ExprParser.OrContext) -> None:
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        if not (right_type == typechecking.BOOL and left_type == typechecking.BOOL):
            raise TypeError(
                f"Type mismatch: {left_type} || {right_type}. Both should be BOOL"
            )
        self.type_stack.append(typechecking.BOOL)

    def exitAnd(self, ctx: ExprParser.AndContext) -> None:
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        if not (right_type == typechecking.BOOL and left_type == typechecking.BOOL):
            raise TypeError(
                f"Type mismatch: {left_type} && {right_type}. Both should be BOOL"
            )
        self.type_stack.append(typechecking.BOOL)

    def exitNot(self, ctx: ExprParser.NotContext) -> None:
        expr_type = self.type_stack.pop()
        if expr_type != typechecking.BOOL:
            raise TypeError(
                f"Type mismatch: tried to `not` a non-boolean expression: {expr_type}"
            )
        self.type_stack.append(typechecking.BOOL)

    def exitRelational(self, ctx: ExprParser.RelationalContext) -> None:
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        if not is_successful(typechecking.get_type_assign(left_type, right_type)):
            raise TypeError(f"Type mismatch: {left_type} != {right_type}")
        self.type_stack.append(typechecking.BOOL)

    def exitAddSub(self, ctx: ExprParser.AddSubContext) -> None:
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        self.check_and_push_type(left_type, right_type)

    def exitMulDiv(self, ctx: ExprParser.MulDivContext) -> None:
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        self.check_and_push_type(left_type, right_type)

    def exitNegate(self, ctx: ExprParser.NegateContext) -> None:
        expr_type = self.type_stack.pop()
        if expr_type == typechecking.BOOL:
            raise TypeError(
                f"Type mismatch: tried to negate a boolean expression: {expr_type}"
            )
        self.type_stack.append(expr_type)

    def enterID(self, ctx: ExprParser.IDContext) -> None:
        identifier: str = ctx.ID().getText()
        if identifier in self.symbol_table._id2type:
            self.type_stack.append(self.symbol_table.get_type(identifier).unwrap())
        else:
            raise ValueError(f"Undefined identifier: {identifier}")

    def exitParens(self, ctx: ExprParser.ParensContext) -> None:
        pass

    @staticmethod
    def _build(
        symbol_table: SymbolTable, context: ExprParser.ExprContext
    ) -> Result[None, Error]:
        listener = ExpressionListener(symbol_table)
        try:
            ParseTreeWalker.DEFAULT.walk(listener, context)
            return Success(None)
        except Exception as exception:
            assert len(exception.args) == 1
            error: Error = exception.args[0]
            return Failure(error)

    @staticmethod
    def build(
        expression: str, symbol_table: SymbolTable
    ) -> Result["ExpressionListener", Error]:
        build_with_params = partial(ExpressionListener._build, symbol_table)
        result: Result["ExpressionListener", Error] = flow(
            expression,
            _get_parser,
            bind_result(_parse_expressions),
            bind_result(build_with_params),
        )
        return result
