from antlr4 import CommonTokenStream, InputStream, ParseTreeWalker
from antlr4.error.ErrorStrategy import ParseCancellationException
from antlr4.error.ErrorListener import ConsoleErrorListener, ErrorListener

from typing import cast

from bpmncwpverify.antlr.ExprListener import ExprListener
from bpmncwpverify.antlr.ExprLexer import ExprLexer
from bpmncwpverify.antlr.ExprParser import ExprParser
from bpmncwpverify.core import typechecking
from bpmncwpverify.core.state import (
    SymbolTable,
    antlr_get_terminal_node_impl,
    antlr_get_text,
)
from bpmncwpverify.error import (
    Error,
    ExceptionError,
    ExpressionComputationCompatabilityError,
    ExpressionRelationCompatabilityError,
    ExpressionRelationalNotError,
    ExpressionNegatorError,
    ExpressionUnrecognizedID,
)

from returns.result import Failure, Result, Success
from returns.pipeline import flow, is_successful
from returns.pointfree import bind_result
from returns.curry import partial
from returns.functions import not_
from typing import Any, List


class ThrowingErrorListener(ErrorListener):  # type: ignore[misc]
    def __init__(self) -> None:
        super().__init__()

    def syntaxError(
        self,
        recognizer: Any,
        offendingSymbol: Any,
        line: int,
        column: int,
        msg: str,
        e: Exception,
    ) -> None:
        msg = "line {}:{} {}".format(line, column, msg)
        raise ParseCancellationException(msg)


def _get_parser(file_contents: str) -> Result[ExprParser, Error]:
    input_stream = InputStream(file_contents)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)
    parser.removeErrorListener(ConsoleErrorListener.INSTANCE)  # type: ignore[unused-ignore]
    parser.addErrorListener(ThrowingErrorListener())  # type: ignore[unused-ignore]
    return Success(parser)


def _parse_expressions(parser: ExprParser) -> Result[ExprParser.StartContext, Error]:
    try:
        tree: ExprParser.StartContext = parser.start()
        return Success(tree)
    except ParseCancellationException as exception:
        msg = str(exception)
        failure_value = ExceptionError(msg)
        return Failure(failure_value)


class ExpressionListener(ExprListener):  # type: ignore[misc]
    __slots__ = ["symbol_table", "type_stack", "final_type"]

    def __init__(self, symbol_table: SymbolTable) -> None:
        self.symbol_table = symbol_table
        self.type_stack: List[str] = []
        self.final_type: str

    def check_arithmetic_types(self, left_type: str, right_type: str) -> None:
        if not_(is_successful)(
            result := typechecking.get_computation_type_result(
                left_type, right_type, ExpressionComputationCompatabilityError
            )
        ):
            raise Exception(result.failure())
        self.type_stack.append(result.unwrap())

    def check_and_or_types(self, left_type: str, right_type: str) -> None:
        if not_(is_successful)(
            result := typechecking.get_and_or_type_result(
                left_type, right_type, ExpressionRelationCompatabilityError
            )
        ):
            raise Exception(result.failure())
        self.type_stack.append(result.unwrap())

    def exitStart(self, ctx: ExprParser.StartContext) -> None:
        self.final_type = self.type_stack.pop()

    def exitOr(self, ctx: ExprParser.OrContext) -> None:
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        self.check_and_or_types(left_type, right_type)

    def exitAnd(self, ctx: ExprParser.AndContext) -> None:
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        self.check_and_or_types(left_type, right_type)

    def exitNot(self, ctx: ExprParser.NotContext) -> None:
        expr_type = self.type_stack.pop()
        if expr_type != typechecking.BOOL:
            raise Exception(ExpressionRelationalNotError(expr_type))
        self.type_stack.append(typechecking.BOOL)

    def exitRelational(self, ctx: ExprParser.RelationalContext) -> None:
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        if not_(is_successful)(
            result := typechecking.get_relational_type_result(
                left_type, right_type, ExpressionRelationCompatabilityError
            )
        ):
            raise Exception(result.failure())
        self.type_stack.append(typechecking.BOOL)

    def exitAddSub(self, ctx: ExprParser.AddSubContext) -> None:
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        self.check_arithmetic_types(left_type, right_type)

    def exitMulDiv(self, ctx: ExprParser.MulDivContext) -> None:
        right_type = self.type_stack.pop()
        left_type = self.type_stack.pop()
        self.check_arithmetic_types(left_type, right_type)

    def exitNegate(self, ctx: ExprParser.NegateContext) -> None:
        expr_type = self.type_stack.pop()
        if expr_type == typechecking.BOOL:
            raise Exception(ExpressionNegatorError(expr_type))
        self.type_stack.append(expr_type)

    def enterID(self, ctx: ExprParser.IDContext) -> None:
        node = antlr_get_terminal_node_impl(ctx.ID())
        identifier = antlr_get_text(node)
        type = self.symbol_table.get_type(identifier)
        if not_(is_successful)(type):
            raise Exception(ExpressionUnrecognizedID(identifier))
        self.type_stack.append(type.unwrap())

    @staticmethod
    def _build(
        symbol_table: SymbolTable, context: ExprParser.ExprContext
    ) -> Result[str, Error]:
        listener = ExpressionListener(symbol_table)
        try:
            walker: ParseTreeWalker = cast(ParseTreeWalker, ParseTreeWalker.DEFAULT)
            walker.walk(listener, context)
            result: Result[str, Error] = Success(listener.final_type)
            return result
        except Exception as exception:
            assert len(exception.args) == 1
            error: Error = exception.args[0]
            return Failure(error)

    @staticmethod
    def type_check(expression: str, symbol_table: SymbolTable) -> Result[str, Error]:
        build_with_params = partial(ExpressionListener._build, symbol_table)
        result: Result[str, Error] = flow(
            expression,
            _get_parser,
            bind_result(_parse_expressions),
            bind_result(build_with_params),
        )
        return result
