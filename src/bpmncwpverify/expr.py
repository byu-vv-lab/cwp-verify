from antlr4 import CommonTokenStream, InputStream
from antlr4.error.ErrorStrategy import ParseCancellationException
from antlr4.error.ErrorListener import ConsoleErrorListener, ErrorListener

from returns.result import Result, Success, Failure
from returns.pipeline import is_successful

from typing import Any

from bpmncwpverify.antlr.ExprParser import ExprParser
from bpmncwpverify.antlr.ExprLexer import ExprLexer
from bpmncwpverify.antlr.ExprListener import ExprListener

from bpmncwpverify.state import SymbolTable
from bpmncwpverify import typechecking


from bpmncwpverify.error import (
    Error,
    ExpressionNotaNumber,
    ExpressionSyntaxError,
    ExpressionUnknownVariableError,
    ExpressionVariableCompatabilityError,
)

# UNKNOWN SYMBOL ERROR
# TYPECHECK ERROR
# MULTIPLE DEF ERROR


class ThrowingErrorListener(ErrorListener):  # type: ignore[misc]
    def __init__(self) -> None:
        super().__init__()

    def syntaxError(
        self,
        recognizer: Any,
        offendingSymbol: Any,
        # line: int,
        # column: int,
        msg: str,
        e: Exception,
    ) -> None:
        # msg = "line {}:{} {}".format(line, column, msg)
        raise ParseCancellationException(msg)


def _get_parser(file_contents: str) -> Result[ExprParser, Error]:
    input_stream = InputStream(file_contents)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)
    parser.removeErrorListener(ConsoleErrorListener.INSTANCE)
    parser.addErrorListener(ThrowingErrorListener())
    return Success(parser)


def _parse_expressions(parser: ExprParser) -> Result[ExprParser.ExprContext, Error]:
    try:
        tree: ExprParser.ExprContext = parser.expr()
        return Success(tree)
    except ParseCancellationException as exception:
        msg = str(exception)
        failure_value = ExpressionSyntaxError(msg)
        return Failure(failure_value)


class ExpressionTypeChecker:
    __slots__ = ["_table"]

    class _Listener(ExprListener):
        __slots__ = ["_expressionTypeChecker"]

        def __init__(self, table: SymbolTable) -> None:
            self._expressionTypeChecker: "ExpressionTypeChecker" = (
                ExpressionTypeChecker(table)
            )

        def exitNumeric_computational_expr(
            self, ctx: ExprParser.Numeric_computational_exprContext
        ) -> None:
            id_1: str = ctx.ID(0).getText()
            id_2: str = ctx.ID(1).getText()

            self._expressionTypeChecker.numericComputationTypeCheck(id_1, id_2)

        def exitNumeric_relational_expr(
            self, ctx: ExprParser.Numeric_relational_exprContext
        ) -> None:
            id_1: str = ctx.ID(0).getText()
            id_2: str = ctx.ID(1).getText()

            """ self._expressionTypeChecker.numericRelationalTypeCheck(id_1, id_2) """

        def exitBinary_expr(self, ctx: ExprParser.Binary_exprContext) -> None:
            operation: str = ctx.BINARYOP(0).getText()
            leftside: str
            rightside: str
            for i in ctx.getChildren():
                continue

    def __init__(self, table: SymbolTable) -> None:
        self._table: SymbolTable = table

    def typeCheck(self, id_1: str, id_2: str) -> Result[str, Error]:
        result: Result[Result[str, Error], Error] = Result.do(
            self.typeCompare(a, b)
            for a in self.indType(id_1)
            for b in self.indType(id_2)
        )
        if is_successful(result):
            return result.unwrap()
        else:
            return Failure(result.failure())

    def numericComputationTypeCheck(self, id_1: str, id_2: str) -> Result[str, Error]:
        result: Result[Result[str, Error], Error] = Result.do(
            self.computationTypeCompare(a, b)
            for a in self.numericIndCheck(id_1)
            for b in self.numericIndCheck(id_2)
        )
        if is_successful(result):
            return result.unwrap()
        else:
            return Failure(result.failure())

    """ def numericRelationalTypeCheck(self, id_1: str, id_2: str) -> Result[str, Error]:
        result: Result[str, Error] = Result.do(
            self.numericIndCheck(id_1)
            self.numericIndCheck(id_2)
        )
        if is_successful(result):
            return Success("bool")
        else:
            return Failure(result.failure()) """

    def typeCompare(self, id_1: str, id_2: str) -> Result[str, Error]:
        result: Result[str, Error] = typechecking.get_type_assign(
            id_1, id_2, ExpressionVariableCompatabilityError
        )
        return result

    def computationTypeCompare(self, id_1: str, id_2: str) -> Result[str, Error]:
        result: Result[str, Error] = typechecking.get_computation_type_result(
            id_1, id_2, ExpressionVariableCompatabilityError
        )
        return result

    def indType(self, id: str) -> Result[str, Error]:
        result: Result[str, Error] = self._table.get_type(id)  # Catch error and replace
        if is_successful(result):
            return result
        else:
            return Failure(ExpressionUnknownVariableError(id))

    def numericIndCheck(self, id: str) -> Result[str, Error]:
        result: Result[str, Error] = self._table.get_type(id)
        if not is_successful(result):
            return Failure(ExpressionUnknownVariableError(id))
        if (
            result.unwrap() == "int"
            or result.unwrap() == "byte"
            or result.unwrap() == "short"
        ):
            return result
        else:
            return Failure(ExpressionNotaNumber(id))
