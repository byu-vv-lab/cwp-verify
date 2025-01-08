import builtins

from antlr4 import CommonTokenStream, InputStream, ParseTreeWalker
from antlr4.error.ErrorStrategy import ParseCancellationException
from antlr4.error.ErrorListener import ConsoleErrorListener, ErrorListener
from antlr4.tree.Tree import TerminalNode, TerminalNodeImpl
from antlr4.Token import Token

from returns.maybe import Maybe, Nothing, Some
from returns.result import Failure, Result, Success
from returns.pipeline import flow, is_successful
from returns.pointfree import bind_result
from returns.functions import not_
from returns.curry import partial

from typing import Any, cast, Iterable

from bpmncwpverify.antlr.StateLexer import StateLexer
from bpmncwpverify.antlr.StateParser import StateParser
from bpmncwpverify.antlr.StateListener import StateListener

from bpmncwpverify.core.error import (
    Error,
    StateInitNotInValues,
    StateMultipleDefinitionError,
    StateSyntaxError,
)

from bpmncwpverify.core import typechecking


def antlr_id_set_context_get_children(
    ctx: StateParser.Id_setContext,
) -> list[TerminalNodeImpl]:
    return [antlr_get_terminal_node_impl(i) for i in ctx.getChildren()]  # type: ignore[unused-ignore]


def antlr_get_id_set_context(ctx: Any) -> Maybe[StateParser.Id_setContext]:
    if ctx is None:
        return Nothing
    assert isinstance(ctx, StateParser.Id_setContext)
    return Some(ctx)


def antlr_get_terminal_node_impl(node: TerminalNode | None) -> TerminalNodeImpl:
    assert isinstance(node, TerminalNodeImpl)
    return node


def antlr_get_text(node: TerminalNodeImpl | StateParser.TypeContext) -> str:
    text: str | None = node.getText()
    assert isinstance(text, str)
    return text


def antlr_get_type_from_type_context(
    ctx: StateParser.Const_var_declContext | StateParser.Var_declContext,
) -> str:
    type_context: Any = ctx.type_()
    assert isinstance(type_context, StateParser.TypeContext)
    return antlr_get_text(type_context)


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


def _get_parser(file_contents: str) -> Result[StateParser, Error]:
    input_stream = InputStream(file_contents)
    lexer = StateLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = StateParser(stream)
    parser.removeErrorListener(ConsoleErrorListener.INSTANCE)  # type: ignore[unused-ignore]
    parser.addErrorListener(ThrowingErrorListener())  # type: ignore[unused-ignore]
    return Success(parser)


def _parse_state(parser: StateParser) -> Result[StateParser.StateContext, Error]:
    try:
        tree: StateParser.StateContext = parser.state()
        return Success(tree)
    except ParseCancellationException as exception:
        msg = str(exception)
        failure_value = StateSyntaxError(msg)
        return Failure(failure_value)


class DeclLoc:
    __slots__ = ["line", "col"]

    def __init__(self, line: Maybe[int], col: Maybe[int]) -> None:
        self.line = line
        self.col = col


class AllowedValueDecl(DeclLoc):
    __slots__ = ["value"]

    def __init__(
        self, value: str, line: Maybe[int] = Nothing, col: Maybe[int] = Nothing
    ) -> None:
        super().__init__(line, col)
        self.value = value


class ConstDecl(DeclLoc):
    __slots__ = ["id", "type_", "init"]

    def __init__(
        self,
        id: str,
        type_: str,
        init: AllowedValueDecl,
        line: Maybe[int] = Nothing,
        col: Maybe[int] = Nothing,
    ) -> None:
        super().__init__(line, col)
        self.id = id
        self.type_ = type_
        self.init = init


class EnumDecl(DeclLoc):
    __slots__ = ["id", "values"]

    def __init__(
        self,
        id: str,
        values: list[AllowedValueDecl],
        line: Maybe[int] = Nothing,
        col: Maybe[int] = Nothing,
    ) -> None:
        super().__init__(line, col)
        self.id = id
        self.values = values


class VarDecl(DeclLoc):
    __slots__ = ["id", "type_", "init", "values", "line", "col"]

    def __init__(
        self,
        id: str,
        type_: str,
        init: AllowedValueDecl,
        values: list[AllowedValueDecl],
        line: Maybe[int] = Nothing,
        col: Maybe[int] = Nothing,
    ) -> None:
        super().__init__(line, col)
        self.id = id
        self.type_ = type_
        self.init = init
        self.values = values

    @staticmethod
    def var_decl(
        id: str,
        type_: str,
        init: AllowedValueDecl,
        values: list[AllowedValueDecl],
        line: Maybe[int] = Nothing,
        col: Maybe[int] = Nothing,
    ) -> Result["VarDecl", Error]:
        value_ids = {i.value for i in values}
        if len(values) == 0 or init.value in value_ids:
            return Success(VarDecl(id, type_, init, values, line, col))
        else:
            return Failure(
                StateInitNotInValues(init.value, init.line, init.col, value_ids)
            )


class TypeWithDeclLoc:
    __slots__ = ["type_", "decl_loc"]

    def __init__(self, type_: str, decl_loc: DeclLoc) -> None:
        self.type_ = type_
        self.decl_loc = decl_loc


class StateBuilder:
    __slots__ = ["_consts", "_enums", "_vars"]

    def __init__(self) -> None:
        self._consts: list[ConstDecl] = list()
        self._enums: list[EnumDecl] = list()
        self._vars: list[VarDecl] = list()

    def with_enum_type_decl(self, enum_decl: EnumDecl) -> "StateBuilder":
        self._enums.append(enum_decl)
        return self

    def with_const_decl(self, const_decl: ConstDecl) -> "StateBuilder":
        self._consts.append(const_decl)
        return self

    def with_var_decl(self, var_decl: VarDecl) -> "StateBuilder":
        self._vars.append(var_decl)
        return self

    def build(self) -> Result["State", Error]:
        state = State(self._consts, self._enums, self._vars)
        return State.type_check(state)


class State:
    __slots__ = ["consts", "enums", "_id2type", "vars"]

    class _Listener(StateListener):  # type: ignore[misc]
        __slots__ = ["state_builder", "error"]

        def __init__(self) -> None:
            super().__init__()
            self.state_builder: "StateBuilder" = StateBuilder()
            self.error: Maybe[Error] = Nothing

        @staticmethod
        def _get_id(id_node: TerminalNodeImpl) -> str:
            id: str = antlr_get_text(id_node)
            return id

        @staticmethod
        def _get_value_decl(id_node: TerminalNodeImpl) -> AllowedValueDecl:
            id: str = antlr_get_text(id_node)
            symbol: Token = id_node.getSymbol()
            return AllowedValueDecl(
                id, Some(cast(int, symbol.line)), Some(cast(int, symbol.column))
            )

        @staticmethod
        def _get_values(
            ctx: Maybe[StateParser.Id_setContext],
        ) -> list[AllowedValueDecl]:
            if ctx == Nothing:
                return list()
            return [
                State._Listener._get_value_decl(i)
                for i in antlr_id_set_context_get_children(ctx.unwrap())
            ]

        def exitEnum_type_decl(self, ctx: StateParser.Enum_type_declContext) -> None:
            node = antlr_get_terminal_node_impl(ctx.ID())
            symbol: Token = node.getSymbol()
            id: str = State._Listener._get_id(node)
            id_line = Some(cast(int, symbol.line))
            id_col = Some(cast(int, symbol.column))

            values: list[AllowedValueDecl] = State._Listener._get_values(
                antlr_get_id_set_context(ctx.id_set()),
            )

            enum_decl = EnumDecl(id, values, id_line, id_col)
            self.state_builder.with_enum_type_decl(enum_decl)

        def exitConst_var_decl(self, ctx: StateParser.Const_var_declContext) -> None:
            node = antlr_get_terminal_node_impl(ctx.ID(0))
            symbol: Token = node.getSymbol()
            id = State._Listener._get_id(node)
            id_line = Some(cast(int, symbol.line))
            id_col = Some(cast(int, symbol.column))

            type_: str = antlr_get_type_from_type_context(ctx)

            node = antlr_get_terminal_node_impl(ctx.ID(1))
            symbol = node.getSymbol()
            init = AllowedValueDecl(
                antlr_get_text(node),
                Some(cast(int, symbol.line)),
                Some(cast(int, symbol.column)),
            )

            const_decl = ConstDecl(id, type_, init, id_line, id_col)
            self.state_builder.with_const_decl(const_decl)

        def exitVar_decl(self, ctx: StateParser.Var_declContext) -> None:
            node = antlr_get_terminal_node_impl(ctx.ID(0))
            symbol: Token = node.getSymbol()
            id: str = State._Listener._get_id(node)
            id_line = Some(cast(int, symbol.line))
            id_col = Some(cast(int, symbol.column))

            type_: str = antlr_get_type_from_type_context(ctx)

            node = antlr_get_terminal_node_impl(ctx.ID(1))
            symbol = node.getSymbol()
            init: AllowedValueDecl = AllowedValueDecl(
                antlr_get_text(node),
                Some(cast(int, symbol.line)),
                Some(cast(int, symbol.column)),
            )

            values: list[AllowedValueDecl] = State._Listener._get_values(
                antlr_get_id_set_context(ctx.id_set()),
            )

            var_decl = VarDecl.var_decl(id, type_, init, values, id_line, id_col)
            if not_(is_successful)(var_decl):
                self.error = Some(var_decl.failure())
                raise Exception()
            self.state_builder.with_var_decl(var_decl.unwrap())

    def __init__(
        self, consts: list[ConstDecl], enums: list[EnumDecl], vars: list[VarDecl]
    ) -> None:
        self.consts = consts
        self.enums = enums
        self._id2type: Maybe[dict[str, TypeWithDeclLoc]] = Nothing
        self.vars = vars

    def __str__(self) -> str:
        raise builtins.NotImplementedError("SymbolTable::__str__")

    @staticmethod
    def _build_id_2_type_consts(state: "State") -> Result["State", Error]:
        # requires
        assert state._id2type != Nothing

        id2type = state._id2type.unwrap()
        for const_decl in state.consts:
            if const_decl.id in id2type:
                first = (id2type[const_decl.id]).decl_loc
                return Failure(
                    StateMultipleDefinitionError(
                        const_decl.id,
                        const_decl.line,
                        const_decl.col,
                        first.line,
                        first.col,
                    )
                )
            id2type[const_decl.id] = TypeWithDeclLoc(const_decl.type_, const_decl)

        return Success(state)

    @staticmethod
    def _build_id_2_type_enums(state: "State") -> Result["State", Error]:
        # requires
        assert state._id2type != Nothing

        for i in state.enums:
            result = state._build_id_2_type_enum(i)
            if not_(is_successful)(result):
                return result

        return Success(state)

    @staticmethod
    def _build_id_2_type_vars(state: "State") -> Result["State", Error]:
        # requires
        assert state._id2type != Nothing

        for i in state.vars:
            result = state._build_id_2_type_var(i)
            if not_(is_successful)(result):
                return result

        return Success(state)

    @staticmethod
    def _from_str(context: StateParser.StateContext) -> Result["State", Error]:
        listener = State._Listener()
        try:
            walker: ParseTreeWalker = cast(ParseTreeWalker, ParseTreeWalker.DEFAULT)
            walker.walk(listener, context)
            return listener.state_builder.build()
        except Exception:
            # requires
            assert listener.error != Nothing
            return Failure(listener.error.unwrap())

    @staticmethod
    def _type_check_assigns(
        state: "State", ltype: str, values: Iterable[AllowedValueDecl]
    ) -> Result[tuple[()], Error]:
        get_type_init = partial(State.get_type, state)
        get_type_assign = partial(typechecking.get_type_assign, ltype)
        for i in values:
            result: Result[str, Error] = flow(
                i.value, get_type_init, bind_result(get_type_assign)
            )
            if not_(is_successful)(result):
                return Failure(result.failure())
        return Success(())

    @staticmethod
    def _type_check_consts(state: "State") -> Result["State", Error]:
        type_check_assigns = partial(State._type_check_assigns, state)
        for const_decl in state.consts:
            result = type_check_assigns(const_decl.type_, [const_decl.init])
            if not_(is_successful)(result):
                return Failure(result.failure())
        return Success(state)

    @staticmethod
    def _type_check_vars(state: "State") -> Result["State", Error]:
        type_check_assigns = partial(State._type_check_assigns, state)
        for var_decl in state.vars:
            values = var_decl.values + [var_decl.init]
            result = type_check_assigns(var_decl.type_, values)
            if not_(is_successful)(result):
                return Failure(result.failure())
        return Success(state)

    @staticmethod
    def type_check(state: "State") -> Result["State", Error]:
        state._id2type = Some(dict())
        result: Result["State", Error] = flow(
            state,
            State._build_id_2_type_enums,
            bind_result(State._build_id_2_type_consts),
            bind_result(State._build_id_2_type_vars),
            bind_result(State._type_check_consts),
            bind_result(State._type_check_vars),
        )

        return result

    def _build_id_2_type_enum(self, enum_decl: EnumDecl) -> Result["State", Error]:
        # requires
        assert self._id2type != Nothing

        id2type = self._id2type.unwrap()
        if enum_decl.id in id2type:
            first = (id2type[enum_decl.id]).decl_loc
            return Failure(
                StateMultipleDefinitionError(
                    enum_decl.id, enum_decl.line, enum_decl.col, first.line, first.col
                )
            )
        id2type[enum_decl.id] = TypeWithDeclLoc(typechecking.ENUM, enum_decl)

        for v in enum_decl.values:
            if v.value in id2type:
                first = id2type[v.value].decl_loc
                return Failure(
                    StateMultipleDefinitionError(
                        v.value, v.line, v.col, first.line, first.col
                    )
                )
            else:
                id2type[v.value] = TypeWithDeclLoc(enum_decl.id, v)

        return Success(self)

    def _build_id_2_type_var(self, var_decl: VarDecl) -> Result["State", Error]:
        # requires
        assert self._id2type != Nothing

        id2type = self._id2type.unwrap()
        if var_decl.id in id2type:
            first = (id2type[var_decl.id]).decl_loc
            return Failure(
                StateMultipleDefinitionError(
                    var_decl.id, var_decl.line, var_decl.col, first.line, first.col
                )
            )
        id2type[var_decl.id] = TypeWithDeclLoc(var_decl.type_, var_decl)

        return Success(self)

    def get_type(self, id: str) -> Result[str, Error]:
        # requires
        assert self._id2type != Nothing

        id2type = self._id2type.unwrap()
        if id in id2type:
            return Success(id2type[id].type_)
        result: Result[str, Error] = typechecking.get_type_literal(id)
        return result

    def is_defined(self, id: str) -> bool:
        # requires
        assert self._id2type != Nothing

        defined: bool = is_successful(self.get_type(id))
        return defined

    @staticmethod
    def from_str(state_def: str) -> Result["State", Error]:
        result: Result["State", Error] = flow(
            state_def,
            _get_parser,
            bind_result(_parse_state),
            bind_result(State._from_str),
        )
        return result
