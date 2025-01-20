from xml.etree.ElementTree import Element

from returns.unsafe import unsafe_perform_io
from returns.io import IOResultE
from returns.curry import partial
from returns.pipeline import flow, is_successful
from returns.pointfree import bind_result
from returns.result import Result, Success, Failure
from returns.functions import not_


from bpmncwpverify.core.error import Error, ExceptionError
from bpmncwpverify.core.state import State
from bpmncwpverify.core.cwp import Cwp
from bpmncwpverify.core.bpmn import Bpmn
from bpmncwpverify.core.accessmethods.bpmnmethods import (
    from_xml as bpmn_from_xml,
    generate_promela,
)
from bpmncwpverify.core.accessmethods.cwpmethods import (
    from_xml as cwp_from_xml,
    generate_ltl,
)


class Builder:
    __slots__ = [
        "behavior_str",
        "bpmn",
        "bpmn_root",
        "cwp",
        "cwp_root",
        "state_str",
        "symbol_table",
    ]

    def __init__(self) -> None:
        self.behavior_str: Result[str, Error] = Failure(Error())
        self.bpmn: Result[Bpmn, Error] = Failure(Error())
        self.bpmn_root: Result[Element, Error] = Failure(Error())
        self.cwp: Result[Cwp, Error] = Failure(Error())
        self.cwp_root: Result[Element, Error] = Failure(Error())
        self.state_str: Result[str, Error] = Failure(Error())
        self.symbol_table: Result[State, Error] = Failure(Error())

    @staticmethod
    def _build_bpmn(builder: "Builder") -> Result["Builder", Error]:
        assert is_successful(builder.symbol_table) and is_successful(builder.bpmn_root)
        builder.bpmn = bpmn_from_xml(
            builder.bpmn_root.unwrap(), builder.symbol_table.unwrap()
        )
        if not_(is_successful)(builder.bpmn):
            return Failure(builder.bpmn.failure())
        else:
            return Success(builder)

    @staticmethod
    def _build_cwp(builder: "Builder") -> Result["Builder", Error]:
        assert is_successful(builder.symbol_table)
        assert is_successful(builder.cwp_root)
        builder.cwp = cwp_from_xml(
            builder.cwp_root.unwrap(), builder.symbol_table.unwrap()
        )
        if not_(is_successful)(builder.cwp):
            return Failure(builder.cwp.failure())
        else:
            return Success(builder)

    @staticmethod
    def _build_symbol_table(builder: "Builder") -> Result["Builder", Error]:
        assert is_successful(builder.state_str)
        builder.symbol_table = State.from_str(builder.state_str.unwrap())
        if not_(is_successful)(builder.symbol_table):
            return Failure(builder.symbol_table.failure())
        else:
            return Success(builder)

    @staticmethod
    def build_promela(
        outputs: "Outputs", builder: "Builder"
    ) -> Result["Outputs", Error]:
        assert is_successful(builder.symbol_table)
        assert is_successful(builder.cwp_root)
        assert is_successful(builder.bpmn_root)
        assert is_successful(builder.behavior_str)

        ltl = generate_ltl((builder.cwp).unwrap(), (builder.symbol_table).unwrap())
        behavior = (builder.behavior_str).unwrap()
        workflow = generate_promela((builder.bpmn).unwrap())

        outputs.promela = f"{ltl}{behavior}{workflow}"
        return Success(outputs)

    def build(self) -> Result["Outputs", Error]:
        outputs: Outputs = Outputs("")
        result: Result["Outputs", Error] = flow(
            Success(self),
            bind_result(Builder._build_symbol_table),
            bind_result(Builder._build_cwp),
            bind_result(Builder._build_bpmn),
            bind_result(partial(Builder.build_promela, outputs)),
        )

        return result

    def with_behavior(self, behavior_str: str) -> "Builder":
        self.behavior_str = Success(behavior_str)
        return self

    def with_bpmn(self, bpmn: Element) -> "Builder":
        self.bpmn_root = Success(bpmn)
        return self

    def with_cwp(self, cwp: Element) -> "Builder":
        self.cwp_root = Success(cwp)
        return self

    def with_state(self, state: str) -> "Builder":
        self.state_str = Success(state)
        return self

    @staticmethod
    def build_(builder: "Builder") -> Result["Outputs", Error | Exception]:
        return builder.build()

    @staticmethod
    def with_behavior_(
        behavior_str: IOResultE[str],
        builder_result: Result["Builder", Error],
    ) -> Result["Builder", Error]:
        if not_(is_successful)(builder_result):
            return builder_result
        if not_(is_successful)(behavior_str):
            error = unsafe_perform_io(behavior_str.failure())
            return Failure(ExceptionError(str(error)))

        bpmn = Success(unsafe_perform_io(behavior_str.unwrap()))
        builder = builder_result.unwrap()
        return bpmn.map(builder.with_behavior)

    @staticmethod
    def with_bpmn_(
        bpmn_root: IOResultE[Element],
        builder_result: Result["Builder", Error],
    ) -> Result["Builder", Error]:
        if not_(is_successful)(builder_result):
            return builder_result
        if not_(is_successful)(bpmn_root):
            error = unsafe_perform_io(bpmn_root.failure())
            return Failure(ExceptionError(str(error)))

        bpmn = Success(unsafe_perform_io(bpmn_root.unwrap()))
        builder = builder_result.unwrap()
        return bpmn.map(builder.with_bpmn)

    @staticmethod
    def with_cwp_(
        cwp_root: IOResultE[Element],
        builder_result: Result["Builder", Error],
    ) -> Result["Builder", Error]:
        if not_(is_successful)(builder_result):
            return builder_result
        if not_(is_successful)(cwp_root):
            error = unsafe_perform_io(cwp_root.failure())
            return Failure(ExceptionError(str(error)))

        cwp = Success(unsafe_perform_io(cwp_root.unwrap()))
        builder = builder_result.unwrap()
        return cwp.map(builder.with_cwp)

    @staticmethod
    def with_state_(
        state_str: IOResultE[str], builder_result: Result["Builder", Error]
    ) -> Result["Builder", Error]:
        if not_(is_successful)(builder_result):
            return builder_result
        if not_(is_successful)(state_str):
            error = unsafe_perform_io(state_str.failure())
            return Failure(ExceptionError(str(error)))

        builder = builder_result.unwrap()
        state = Success(unsafe_perform_io(state_str.unwrap()))
        return state.map(builder.with_state)


class Outputs:
    __slots__ = ["promela"]

    def __init__(self, promela: str) -> None:
        self.promela = promela
