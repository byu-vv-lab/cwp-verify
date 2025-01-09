import argparse
from defusedxml import ElementTree
from xml.etree.ElementTree import Element

from bpmncwpverify.core.spin import Builder, Outputs
from returns.io import impure_safe, IOResultE
from returns.curry import partial
from returns.pipeline import managed, flow
from returns.pointfree import bind_result
from returns.result import ResultE, Result, Success, Failure

from typing import TextIO, cast

from bpmncwpverify.core.error import Error, get_error_message


def element_tree_from_string(input: str) -> Element:
    return cast(Element, ElementTree.fromstring(input))  # type: ignore[unused-ignore]


def _close_file(
    file_obj: TextIO,
    file_contents: ResultE[str],
) -> IOResultE[None]:
    return impure_safe(file_obj.close)()


def _get_argument_parser() -> "argparse.ArgumentParser":
    argument_parser = argparse.ArgumentParser(
        description="Verify the BPMN is a safe substitution for the CWP given the state"
    )

    argument_parser.add_argument(
        "state_file",
        help="State definition text file",
    )
    argument_parser.add_argument(
        "cwp_file",
        help="CWP state machine file in XML",
    )
    argument_parser.add_argument(
        "bpmn_file",
        help="BPMN workflow file in XML",
    )
    argument_parser.add_argument(
        "behavior_file",
        help="Behavior models file in Promela",
    )
    return argument_parser


def _get_file_contents(name: str) -> IOResultE[str]:
    return flow(
        name,
        impure_safe(lambda filename: open(filename, "r")),  # type: ignore[unused-ignore]
        managed(_read_file, _close_file),
    )


def _read_file(file_obj: TextIO) -> IOResultE[str]:
    return impure_safe(file_obj.read)()


def _verify() -> Result["Outputs", Error]:
    argument_parser = _get_argument_parser()
    args = argument_parser.parse_args()
    state_str = _get_file_contents(args.state_file)
    bpmn_root: IOResultE[Element] = _get_file_contents(args.bpmn_file).map(
        element_tree_from_string
    )
    cwp_root: IOResultE[Element] = _get_file_contents(args.cwp_file).map(
        element_tree_from_string
    )
    behavior_str = _get_file_contents(args.behavior_file)

    builder: Builder = Builder()

    result: Result["Outputs", Error] = flow(
        Success(builder),
        partial(Builder.with_state_, state_str),
        partial(Builder.with_cwp_, cwp_root),
        partial(Builder.with_bpmn_, bpmn_root),
        partial(Builder.with_behavior_, behavior_str),
        bind_result(Builder.build_),
    )

    return result


def verify() -> None:
    result: Result[Outputs, Error] = _verify()

    match result:
        case Success(o):
            print(o.promela)
        case Failure(e):
            msg = get_error_message(e)
            print(msg)
        case _:
            assert False, "ERROR: unhandled type"


def generate_stubs() -> None:
    """Generate behavior stubs for the BPMN workflow"""
    pass
