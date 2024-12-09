# Imports from refactor
import argparse
from bpmncwpverify.core.promcreate import create_promela, write_promela
from returns.io import impure_safe, IOResult, IOResultE

from returns.pipeline import managed, flow
from returns.pointfree import bind_result
from returns.curry import partial
from returns.result import ResultE, Result, Success, Failure
from typing import TextIO

from bpmncwpverify.error import Error, get_error_message
from bpmncwpverify.core.state import SymbolTable


def _get_argument_parser() -> "argparse.ArgumentParser":
    argument_parser = argparse.ArgumentParser(
        description="Verify the BPMN is a safe substitution for the CWP given the state"
    )
    # Rework to not do the type conversion for the file. Rather use the `managed` from returns. impure_safe open the files and then managed to return and close.
    # See the example in pipelines https://returns.readthedocs.io/en/latest/pages/pipeline.html
    argument_parser.add_argument(
        "statefile",
        help="State definition text file",
    )
    argument_parser.add_argument(
        "cwpfile",
        help="CWP state machine file in XML",
    )
    argument_parser.add_argument(
        "bpmnfile",
        help="BPMN workflow file in XML",
    )
    argument_parser.add_argument(
        "behaviorfile",
        help="Behavior models file in Promela",
    )
    return argument_parser


def _read_file(file_obj: TextIO) -> IOResultE[str]:
    return impure_safe(file_obj.read)()


def _close_file(
    file_obj: TextIO,
    file_contents: ResultE[str],
) -> IOResultE[None]:
    return impure_safe(file_obj.close)()


def verify() -> None:
    argument_parser = _get_argument_parser()
    args = argument_parser.parse_args()
    managed_read = managed(_read_file, _close_file)
    state_filename: str = args.statefile
    bpmn_filename: str = args.bpmnfile
    cwp_filename: str = args.cwpfile

    prom_create = partial(create_promela, cwp_filename, bpmn_filename)

    write_file = partial(write_promela, "output.pml")
    result: IOResultE[Result[SymbolTable, Error]] = flow(
        state_filename,
        impure_safe(lambda filename: open(filename, "r")),
        managed_read,
        bind_result(SymbolTable.build),
        bind_result(prom_create),
        bind_result(write_file),
    )

    match result:
        case IOResult(Success(success)):
            print(success)
        case IOResult(Failure(error)):
            msg = get_error_message(error)
            print(msg)
        case IOResult(other):
            print(other)

    # Add tests for the StateIngester
    # Repeat the above for the CWP and BPMN but include the validatation in the flow (move to separate method)
    # print(state)


def generate_stubs() -> None:
    """Generate behavior stubs for the BPMN workflow"""
    pass
