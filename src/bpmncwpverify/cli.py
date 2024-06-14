# Imports from refactor
import argparse
from returns.io import IOResultE, impure_safe
from typing import TextIO
from returns.pipeline import managed, flow
from returns.result import ResultE


def _get_argument_parser():
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


def verify():
    argument_parser = _get_argument_parser()
    args = argument_parser.parse_args()
    managed_read = managed(_read_file, _close_file)

    state: IOResultE[str] = flow(
        args.statefile,
        impure_safe(lambda filename: open(filename, "r")),
        managed_read,
        # bind_result(parse_toml), <== replace with a from_str method for the state (e.g., the state ingester)
        # bind_result(get_project_name)
    )

    # Add tests for the StateIngester
    # Repeat the above for the CWP and BPMN but include the validatation in the flow (move to separate method)
    print(state)


def generate_stubs():
    """Generate behavior stubs for the BPMN workflow"""
    return
