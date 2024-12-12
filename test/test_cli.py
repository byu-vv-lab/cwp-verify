# type: ignore
import sys
from returns.pipeline import is_successful
from returns.functions import not_

from bpmncwpverify.cli import _verify
from bpmncwpverify.error import StateSyntaxError, ExceptionError


def test_givin_bad_state_file_path_when_verify_then_io_error(capsys):
    # given
    test_args = [
        "verify",
        "state.txt",
        "./test/resources/test_cwp.xml",
        "./test/resources/test_bpmn.bpmn",
        "./test/resources/behavior.txt",
    ]
    sys.argv = test_args

    # when
    result = _verify()

    # then
    assert not_(is_successful)(result)
    error = result.failure()
    assert isinstance(error, ExceptionError)
    assert "state.txt" in error.exception_str


def test_givin_bad_cwp_file_path_when_verify_then_io_error(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/state.txt",
        "test_cwp.xml",
        "./test/resources/test_bpmn.bpmn",
        "./test/resources/behavior.txt",
    ]
    sys.argv = test_args

    # when
    result = _verify()

    # then
    assert not_(is_successful)(result)
    error = result.failure()
    assert isinstance(error, ExceptionError)
    assert "test_cwp.xml" in error.exception_str


def test_givin_bad_bpmn_file_path_when_verify_then_io_error(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/state.txt",
        "./test/resources/test_cwp.xml",
        "test_bpmn.bpmn",
        "./test/resources/behavior.txt",
    ]
    sys.argv = test_args

    # when
    result = _verify()

    # then
    assert not_(is_successful)(result)
    error = result.failure()
    assert isinstance(error, ExceptionError)
    assert "test_bpmn.bpmn" in error.exception_str


def test_givin_bad_behavior_file_path_when_verify_then_io_error(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/state.txt",
        "./test/resources/test_cwp.xml",
        "./test/resources/test_bpmn.bpmn",
        "behavior.txt",
    ]
    sys.argv = test_args

    # when
    result = _verify()

    # then
    assert not_(is_successful)(result)
    error = result.failure()
    assert isinstance(error, ExceptionError)
    assert "behavior.txt" in error.exception_str


def test_givin_bad_state_file_when_verify_then_state_errror(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/bad_state.txt",
        "./test/resources/test_cwp.xml",
        "./test/resources/test_bpmn.bpmn",
        "./test/resources/behavior.txt",
    ]
    sys.argv = test_args

    # when
    result = _verify()

    # then
    assert not_(is_successful)(result)
    error = result.failure()
    assert isinstance(error, StateSyntaxError)


def test_givin_good_files_when_verify_then_output_promela(capsys):
    # given
    test_args = [
        "verify",
        "./test/resources/state.txt",
        "./test/resources/test_cwp.xml",
        "./test/resources/test_bpmn.bpmn",
        "./test/resources/behavior.txt",
    ]
    sys.argv = test_args

    # when
    result = _verify()

    # then
    assert is_successful(result)
    outputs = result.unwrap()
    assert outputs.promela is not None
    assert outputs.promela != ""
