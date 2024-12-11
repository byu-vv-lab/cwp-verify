# TODO: create a "match" function on Failure(Error) and create standard error messaging.
import typing
import builtins
from xml.etree.ElementTree import Element


class Error:
    def __init__(self) -> None:
        pass


class BpmnStructureError(Error):
    __slots__ = ["node_id", "error_msg"]

    def __init__(self, node_id: str, error_msg: str) -> None:
        super().__init__()
        self.node_id = node_id
        self.error_msg = error_msg


class ExpressionComputationCompatabilityError(Error):
    __slots__ = ["ltype", "rtype"]

    def __init__(self, ltype: str, rtype: str) -> None:
        super().__init__()
        self.ltype = ltype
        self.rtype = rtype

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, ExpressionComputationCompatabilityError):
            return self.ltype == other.ltype and self.rtype == other.rtype
        return False


class ExpressionNegatorError(Error):
    __slots__ = ["_type"]

    def __init__(self, type: str) -> None:
        super().__init__()
        self._type = type

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, ExpressionNegatorError):
            return self._type == other._type
        return False


class ExpressionRelationCompatabilityError(Error):
    __slots__ = ["ltype", "rtype"]

    def __init__(self, ltype: str, rtype: str) -> None:
        super().__init__()
        self.ltype = ltype
        self.rtype = rtype

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, ExpressionComputationCompatabilityError):
            return self.ltype == other.ltype and self.rtype == other.rtype
        return False


class ExpressionRelationalNotError(Error):
    __slots__ = ["_type"]

    def __init__(self, type: str) -> None:
        super().__init__()
        self._type = type

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, ExpressionRelationalNotError):
            return self._type == other._type
        return False


class ExpressionUnrecognizedID(Error):
    __slots__ = ["_id"]

    def __init__(self, id: str) -> None:
        super().__init__()
        self._id = id

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, ExpressionUnrecognizedID):
            return self._id == other._id
        return False


class BpmnFlowIncomingError(Error):
    __slots__ = ["node_id"]

    def __init__(self, node_id: str) -> None:
        super().__init__()
        self.node_id = node_id


class BpmnFlowNoIdError(Error):
    __slots__ = ["element"]

    def __init__(self, element: Element) -> None:
        super().__init__()
        self.element = element


class BpmnFlowTypeError(Error):
    __slots__ = ["flow_id"]

    def __init__(self, flow_id: str) -> None:
        super().__init__()
        self.flow_id = flow_id


class BpmnGraphConnError(Error):
    def __init__(self) -> None:
        super().__init__()


class BpmnMissingEventsError(Error):
    __slots__ = ["start_events", "end_events"]

    def __init__(self, start_events: int, end_events: int) -> None:
        super().__init__()
        self.start_events = start_events
        self.end_events = end_events


class BpmnMsgEndEventError(Error):
    __slots__ = ["event_id"]

    def __init__(self, event_id: str) -> None:
        super().__init__()
        self.event_id = event_id


class BpmnMsgFlowSamePoolError(Error):
    __slots__ = ["msg_id"]

    def __init__(self, msg_id: str) -> None:
        super().__init__()
        self.msg_id = msg_id


class BpmnMsgGatewayError(Error):
    __slots__ = ["gateway_type", "gateway_id"]

    def __init__(self, gateway_type: str, gateway_id: str) -> None:
        super().__init__()
        self.gateway_type = gateway_type
        self.gateway_id = gateway_id


class BpmnMsgMissingRefError(Error):
    __slots__ = ["msg_id"]

    def __init__(self, msg_id: str) -> None:
        super().__init__()
        self.msg_id = msg_id


class BpmnMsgNodeTypeError(Error):
    __slots__ = ["msg_id"]

    def __init__(self, msg_id: str) -> None:
        super().__init__()
        self.msg_id = msg_id


class BpmnMsgSrcError(Error):
    __slots__ = ["obj_type", "node_id"]

    def __init__(self, obj_type: str, node_id: str) -> None:
        super().__init__()
        self.obj_type = obj_type
        self.node_id = node_id


class BpmnMsgTargetError(Error):
    __slots__ = ["obj_type", "node_id"]

    def __init__(self, obj_type: str, node_id: str) -> None:
        super().__init__()
        self.obj_type = obj_type
        self.node_id = node_id


class BpmnNodeTypeError(Error):
    __slots__ = ["flow_id"]

    def __init__(self, flow_id: str) -> None:
        super().__init__()
        self.flow_id = flow_id


class BpmnSeqFlowEndEventError(Error):
    __slots__ = ["event_id"]

    def __init__(self, event_id: str) -> None:
        super().__init__()
        self.event_id = event_id


class BpmnSeqFlowNoExprError(Error):
    __slots__ = ["gateway_id", "out_flow_id"]

    def __init__(self, gateway_id: str, out_flow_id: str) -> None:
        super().__init__()
        self.gateway_id = gateway_id
        self.out_flow_id = out_flow_id


class BpmnTaskFlowError(Error):
    __slots__ = ["task_id"]

    def __init__(self, task_id: str) -> None:
        super().__init__()
        self.task_id = task_id


class CwpEdgeNoParentExprError(Error):
    __slots__ = ["edge"]

    def __init__(self, edge: Element) -> None:
        super().__init__()
        self.edge = edge


class CwpEdgeNoStateError(Error):
    __slots__ = ["edge"]

    def __init__(self, edge: Element) -> None:
        super().__init__()
        self.edge = edge


class CwpGraphConnError(Error):
    def __init__(self) -> None:
        super().__init__()


class CwpMultStartStateError(Error):
    __slots__ = ["start_states"]

    def __init__(self, start_states: typing.List[str]) -> None:
        super().__init__()
        self.start_states = start_states


class CwpFileStructureError(Error):
    __slots__ = ["element"]

    def __init__(self, element: str) -> None:
        super().__init__()
        self.element = element


class CwpNoEndStatesError(Error):
    def __init__(self) -> None:
        super().__init__()


class CwpNoParentEdgeError(Error):
    __slots__ = ["edge"]

    def __init__(self, edge: Element) -> None:
        super().__init__()
        self.edge = edge


class CwpNoStartStateError(Error):
    def __init__(self) -> None:
        super().__init__()


class NotImplementedError(Error):
    __slots__ = ["function"]

    def __init__(self, function: str) -> None:
        super().__init__()
        self.function = function


class MessageError(Error):
    __slots__ = ["node_id", "error_msg"]

    def __init__(self, node_id: str, error_msg: str) -> None:
        super().__init__()
        self.node_id = node_id
        self.error_msg = error_msg


class StateInitNotInValues(Error):
    __slots__ = ["id", "line", "column", "values"]

    def __init__(self, id: str, line: int, column: int, values: set[str]) -> None:
        super().__init__()
        self.id = id
        self.line = line
        self.column = column
        self.values = values

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, StateInitNotInValues):
            return (
                self.id == other.id
                and self.line == other.line
                and self.column == other.column
                and self.values == other.values
            )
        return False


class StateMultipleDefinitionError(Error):
    __slots__ = ("id", "line", "column", "prev_line", "prev_column")

    def __init__(
        self, id: str, line: int, column: int, prev_line: int, prev_column: int
    ) -> None:
        super().__init__()
        self.id = id
        self.line = line
        self.column = column
        self.prev_line = prev_line
        self.prev_column = prev_column

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, StateMultipleDefinitionError):
            return (
                self.id == other.id
                and self.line == other.line
                and self.column == other.column
                and self.prev_line == other.prev_line
                and self.prev_column == other.prev_column
            )
        return False


class StateSyntaxError(Error):
    __slots__ = "msg"

    def __init__(self, msg: str) -> None:
        self.msg = msg
        super().__init__()


class TypingAssignCompatabilityError(Error):
    __slots__ = ["ltype", "rtype"]

    def __init__(self, ltype: str, rtype: str) -> None:
        super().__init__()
        self.ltype = ltype
        self.rtype = rtype

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, TypingAssignCompatabilityError):
            return self.ltype == other.ltype and self.rtype == other.rtype
        return False


class TypingNoTypeError(Error):
    __slots__ = ["id"]

    def __init__(self, id: str) -> None:
        super().__init__()
        self.id = id

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, TypingNoTypeError):
            return self.id == other.id
        return False


class TypingNegateBoolError(Error):
    __slots__ = ["expr_type"]

    def __init__(self, expr_type: str) -> None:
        super().__init__()
        self.expr_type = expr_type


class TypingNotNonBoolError(Error):
    __slots__ = ["expr_type"]

    def __init__(self, expr_type: str) -> None:
        super().__init__()
        self.expr_type = expr_type


def _get_exception_message(error: Exception) -> str:
    return "ERROR: {0} ({1})".format(type(error), error)


def _get_error_message(error: Error) -> str:
    match error:
        case BpmnStructureError(node_id=node_id, error_msg=error_msg):
            return f"BPMN ERROR at node: {node_id}. {error_msg}"
        case ExpressionComputationCompatabilityError(ltype=ltype, rtype=rtype):
            return "EXPR ERROR: sometion of type '{}' cannot be computed with something of type '{}'".format(
                rtype, ltype
            )
        case ExpressionNegatorError(_type=_type):
            return "EXPR ERROR: sometiong of type '{}' cannot be used with a mathmatical negator".format(
                _type
            )
        case ExpressionRelationCompatabilityError(ltype=ltype, rtype=rtype):
            return "EXPR ERROR: sometion of type '{}' cannot be related with something of type '{}'".format(
                rtype, ltype
            )
        case ExpressionRelationalNotError(_type=_type):
            return "EXPR ERROR: sometiong of type '{}' cannot be used with a relational not".format(
                _type
            )
        case ExpressionUnrecognizedID(_id=_id):
            return "EXPR ERROR: '{}' is not recognized as a literal or something stored in the symbol table".format(
                _id
            )
        case NotImplementedError(function=function):
            return "ERROR: not implemented '{}'".format(function)
        case MessageError(node_id=node_id, error_msg=error_msg):
            return f"Inter-process message error at node: {node_id}. {error_msg}"
        case BpmnFlowIncomingError(node_id=node_id):
            return f"Flow error: No incoming flow into node: {node_id}."
        case BpmnFlowNoIdError(element=element):
            return f"Flow error: Flow_id does not exist. Occurred at tree element with following attributes: {element.attrib}."
        case BpmnFlowTypeError(flow_id=flow_id):
            return f"Flow error: Flow '{flow_id}' is not a sequence flow when it should be."
        case BpmnNodeTypeError(flow_id=flow_id):
            return f"Node type error: Source or target node of flow is not of type node. Flow details: {flow_id}."
        case BpmnMsgFlowSamePoolError(msg_id=msg_id):
            return f"Message flow error: {msg_id} connects nodes in the same pool."
        case BpmnMsgMissingRefError(msg_id=msg_id):
            return f"Message flow error: Source ref or target ref is missing for message '{msg_id}'."
        case BpmnMsgNodeTypeError(msg_id=msg_id):
            return f"Message flow error: 'From' node and 'To' node of message are not of type Node. Message flow id: {msg_id}."
        case BpmnMsgTargetError(obj_type=obj_type, node_id=node_id):
            return f"Message flow target error while visiting {obj_type}. A message flow can only go to a Message start or intermediate event; Receive, User, or Service task; Subprocess; or black box pool. Node ID: {node_id}."
        case BpmnMsgSrcError(obj_type=obj_type, node_id=node_id):
            return f"Message flow source error while visiting {obj_type}. A message flow can only come from specific sources. Node ID: {node_id}."
        case BpmnMsgEndEventError(event_id=event_id):
            return f"Message flow error: End events cannot have incoming messages. Event ID: {event_id}."
        case BpmnMsgGatewayError(gateway_type=gateway_type, gateway_id=gateway_id):
            return f"Gateway error: {gateway_type} gateways cannot have incoming or outgoing messages. Gateway ID: {gateway_id}."
        case BpmnSeqFlowEndEventError(event_id=event_id):
            return f"Sequence flow error: End event '{event_id}' cannot have outgoing sequence flows."
        case BpmnTaskFlowError(task_id=task_id):
            return f"Task flow error: Task '{task_id}' should have at least one incoming and one outgoing flow."
        case BpmnSeqFlowNoExprError(gateway_id=gateway_id, out_flow_id=out_flow_id):
            return f"Flow: `{out_flow_id}` does not have an expression. All flows coming out of gateways must have expressions. Gateway id: {gateway_id}"
        case BpmnMissingEventsError(start_events=start_events, end_events=end_events):
            return f"Event error: Start events = {start_events}, End events = {end_events}. Missing required start or end events."
        case BpmnGraphConnError():
            return "Bpmn Process graph error: Process graph is not fully connected."
        case CwpEdgeNoStateError(edge=edge):
            return f"CWP ERROR: Edge does not have a source or a target. Edge details: {edge.attrib}."
        case CwpEdgeNoParentExprError(edge=edge):
            return f"CWP ERROR: Expression or parent node not found in edge. Edge details: {edge.attrib}."
        case CwpNoParentEdgeError(edge=edge):
            return f"CWP ERROR: Parent edge not found or no parent ID reference. Edge details: {edge.attrib}."
        case CwpMultStartStateError(start_states=start_states):
            return f"CWP ERROR: More than one start state found. Start state IDs: {start_states}."
        case CwpNoStartStateError():
            return "CWP ERROR: No start states found."
        case CwpFileStructureError(element=element):
            return f"A {element} element is missing from your cwp file."
        case CwpNoEndStatesError():
            return "CWP ERROR: No end states found."
        case CwpGraphConnError():
            return "CWP ERROR: Graph is not connected."
        case StateInitNotInValues(id=id, line=line, column=column, values=values):
            # Convert to a list since Python sets are not stable
            return "STATE ERROR: init value '{}' at line {}:{} not in allowed values {}".format(
                id, line, column, sorted(values)
            )
        case StateMultipleDefinitionError(
            id=id,
            line=line,
            column=column,
            prev_line=prev_line,
            prev_column=prev_column,
        ):
            return "STATE ERROR: multiple definition of '{}' at line {}:{}, previously defined at line {}:{}".format(
                id, line, column, prev_line, prev_column
            )
        case StateSyntaxError(msg=msg):
            return "STATE SYNTAX ERROR: {}".format(msg)
        case TypingAssignCompatabilityError(ltype=ltype, rtype=rtype):
            return "TYPING ERROR: something of type '{}' cannot by assigned to something of type '{}'".format(
                rtype, ltype
            )
        case TypingNoTypeError(id=id):
            return "TYPING ERROR: literal '{}' has an unknown type".format(id)
        case _:
            raise builtins.NotImplementedError


def get_error_message(error: Error | Exception) -> str:
    match error:
        case Exception():
            return _get_exception_message(error)
        case Error():
            return _get_error_message(error)
