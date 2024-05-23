import re


class TokenType:
    NUM, STR, VAR, GT, GTE, LT, LTE, EQ, NEQ, LP, RP, AND, OR, PAREN = range(14)
    INVALID = -1
    OPERATOR = [GT, GTE, LT, LTE, EQ, NEQ]
    COMPARER = [GT, GTE, LT, LTE]


class Token:
    def __init__(self, value, type=TokenType.INVALID):
        self.value = value
        self.type = type

    def __repr__(self):
        return "value: {}".format(
            self.value,
        )


class TreeNode:
    def __init__(
        self, value=None, type=TokenType.INVALID, left=None, right=None
    ) -> None:
        self.value = value
        self.type = type
        self.left = left
        self.right = right

    def __repr__(self):
        left = str(self.left) if self.left else ""
        right = str(self.right) if self.right else ""
        if self.type == TokenType.PAREN:
            return "({})".format(left)
        return left + self.value + right


class ExpressionParser:
    def __init__(self, varList=None):
        self.tokenQueue = None
        if varList:
            self.varList = varList
        else:
            self.varList = []
        self.root = None

    def setVarList(self, varList):
        self.varList = varList

    def execute(self, expression):
        self.tokenQueue = []
        self.tokenize(expression)
        self.root = self.parseExpression()
        return self.root

    def parseExpression(self):
        andExpr1 = self.parseAndExpression()
        if self.tokenQueue:
            if self.tokenQueue[-1].type == TokenType.OR:
                self.tokenQueue.pop()
                andExprX = self.parseAndExpression()
                andExpr = TreeNode(
                    value="||", type=TokenType.OR, left=andExpr1, right=andExprX
                )
                andExpr1 = andExpr
        return andExpr1

    def parseAndExpression(self):
        cond1 = self.parseCondition()
        if self.tokenQueue:
            if self.tokenQueue[-1].type == TokenType.AND:
                self.tokenQueue.pop()
                condX = self.parseCondition()
                cond = TreeNode(value="&&", type=TokenType.AND, left=cond1, right=condX)
                cond1 = cond
        return cond1

    def parseCondition(self):
        # Parenthases
        if self.tokenQueue:
            if self.tokenQueue[-1].type == TokenType.LP:
                self.tokenQueue.pop()
                expr = self.parseExpression()
                if self.tokenQueue[-1].type == TokenType.RP:
                    self.tokenQueue.pop()
                    expr2 = TreeNode(type=TokenType.PAREN, left=expr)
                    return expr2
                else:
                    tok = self.tokenQueue.pop()
                    raise Exception("Expected closing ) but got {}".format(tok.value))

        # Terminal Operator Terminal
        terminal1 = self.parseTerminal()
        if self.tokenQueue:
            if self.tokenQueue[-1].type in TokenType.OPERATOR:
                tok = self.tokenQueue.pop()
                terminal2 = self.parseTerminal()
                operation = TreeNode(
                    value=tok.value, type=tok.type, left=terminal1, right=terminal2
                )
                term1Type = next(
                    (
                        var.type
                        for var in self.varList
                        if var.cwp == terminal1.value or var.bpmn == terminal1.value
                    ),
                    None,
                )
                term2Type = next(
                    (
                        var.type
                        for var in self.varList
                        if var.cwp == terminal2.value or var.bpmn == terminal2.value
                    ),
                    None,
                )
                if terminal1.type == TokenType.NUM and terminal2.type == TokenType.NUM:
                    raise Exception(
                        "Why are you comparing two numbers? {}".format(
                            terminal1.value + tok.value + terminal2.value
                        )
                    )
                elif terminal1.type == TokenType.NUM and term2Type not in [
                    "int",
                    "byte",
                    "short",
                ]:
                    raise Exception(
                        "Type mismatch: {}".format(
                            terminal1.value + tok.value + terminal2.value
                        )
                    )
                elif terminal2.type == TokenType.NUM and term1Type not in [
                    "int",
                    "byte",
                    "short",
                ]:
                    raise Exception(
                        "Type mismatch: {}".format(
                            terminal1.value + tok.value + terminal2.value
                        )
                    )
                elif term1Type != term2Type:
                    raise Exception(
                        "Type mismatch: {}".format(
                            terminal1.value + tok.value + terminal2.value
                        )
                    )

                if tok.type in TokenType.COMPARER:
                    if term1Type in ["enum", "bool"]:
                        raise Exception(
                            "Can't compare Enum or Bool: {}".format(
                                terminal1.value + tok.value + terminal2.value
                            )
                        )
                    elif term2Type in ["enum", "bool"]:
                        raise Exception(
                            "Can't compare Enum or Bool: {}".format(
                                terminal1.value + tok.value + terminal2.value
                            )
                        )
                return operation

            else:
                tok = self.tokenQueue.pop()
                raise Exception("Expected an Operator, got {}".format(tok.value))

    def parseTerminal(self):
        if self.tokenQueue:
            if self.tokenQueue[-1].type == TokenType.NUM:
                tok = self.tokenQueue.pop()
                n = TreeNode(value=int(tok.value))
                return n
            elif TokenType.VAR:
                tok = self.tokenQueue.pop()
                n = TreeNode(value=tok.value, type=tok.type)
                return n
            elif self.tokenQueue[-1].type == TokenType.STR:
                raise Exception("String variable type not supported in SPIN")
            else:
                raise Exception("terminal expected, got {}".format(tok.value))
        else:
            raise Exception("expected a terminal, got nothing instead")

    def tokenize(self, expression):
        regex = re.compile(r"(&&|\|\||!=|==|<=|>=|<|>|\(|\))")
        self.tokenStrings = regex.split(expression)
        self.tokenStrings.reverse()
        for item in self.tokenStrings:
            token = Token(value=item.strip())
            if token.value == "":
                continue
            elif token.value == "&&":
                token.type = TokenType.AND
            elif token.value == "||":
                token.type = TokenType.OR
            elif token.value == "(":
                token.type = TokenType.LP
            elif token.value == ")":
                token.type = TokenType.RP
            elif token.value == "<":
                token.type = TokenType.LT
            elif token.value == ">":
                token.type = TokenType.GT
            elif token.value == "<=":
                token.type = TokenType.LTE
            elif token.value == ">=":
                token.type = TokenType.GTE
            elif token.value == "==":
                token.type = TokenType.EQ
            elif token.value == "!=":
                token.type = TokenType.NEQ
            else:
                if token.value[0] == '"' and token.value[-1] == '"':
                    token.type = TokenType.STR
                elif token.value.isdigit():
                    token.type = TokenType.NUM
                elif re.search("^[a-zA-Z][a-zA-Z0-9_]+$", token.value):
                    token.type = TokenType.VAR
                    if token.value not in [
                        var.cwp for var in self.varList
                    ] and token.value not in [var.bpmn for var in self.varList]:
                        raise Exception("Variable not in list: {}".format(token.value))

            if token.type == TokenType.INVALID:
                raise Exception("Invalid Token: {}".format(token.value))
            else:
                self.tokenQueue.append(token)


if __name__ == "__main__":
    parser = ExpressionParser()
    parser.setVarList(["hello", "thi3s", "that", "True", "False"])
    root = parser.execute("((hello==True) && that == True)")
    print(root)
