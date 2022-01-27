import re

class Function():
    def __init__(self, name, retType, arguments, body):
        self.name = name
        self.retType = retType
        self.arguments = arguments
        self.body = body

    def __str__(self):
        return self.name + ": " + str(self.arguments) + " -> " + self.retType

class Fact():
    def __init__(self, name, header, body, variables):
        self.name = name
        self.header= header
        self.body = body
        self.variables = variables

    def __str__(self):
        return self.name + ": " + self.header

    def eldaricaModel(self):
        newbody = [self.header]
        
        for l in self.body:
           if isFact(l):
                # We need to change facts to asserts
                (ws, retExp) = isFact(l)
                newbody.append(ws + "assert(" + retExp + "); // AUTO-GENERATED")
           elif isAssume(l):
                # We need to change facts to asserts
                (ws, retExp) = isAssume(l)
                newbody.append(ws + "assume(" + retExp + "); // AUTO-GENERATED")
           else:
                newbody.append(l)

        return "\n".join(newbody)

    def cbmcModel(self):
        newbody = [self.header]

        for l in self.body:
           if isFact(l):
                # We need to change facts to asserts
                (ws, retExp) = isFact(l)
                newbody.append(ws + "__CPROVER_assert(" + retExp + ", \"test\"); // AUTO-GENERATED")
           elif isAssume(l):
                (ws, retExp) = isAssume(l)
                newbody.append(ws + "__CPROVER_assume(" + retExp + "); // AUTO-GENERATED")
           elif isIntVariable(l):
               (ws, name, value) = isIntVariable(l)
               if value == "_":
                   newbody.append(ws + "int " + name + " = int_nondet();")
               else:
                   newbody.append(ws + "int " + name + " = " + value + ";")
           else:
                newbody.append(l)

        return "\n".join(newbody)



    #### TODO: What if we have nested constraints, calls, etc.
    #### TODO: The replacement of arguments is not good
    def find_call(self, fun):
        constraints = []
        calls = []
        for b in self.body:
            if containsCall(b, fun):
                args = containsCall(b, fun)
                normConstraints = []
                for c in constraints:
                    ctmp = c
                    for i, arg in enumerate(args):
                        ctmp = ctmp.replace(arg, "ARG" + str(i))
                    normConstraints.append("(" + ctmp + ")")
                calls.append(" && ".join(normConstraints))
            if isIntVariable(b):
                (_, var, val) = isIntVariable(b)
                if not val == "_":
                    constraints.append(var + " = " + val)
            if isAssume(b):
                (_, formula) = isAssume(b)
                constraints.append(formula)

        return calls

def isFunDeclaration(line):
    r1 = re.findall("(int) (.*)\\((.*)\\)", line)
    if r1:
        returnType = r1[0][0]
        funName = r1[0][1]
        arguments = list(map(lambda x : x.strip(), r1[0][2].split(",")))
        return (returnType, funName, arguments)
    else:
        return None

    # TODO: How come if we have an integer fact it shows up in the list of facts?
def isFactDeclaration(line):
    r1 = re.findall("(void) (.*)\\(\\)", line)
    if r1:
        returnType = r1[0][0]
        funName = r1[0][1]
        return (returnType, funName)
    else:
        return None

def isIntVariable(line):
    r = re.fullmatch("(\s*)int (\S*)\s*=\s*(.*);", line)
    if r:
        ws = r[1]
        name = r[2]
        value = r[3]
        return (ws, name, value)
    else:
        return None


def parse_functions(filename):
    file1 = open(filename, 'r')
    lines = file1.readlines()

    functions = {}
    lastFunctionBody = []
    lastFunctionName = ""
    lastArguments = ""
    lastReturnType = ""
    inFunction = False

    for l in lines:
        line = l.rstrip()
        if isFunDeclaration(line):
            if inFunction:
                functions[lastFunctionName] = Function(lastFunctionName, lastReturnType, lastArguments, lastFunctionBody)
                lastFunctionBody = []
            (returnType, name, arguments) = isFunDeclaration(line)
            lastReturnType = returnType
            lastArguments = arguments
            lastFunctionName = name
            inFunction = True
        elif inFunction:
            lastFunctionBody.append(line)

    functions[lastFunctionName] = Function(lastFunctionName, lastReturnType, lastArguments, lastFunctionBody)

    return functions



def parse_facts(filename):
    file1 = open(filename, 'r')
    lines = file1.readlines()

    facts = {}
    lastFactBody = []
    lastFactName = ""
    lastHeader = ""
    lastVariables = []
    inFact = False
    realLines = [l for l in lines if not l.lstrip().startswith("//")]
    for l in realLines:
        line = l.rstrip()
        if isFactDeclaration(line):
            if inFact:
                facts[lastFactName] = Fact(lastFactName, lastHeader, lastFactBody, lastVariables)
                lastFactBody = []
                lastVariables = []
            (returnType, name) = isFactDeclaration(line)
            lastFactName = name
            lastHeader = line
            inFact = True
        elif inFact:
            if isIntVariable(line):
                (_, name, value) = isIntVariable(line)
                lastVariables.append(name)
            lastFactBody.append(line)

    facts[lastFactName] = Fact(lastFactName, lastHeader, lastFactBody, lastVariables)

    return facts

def isFact(line):
    r1 = re.findall("(\s*)#FACT (.*)", line.rstrip())
    if r1:
        return (r1[0][0], r1[0][1].strip())
    else:
        return None

def isAssume(line):
    r1 = re.findall("(\s*)#ASSUME (.*)", line.rstrip())
    if r1:
        return (r1[0][0], r1[0][1].strip())
    else:
        return None

def containsCall(line, fun):
    r1 = re.findall(".*" + fun + "\\((.*)\\).*", line)
    if r1:
        arguments = r1[0].split(",")
        return arguments
    else:
        return None
