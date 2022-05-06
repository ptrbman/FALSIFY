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

    def cbmcModel(self, disableFacts=False):
        newbody = [self.header]

        for l in self.body:
           if isFact(l):
                (ws, retExp) = isFact(l)
                if not disableFacts:
                    newbody.append(ws + "__CPROVER_assert(" + retExp + ", \"test\"); // AUTO-GENERATED")
                else:
                    newbody.append("// Facts disabled")
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

def isFact(line):
    r1 = re.fullmatch("(\s*)#FACT (.*)", line.rstrip())
    if r1:
        return (r1.groups()[0], r1.groups()[1].strip())
    else:
        return None

def isAssume(line):
    r1 = re.fullmatch("(\s*)#ASSUME (.*)", line.rstrip())
    if r1:
        return (r1.groups()[0], r1.groups()[1].strip())
    else:
        return None

def parse_facts(filename):
    file1 = open(filename, 'r')
    lines = file1.readlines()
    realLines = [l for l in lines if not l.lstrip().startswith("//")]

    # Begin by extracting includes, currently we enforce them to be top of file
    includelines = [l for l in realLines if l.startswith("#include")]
    codelines = [l for l in realLines if not l.startswith("#include")]

    facts = {}
    lastFactBody = []
    lastFactName = ""
    lastHeader = ""
    lastVariables = []
    inFact = False
    for l in codelines:
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

    return (includelines, facts)

