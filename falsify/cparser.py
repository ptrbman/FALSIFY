import re

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
           else:
                newbody.append(l)

        return "\n".join(newbody)

def isFactDeclaration(line):
    r1 = re.findall("(void) (.*)\\(\\)", line)
    if r1:
        returnType = r1[0][0]
        funName = r1[0][1]
        return (returnType, funName)
    else:
        return None

def isIntVariable(line):
    r1 = re.findall("\s*int (\S*)\s.*", line)
    if r1:
        name = r1[0]
        return name
    else:
        return None

def parse_facts(filename):
    file1 = open(filename, 'r')
    lines = file1.readlines()

    facts = {}
    lastFactBody = []
    lastFactName = ""
    lastHeader = ""
    lastVariables = []
    inFact = False

    for l in lines:
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
                name = isIntVariable(line)
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


