import re

class Function():
    def __init__(self, name, retType, arguments, body, mem):
        self.name = name
        self.retType = retType
        self.arguments = arguments
        self.body = body
        self.mem = mem

    def __str__(self):
        return self.name + ": " + str(self.arguments) + " -> " + self.retType

class Test():
    def __init__(self, name, header, body, variables):
        self.name = name
        self.header= header
        self.body = body
        self.variables = variables

    def __str__(self):
        return self.name + ": " + self.header

    def context(self):
        ctx = []
        inContext = False
        for l in self.body:
            if isContext(l):
                inContext = True
            elif isEndContext(l):
                return ctx
            elif inContext:
                ctx.append(l)
            else:
                ()

    def cbmcModel(self, disableTests=False, replacedContext=None):
        inContext = False
        newbody = []
        if replacedContext:
            newbody.append("void main() {")
        else:
            newbody.append(self.header)
        for l in self.body:
           if inContext and replacedContext and not isEndContext(l):
               ()
           elif isTest(l):
                (ws, retExp) = isTest(l)
                if not disableTests:
                    if replacedContext:
                        newbody.append(ws + "assert(" + retExp + ");")
                    else:
                        newbody.append(ws + "__CPROVER_assert(" + retExp + ", \"test\"); // AUTO-GENERATED")
                else:
                    newbody.append("// Tests disabled")
           elif isAssume(l):
                (ws, retExp) = isAssume(l)
                newbody.append(ws + "__CPROVER_assume(" + retExp + "); // AUTO-GENERATED")
           elif isContext(l):
               inContext = True
           elif isEndContext(l):
               inContext = False
               if replacedContext:
                   for l in replacedContext:
                       newbody.append(l)
           elif isMemMax(l):
                (ws, retMem) = isMemMax(l)
                newbody.append(ws + "__MEMORY__LIMIT__ = " + retMem + "; // AUTO-GENERATED")
           elif isIntVariable(l):
               (ws, name, value) = isIntVariable(l)
               if value == "_":
                   newbody.append(ws + "int " + name + " = nondet_int();")
               else:
                   newbody.append(ws + "int " + name + " = " + value + ";")
           elif "= _;" in l:
               r = re.findall("(.*)= _;", l)
               newline = r[0] + "= nondet_int();"
               newbody.append(newline)
           else:
                newbody.append(l)

        return newbody

def isFunDeclaration(line):
    r1 = re.findall("(int|void) (.*)\\((.*)\\)", line)
    if r1:
        returnType = r1[0][0]
        funName = r1[0][1]
        arguments = list(map(lambda x : x.strip(), r1[0][2].split(",")))
        return (returnType, funName, arguments)
    else:
        return None

# TODO: How come if we have an integer test it shows up in the list of tests?
def isTestDeclaration(line):
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

def isTest(line):
    r1 = re.fullmatch("(\s*)#ASSERT (.*)", line.rstrip())
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

def isMemMax(line):
    r1 = re.fullmatch("(\s*)#MEMMAX (.*)", line.rstrip())
    if r1:
        return (r1.groups()[0], r1.groups()[1].strip())
    else:
        return None

def isContext(line):
    return "#CONTEXT" in line

def isEndContext(line):
    return "#ENDCONTEXT" in line

def isMem(line):
    r1 = re.fullmatch("(\s*)#MEMORY (.*)", line.rstrip())
    if r1:
        return (r1.groups()[1].strip())
    else:
        return None

def isMemEnd(line):
    r1 = re.fullmatch("(\s*)#MEMEND", line.rstrip())
    if r1:
        return True
    else:
        return None

## Parse filename and return tests and the other lines, i.e., program code
def parse_tests(filename):
    file1 = open(filename, 'r')
    lines = file1.readlines()
    realLines = [l for l in lines if not l.lstrip().startswith("//")]

    # Begin by extracting includes, currently we enforce them to be top of file

    otherLines = []

    tests = {}
    lastTestBody = []
    lastTestName = ""
    lastHeader = ""
    lastVariables = []
    inTest = False

    for l in realLines:
        line = l.rstrip()
        if "#BEGINTEST" in l:
            inTest = True
        elif "#ENDTEST" in l:
            tests[lastTestName] = Test(lastTestName, lastHeader, lastTestBody, lastVariables)
            lastTestBody = []
            lastVariables = []
            inTest = False
        elif inTest:
            if isTestDeclaration(line):
               (returnType, name) = isTestDeclaration(line)
               lastTestName = name
               lastHeader = line
            else:
                if isIntVariable(line):
                    (_, name, value) = isIntVariable(line)
                    lastVariables.append(name)
                lastTestBody.append(line)
        else:
            # All non-test lines are stored in otherLines
            otherLines.append(line)

    return (otherLines, tests)

# Update code files to add memory constraints
def parse_code_file(filename, meminfo):
    outfile = filename + ".falsify.c"
    fin = open(filename, "r")
    fout = open(outfile, "w")
    curmem = None
    fout.write("extern int __MEMORY__USAGE__;\n")
    fout.write("extern int __MEMORY__LIMIT__;\n")
    for l in fin:
        if isFunDeclaration(l):
            (returnType, funName, arguments) = isFunDeclaration(l)
            fout.write(l)
            if meminfo[funName]:
                curmem = meminfo[funName]
                fout.write("__MEMORY__USAGE__ += " + curmem + ";\n")
                fout.write("__CPROVER_assert(__MEMORY__USAGE__ <= __MEMORY__LIMIT__, \"Memory Overflow\");\n")
            else:
                curmem = None
        elif curmem and "return" in l:
            fout.write("__MEMORY__USAGE__ -= " + curmem + ";\n")
            fout.write(l)
        else:
            fout.write(l)
    fin.close()
    fout.close()

    return outfile
