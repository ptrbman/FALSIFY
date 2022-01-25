import subprocess
import re

def parse_output(output):
    for l in output.split("\n"):
        if "VERIFICATION SUCCESSFUL" in l:
            return True
        elif "VERIFICATION FAILED" in l:
            return False
    raise Exception("Cannot handle CBMC output: " + output)

## Find states correspdonding to int_nondet and then we can get counter-example
def parse_counterexample(output, lines):
    for i,l in enumerate(output.split("\n")):
        r1 = re.findall("State \d+ \S* \S* function \S* line (\d+) thread 0", l)
        if r1:
            lineNo = int(r1[0])
    raise Exception("Counter-example has no final line...")

# True if program is SAFE
def check_fact(fileName, function, config):
    command = [config["cbmc_dir"] + "cbmc", "--function", function, fileName]
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output = result.stdout.decode('utf-8')
    return parse_output(output)

## TODO: Make a better handler for extracting variable assignment lines
def find_nondet_lines(fileName):
    lines = {}
    f = open(fileName, "r")
    for i, l in enumerate(f):
        if "int_nondet" in l:
            r1 = re.findall("(\s*)int (\S*)\s*=\s*(.*);", l)
            if r1:
                ws = r1[0][0]
                name = r1[0][1]
                value = r1[0][2]
                lines[i+1] = name
            else:
                raise Exception("Unhandled nondet")
    return lines

def parse_trace(output):
    phase = 0
    lines = output.split("\n")
    i = 0
    states = []
    curCodeLine = 0
    while phase < 5:
        if phase == 0:
            if lines[i].startswith("State"):
                r1 = re.findall("State \d+ \S* \S* function \S* line (\d+) thread 0", lines[i])
                curCodeLine = r1[0]
                phase = 1
            elif lines[i].startswith("Violated"):
                phase = 5
        elif phase == 1:
            # Skip
            phase = 2
        elif phase == 2:
            r1 = re.findall("\s*(.*)=(-?\d+) .*", lines[i])
            var = r1[0][0]
            val = r1[0][1]
            states.append((int(curCodeLine), var, val))
            phase = 3
        elif phase == 3:
            phase = 0
        i += 1
    return states

## TODO: We should add functionality to find values also for "interesting values" at the point of failure
def parse_states(states, lines):
    i = 0
    cex = []
    while i < len(states):
        (l, var, val) = states[i]
        if l in lines:
            ## Ensure the next one is for the same variable
            (l2, var2, val2) = states[i+1]
            if not l == l2 or not var == var2:
                raise Exception("BUG 001")
            cex.append(var + ": " + val2)
            i += 1
        i += 1
    return ", ".join(cex)

def get_counterexample(fileName, function, variables, config):
    ## TODO: Beautify experimental
    command = [config["cbmc_dir"] + "cbmc", "--beautify", "--function", function, "--trace", fileName]
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output = result.stdout.decode('utf-8')
    states = parse_trace(output)
    lines = find_nondet_lines(fileName)
    return parse_states(states, lines)

## TODO: Change this so formual contains the actual names of the arguments in
# ## Function object. And then this function takes the name of the arguments
# ## instead of the count.

# ## TODO: Refactor to have check_file, etc. for eldarica so we can re-use some code.
# def check_formula(formula, arguments, config):
#     # Write to a temporary file
#     lines = []
#     args = []
#     for i in range(arguments):
#         args.append("ARG" + str(i))

#     lines.append("void main() {")
#     lines.append("\tint " + ",".join(args) + ";")
#     lines.append("\tif (" + formula + ") {")
#     lines.append("\t\tassert(0 == 1);")
#     lines.append("\t}")
#     lines.append("}")

#     filename = config["tmp_dir"] + "/check.c"
#     outfile = open(filename, "w")
#     for l in lines:
#         outfile.write(l)
#     outfile.close()

#     command = [config["eldarica_dir"] + "eld", filename]
#     result = subprocess.run(command, stdout=subprocess.PIPE)
#     output = result.stdout.decode('utf-8')
#     is_covered = parse_output(output)
#     if (is_covered):
#         return None
#     else:
#         command = [config["eldarica_dir"] + "eld", "-cex", filename]
#         result = subprocess.run(command, stdout=subprocess.PIPE)
#         output = result.stdout.decode('utf-8')
#         return parse_counterexample(output, args)



