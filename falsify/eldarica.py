import subprocess
import re

def parse_output(output):
    if output.strip() == "SAFE":
        return True
    elif output.strip() == "UNSAFE":
        return False
    else:
        raise Exception("Cannot handle eldarica output: " + output)

def parse_cex_line(line, variables):
    r1 = re.findall(".*\\((.*)\\).*", line)
    values = r1[0].strip().split(',')
    ret = ""
    for var, val in zip(variables, values):
        ret = ret + var + ": " + str(int(val)) + " "
    return ret

def parse_counterexample(output, variables):
    lines = output.split("\n")
    for i,l in enumerate(lines):
        r1 = re.findall(".*Final.*", l)
        if r1:
            return parse_cex_line(lines[i+1], variables)
    raise Execption("Counter-example has no final line...")

# True if program is SAFE
def check_fact(fileName, function):
    command = ['lib/eldarica/eld', "-m:" + function, fileName]
    result = subprocess.run(command, stdout=subprocess.PIPE)
    output = result.stdout.decode('utf-8')
    return parse_output(output)

def get_counterexample(fileName, function, variables):
    command = ['lib/eldarica/eld', "-m:" + function, "-cex", fileName]
    result = subprocess.run(command, stdout=subprocess.PIPE)
    output = result.stdout.decode('utf-8')
    return parse_counterexample(output, variables)

## TODO: Change this so formual contains the actual names of the arguments in
## Function object. And then this function takes the name of the arguments
## instead of the count.

## TODO: Refactor to have check_file, etc. for eldarica so we can re-use some code.
def check_formula(formula, arguments):

    # Write to a temporary file
    lines = []
    args = []
    for i in range(arguments):
        args.append("ARG" + str(i))

    lines.append("void main() {")
    lines.append("\tint " + ",".join(args) + ";")
    lines.append("\tif (" + formula + ") {")
    lines.append("\t\tassert(0 == 1);")
    lines.append("\t}")
    lines.append("}")

    outfile = open("tmp/check.c", "w")
    for l in lines:
        outfile.write(l)
    outfile.close()

    command = ['lib/eldarica/eld', "tmp/check.c"]
    result = subprocess.run(command, stdout=subprocess.PIPE)
    output = result.stdout.decode('utf-8')
    is_covered = parse_output(output)
    if (is_covered):
        return None
    else:
        command = ['lib/eldarica/eld', "-cex", "tmp/check.c"]
        result = subprocess.run(command, stdout=subprocess.PIPE)
        output = result.stdout.decode('utf-8')
        return parse_counterexample(output, args)



