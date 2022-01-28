import subprocess
import re

# Check for the occurrence of the success/failed string
def parse_output(stdout, stderr):
    for l in stdout.split("\n"):
        if "VERIFICATION SUCCESSFUL" in l:
            return True
        elif "VERIFICATION FAILED" in l:
            return False
    raise Exception("Cannot handle CBMC output: \n" + stdout + "\n" + stderr)

## TODO: Make a better handler for extracting variable assignment lines
def find_nondet_lines(fileName):
    lines = {}
    f = open(fileName, "r")
    for i, l in enumerate(f):
        if "int_nondet" in l:
            r1 = re.findall("(\s*)int (\S*)\s*=\s*(.*);", l)
            if r1:
                lines[i+1] = r1[0][1]
            else:
                raise Exception("Unhandled nondet")
    return lines

def parse_trace(output):
    lines = output.split("\n")
    states = []
    for i in range(0, len(lines)):
        if lines[i].startswith("State"):
            r = re.findall("State \d+ \S* \S* function \S* line (\d+) thread 0", lines[i])
            curCodeLine = r[0]
            r = re.findall("\s*(.*)=(.*) \(.*\).*", lines[i+2])
            states.append((int(curCodeLine), r[0][0], r[0][1]))
            i += 3
    return states

# Extracts only values which are in lines
def parse_states(states, lines):
    cex = {}
    for (l, var, val) in states:
        if l in lines and lines[l] == var:
            cex[var] = val
    return ", ".join([k + ": " + cex[k] for k in cex])

# Assumes that there will be a failure
def get_counterexample(fileName, function, variables, config):
    ## TODO: Beautify experimental
    command = [config["cbmc_dir"] + "cbmc", "--beautify", "--function", function, "--trace", fileName]
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output = result.stdout.decode('utf-8')
    states = parse_trace(output)
    lines = find_nondet_lines(fileName)
    return parse_states(states, lines)

# True if program is SAFE
def check_fact(fileName, function, config):
    command = [config["cbmc_dir"] + "cbmc", "--function", function, fileName]
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout = result.stdout.decode('utf-8')
    stderr = result.stderr.decode('utf-8')
    return parse_output(stdout, stderr)

