import subprocess
import re

def parse_output(stdout, stderr):
    for l in stdout.split("\n"):
        if "VERIFICATION SUCCESSFUL" in l:
            return True
        elif "VERIFICATION FAILED" in l:
            return False
    raise Exception("Cannot handle CBMC output: \n" + stdout + "\n" + stderr)

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
    stdout = result.stdout.decode('utf-8')
    stderr = result.stderr.decode('utf-8')
    return parse_output(stdout, stderr)

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
            # r1 = re.findall("\s*(.*)=(-?\d+) .*", lines[i])
            r1 = re.findall("\s*(.*)=(.*) \(.*\).*", lines[i])
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
    cex = {}
    for (l, var, val) in states:
        if l in lines and lines[l] == var:
            cex[var] = val
        i += 1
    cexstr = []
    for k in cex:
        cexstr.append(k + ": " + cex[k])
    return ", ".join(cexstr)

def get_counterexample(fileName, function, variables, config):
    ## TODO: Beautify experimental
    command = [config["cbmc_dir"] + "cbmc", "--beautify", "--function", function, "--trace", fileName]
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output = result.stdout.decode('utf-8')
    states = parse_trace(output)
    lines = find_nondet_lines(fileName)
    return parse_states(states, lines)
