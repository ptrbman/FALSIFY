##
## Module for handling input/output with CBMC
##
##


import subprocess
import re

# Check for the occurrence of the success/failed string
def parse_output(stdout, stderr):
    unwinding_failure = False
    assertion_failure = False
    verification_result = None
    for l in stdout.split("\n"):
        if "FAILURE" in l:
            if "unwinding" in l:
                unwinding_failure = True
            elif "assertion" in l:
                assertion_failure = True
            else:
                raise Exception("Unhandled FAILURE: ", l)
        elif "VERIFICATION SUCCESSFUL" in l:
            verification_result = "SUCCESS"
        elif "VERIFICATION FAILED" in l:
            verification_result = "FAILED"

    if assertion_failure:
       return (False, "")
    elif unwinding_failure:
       return (False, "UNWIND")
    elif verification_result == "SUCCESS":
       return (True, "")
    elif verification_result == "FAILED":
       raise Exception("Unidentified failure\n:" + stdout + "\n" + stderr)
    else:
       raise Exception("Unhandled CBMC output\n:" + stdout + "\n" + stderr)

# Checks for errors, None means everything is ok!
def parse_stderr(stderr):
    if not stderr:
        return None

    for l in stderr.split("\n"):
        r = re.findall("function (.*) is not declared", l)
        if r:
            return "Missing function in " + r[0]

        r = re.findall("fatal error: (.*) file not found", l)
        if r:
            return "Missing file " + r[0]

    return "Unrecognized error: " + stderr

## TODO: Make a better handler for extracting variable assignment lines
def find_nondet_lines(fileName):
    lines = {}
    f = open(fileName, "r")
    for i, l in enumerate(f):
        if "nondet_int" in l and not l == "int nondet_int();\n":
            r1 = re.findall("(\s*)int (\S*)\s*=\s*(.*);", l)
            r2 = re.findall("(\s*)(\S*)\s*=\s*(.*);", l)
            if r1:
                lines[i+1] = r1[0][1]
            if r2:
                lines[i+1] = r2[0][1]
            else:
                raise Exception("Unhandled nondet: " + l)
    return lines

def parse_trace(output):
    lines = output.split("\n")
    states = []
    prevCodeLine = 0
    for i in range(0, len(lines)):
        if lines[i].startswith("State"):
            r = re.findall("State \d+ \S* \S* function \S* line (\d+) thread 0", lines[i])
            r2 = re.findall("State \d+ function \S* thread 0", lines[i])
            if r:
                curCodeLine = r[0]
            elif r2:
                curCodeLine = prevCodeLine
            else:
                print("Parser error: ", lines[i])
                10/0

            r = re.findall("\s*(.*)=(.*) \(.*\).*", lines[i+2])
            states.append((int(curCodeLine), r[0][0], r[0][1]))
            prevCodeLien = curCodeLine
            i += 3
    return states

# Extracts only values which are in lines
def parse_states(states, lines):
    cex = {}
    for (l, var, val) in states:
        if l in lines and lines[l] == var:
            cex[var] = val
    return ", ".join([k + ": " + cex[k] for k in cex])

## TODO: Unwindings hard-coded
def base_command(config, function):
    includes = []
    for i in config["includes"]:
        includes.append("-I")
        includes.append(i)
    defines = []
    for d in config["defines"]:
        defines.append("-D")
        defines.append(d)

    code_files = config["code_files"]
    command = [config["cbmc_dir"] + "cbmc", "--unwinding-assertions", "--unwind", config["unwind"]] + includes + defines + ["--function", function] + code_files
    return command


# Assumes that there will be a failure
def get_counterexample(fileName, function, variables, config):
    ## TODO: Beautify experimental
    bc = base_command(config, function)
    command = bc + ["--beautify", "--trace", fileName]
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output = result.stdout.decode('utf-8')
    states = parse_trace(output)
    lines = find_nondet_lines(fileName)

    return parse_states(states, lines)

# True if program is SAFE
def check_test(fileName, function, config):
    bc = base_command(config, function)
    command = bc + [fileName]
    if config["verbose"]:
        print("Command: ", " ".join(command))
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout = result.stdout.decode('utf-8')
    stderr = result.stderr.decode('utf-8')
    error = parse_stderr(stderr)
    if error:
        print("ERROR ENCOUNTERED")
        print(error)
        return False
    retval = parse_output(stdout, stderr)
    return retval


def parse_branch(line):
    if "FAILURE" in line:
        r = re.findall(".*Branch (-?\d*): .*", line)
        return int(r[0])
    return None

def parse_coverage(output):
    failed = []
    for l in output.split("\n"):
        if "Branch" in l:
            ret = parse_branch(l)
            if ret:
                failed.append(ret)
    return failed

def coverage_test(fileName, function, config):
    command = [config["cbmc_dir"] + "cbmc", "--unwind", "10", "--function", function, fileName]
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout = result.stdout.decode('utf-8')
    return parse_coverage(stdout)



