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
def check_fact(fileName, function, config):
    command = [config["eldarica_dir"] + "eld", "-m:" + function, fileName]
    result = subprocess.run(command, stdout=subprocess.PIPE)
    output = result.stdout.decode('utf-8')
    return parse_output(output)

def get_counterexample(fileName, function, variables, config):
    command = [config["eldarica_dir"] + "eld", "-m:" + function, "-cex", fileName]
    result = subprocess.run(command, stdout=subprocess.PIPE)
    output = result.stdout.decode('utf-8')
    return parse_counterexample(output, variables)

