import subprocess

def parse_output(output):
    if output.strip() == "SAFE":
        return True
    elif output.strip() == "UNSAFE":
        return False
    else:
        raise Exception("Cannot handle eldarica output: " + output)

# True if program is SAFE
def check_fact(fileName, function):
    command = ['lib/eldarica/eld', "-m:" + function, fileName]
    result = subprocess.run(command, stdout=subprocess.PIPE)
    output = result.stdout.decode('utf-8')
    return parse_output(output)
