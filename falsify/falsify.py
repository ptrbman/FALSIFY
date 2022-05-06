### Main file for running FALSIFY

from falsify.cparser import parse_facts
from falsify.cbmc import check_fact, get_counterexample

import tempfile

def falsify(config):
    # file1 = open(config["code_file"], 'r')
    # codelines = file1.readlines()
    (includelines, facts) = parse_facts(config["test_file"])
    outlines = []

    # The code is unchanged
    # for l in codelines:
    #     outlines.append(l)

    # Change test file to CBMC format
    for test in facts:
        outlines.append(facts[test].cbmcModel())

    # Write tests to a temporary file
    filename = config["tmp_dir"] + "check.c"
    outfile = open(filename, "w")
    for l in includelines:
        outfile.write(l)
    for l in outlines:
        outfile.write(l)
    outfile.close()

    print("Found ", len(facts), " fact(s) to be checked...", sep="")
    safe_count = 0
    for fact in facts:
        print("Fact ", fact, ": ", end="")
        safe = check_fact(filename, fact, config)
        if safe:
            print("true")
            safe_count = safe_count + 1
        else:
            cex = get_counterexample(filename, fact, facts[fact].variables, config)
            print("false (", cex, ")")
    print()
    print(str(safe_count), "/", str(len(facts)), " facts were true.", sep="")
