### Main file for running FALSIFY

from falsify.cparser import parse_facts
from falsify.cbmc import check_fact, get_counterexample

import tempfile

def falsify(config):
    file1 = open(config["code_file"], 'r')
    codelines = file1.readlines()
    f = parse_facts(config["facts_file"])
    outlines = []

    # The code is unchanged
    for l in codelines:
        outlines.append(l)

    for fact in f:
        outlines.append(f[fact].cbmcModel())

    # Write all of it to temporary file
    filename = config["tmp_dir"] + "check.c"
    outfile = open(filename, "w")
    for l in outlines:
        outfile.write(l)
    outfile.close()

    print("Found ", len(f), " facts to be checked...", sep="")
    safe_count = 0
    for fact in f:
        print("Fact ", fact, ": ", end="")
        safe = check_fact(filename, fact, config)
        if safe:
            print("true")
            safe_count = safe_count + 1
        else:
            cex = get_counterexample(filename, fact, f[fact].variables, config)
            print("false (", cex, ")")
    print()
    print(str(safe_count), "/", str(len(f)), " facts were true.", sep="")
