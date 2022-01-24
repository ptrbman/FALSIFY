### Main file for running FALSIFY

from falsify.cparser import parse_facts
from falsify.eldarica import check_fact, get_counterexample

import tempfile

def falsify(config):
    # Extract the code
    file1 = open(config["code_file"], 'r')
    codelines = file1.readlines()

    f = parse_facts(config["facts_file"])
    outlines = []

    # The code is unchanged
    for l in codelines:
        outlines.append(l)

    # The facts are preprocessed to fit eldarica
    for fact in f:
        outlines.append(f[fact].eldaricaModel())

    # Write all of it to temporary file
    filename = config["tmp_dir"] + "check.c"
    outfile = open(filename, "w")
    for l in outlines:
        outfile.write(l)
    outfile.close()

    print("Found ", len(f), " facts to be checked...", sep="")
    # Run eldarica on each fact
    no_safe = 0
    for fact in f:
        print("Fact ", fact, ": ", end="")
        safe = check_fact(filename, fact, config)
        if safe:
            print("true")
            no_safe = no_safe + 1
        else:
            ret = get_counterexample(filename, fact, f[fact].variables, config)
            print("false (", ret, ")")
    print()
    print(str(no_safe), "/", str(len(f)), " facts were true.", sep="")
    
