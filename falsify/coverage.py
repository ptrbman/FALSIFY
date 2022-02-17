from falsify.cparser import parse_facts
from falsify.cbmc import coverage_fact

import re

def branch_coverage(config):
    file1 = open(config["code_file"], 'r')
    codelines = file1.readlines()
    f = parse_facts(config["facts_file"])
    outlines = []

    # Add BC
    curBID = 1
    all = []
    for l in codelines:
        r = re.fullmatch("(\s*)if.*\n",l)
        if r:
            outlines.append(l)
            string = "  __CPROVER_assert(BC != " + str(curBID) + ", \"Branch " + str(curBID) + "\");\n"
            outlines.append(r[1] + string)
            all.append(curBID)
        else:
            r = re.fullmatch("(\s*)} else {\n", l)
            if r:
                outlines.append(l)
                string = "  __CPROVER_assert(BC != -" + str(curBID) + ", \"Branch -" + str(curBID) + "\");\n"
                outlines.append(r[1] + string)
                all.append(-curBID)
                curBID += 1
            else:
                outlines.append(l)

    for fact in f:
        outlines.append(f[fact].cbmcModel(True))

    # Write all of it to temporary file
    filename = config["tmp_dir"] + "coverage.c"
    outfile = open(filename, "w")
    outfile.write("int BC = int_nondet();\n\n")
    for l in outlines:
        outfile.write(l)
    outfile.close()

    all_covered = []
    print("Found a total of ", str(len(all)), "branches")
    print("Found ", len(f), " facts to be checked...", sep="")
    for fact in f:
        print("Fact ", fact, ": ", end="")
        covered = coverage_fact(filename, fact, config)
        print("\t", covered)
        all_covered = all_covered + covered
    for c in set(all_covered):
        all.remove(c)

    print("Remaining branches: ", len(all))
