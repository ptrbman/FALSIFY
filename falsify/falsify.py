### Main file for running FALSIFY

from falsify.cparser import parse_facts
from falsify.eldarica import check_fact

def check_code_and_facts(code, facts):
    # -Extract the code 
    file1 = open(code, 'r')
    codelines = file1.readlines()

    f = parse_facts(facts)
    outlines = []

    # The code is unchanged
    for l in codelines:
        outlines.append(l)

    # The facts are preprocessed to fit eldarica
    for fact in f:
        outlines.append(f[fact].eldaricaModel())

    # Write all of it to temporary file
    outfile = open("tmp/check.c", "w")
    for l in outlines:
        outfile.write(l)
    outfile.close()

    print("Found ", len(f), " facts to be checked...", sep="")
    # Run eldarica on each fact
    no_safe = 0
    for fact in f:
        print("Fact ", fact, ": ", end="")
        safe = check_fact("tmp/check.c", fact)
        if safe:
            print("true")
            no_safe = no_safe + 1
        else:
            print("false")
    print()
    print(str(no_safe), "/", str(len(f)), " facts were true.", sep="")
