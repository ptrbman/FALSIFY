### Main file for running FALSIFY

from falsify.cparser import parse_tests
from falsify.cbmc import check_test, get_counterexample

import tempfile

# Let's change this: Now, do tests one by one, by introducing a file containing
# all non-test code and one test. Also, add assert(0 == 1) at the end to ensure
# unwinding is complete.

def falsify(config):
    (otherlines, tests) = parse_tests(config["test_file"])

    print("Found ", len(tests), " test(s) to be checked...", sep="")
    safe_count = 0
    otherlines.append("int nondet_int();")

    for test in tests:
        # Change test file to CBMC format
        testlines = tests[test].cbmcModel()

        # Write tests to a temporary file
        filename = config["tmp_dir"] + "check.c"
        outfile = open(filename, "w")
        for l in otherlines:
            outfile.write(l + "\n")
        for l in testlines:
            outfile.write(l + "\n")
        outfile.close()

        print("Test ", test, ": ", end="")
        safe = check_test(filename, test, config)
        if safe:
            print("true")
            safe_count = safe_count + 1
        else:
            cex = get_counterexample(filename, test, tests[test].variables, config)
            print("false (", cex, ")")
    # print()
    # print(str(safe_count), "/", str(len(tests)), " tests were true.", sep="")
