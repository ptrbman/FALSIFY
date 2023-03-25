from falsify.cparser import parse_tests, parse_code_file
from falsify.cbmc import check_test, get_counterexample
from falsify.pbt import run_pbt
from falsify.memory import get_memory_info
import tempfile

def falsify(config):
    (otherlines, tests) = parse_tests(config["test_file"])

    print("Found ", len(tests), " test(s) to be checked...", sep="")
    safe_count = 0
    otherlines.append("int nondet_int();")
    otherlines.append("int __MEMORY__USAGE__ = 0;")
    otherlines.append("int __MEMORY__LIMIT__;")

    # We need to edit code_files
    if config["memory"]:
        # First get memory info:
        mem_info = get_memory_info(config["memfiles"])
        new_code_files = []
        for cf in config["code_files"]:
            new_file = parse_code_file(cf, mem_info)
            new_code_files.append(new_file)
        config["code_files"] = new_code_files



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
        (safe, reason) = check_test(filename, test, config)
        if safe:
            print("true")
            safe_count = safe_count + 1
        else:
            if reason == "UNWIND":
                print("unknown (insufficient unwindings)")
                if config["pbt"]:
                    pbt_result = run_pbt(otherlines, testlines, tests[test], config)
                    if pbt_result:
                        print("\tPBT failure: ", pbt_result)
                    else:
                        print("\tPBT indicates passing")
            else:
                cex = get_counterexample(filename, test, tests[test].variables, config)
                print("false (", cex, ")")
    # print()
    # print(str(safe_count), "/", str(len(tests)), " tests were true.", sep="")
