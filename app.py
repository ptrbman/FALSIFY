from falsify.falsify import falsify
from falsify.coverage import branch_coverage
import sys
import os

import inspect, os.path

def print_usage():
    print("Usage: falsify check|coverage input.c input.facts")

if (len(sys.argv) < 4):
    print("Error: mode, code and facts file needed")
    print_usage()
elif not sys.argv[1] in ["check", "coverage"]:
    print("Error: modes supported: check, coverage")
elif not ".c" in sys.argv[2] or not ".facts" in sys.argv[3]:
    print("Error: only support for .c and .facts files.")
    print_usage()
else:
    filename = inspect.getframeinfo(inspect.currentframe()).filename
    base = os.path.dirname(os.path.abspath(filename))
    config = {}
    config["code_file"] = sys.argv[2]
    config["facts_file"] = sys.argv[3]
    config["cbmc_dir"] = ""
    config["tmp_dir"] = base + "/tmp/"
    if sys.argv[1] == "check":
        falsify(config)
    elif sys.argv[1] == "coverage":
        branch_coverage(config)


