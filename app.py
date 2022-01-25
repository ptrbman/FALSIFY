from falsify.falsify import falsify
from falsify.coverage import coverage 
import sys
import os

import inspect, os.path

def print_usage():
    print("Usage: falsify [falsify|coverage] input.c input.facts")

if (len(sys.argv) < 4):
    print("Error: both mode, code and facts file needed")
    print_usage()
elif not ".c" in sys.argv[2] or not ".facts" in sys.argv[3]:
    print("Error: only support for .c and .facts files.")
    print_usage()
else:
    filename = inspect.getframeinfo(inspect.currentframe()).filename
    base = os.path.dirname(os.path.abspath(filename))
    config = {}
    config["code_file"] = sys.argv[2]
    config["facts_file"] = sys.argv[3]
    config["eldarica_dir"] = base + "/lib/eldarica/"
    config["cbmc_dir"] = ""
    config["tmp_dir"] = base + "/tmp/"
    if sys.argv[1] == "falsify":
        falsify(config)
    elif sys.argv[1] == "coverage":
        coverage(config)
    else:
        print("Error: modes falsify and coverage supported")
        print_usage()

