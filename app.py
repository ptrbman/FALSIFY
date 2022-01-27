from falsify.falsify import falsify
import sys
import os

import inspect, os.path

def print_usage():
    print("Usage: falsify input.c input.facts")

if (len(sys.argv) < 3):
    print("Error: both code and facts file needed")
    print_usage()
elif not ".c" in sys.argv[1] or not ".facts" in sys.argv[2]:
    print("Error: only support for .c and .facts files.")
    print_usage()
else:
    filename = inspect.getframeinfo(inspect.currentframe()).filename
    base = os.path.dirname(os.path.abspath(filename))
    config = {}
    config["code_file"] = sys.argv[1]
    config["facts_file"] = sys.argv[2]
    config["eldarica_dir"] = base + "/lib/eldarica/"
    config["cbmc_dir"] = ""
    config["tmp_dir"] = base + "/tmp/"
    falsify(config)

