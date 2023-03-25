from falsify.falsify import falsify

import sys
import os
import inspect, os.path
import argparse

## Supports arguments, multiple code files, one test file, multiple includes and defines
parser = argparse.ArgumentParser()
parser.add_argument("code", help="Program code", nargs='+')
parser.add_argument("tests", help="Tests")
parser.add_argument("--include", help="Directory of headers", action='append')
parser.add_argument("--define", help="C macros", action='append')
parser.add_argument("--memory", help="Memory analysis", default=False, action='store_true')
parser.add_argument("--memfile", help="Memory info file", action='append')
parser.add_argument("--verbose", help="Verbose mode", default=False, action='store_true')
parser.add_argument("--unwind", help="Unwinding bounds", default=3, type=int)
parser.add_argument("--pbt", help="Property based testing", default=False, action='store_true')
parser.add_argument("--pbttries", help="PBT tries", default=10, type=int)
args = parser.parse_args()


## Figure out which folder we are in, and use this to access local files
filename = inspect.getframeinfo(inspect.currentframe()).filename
base = os.path.dirname(os.path.abspath(filename))
config = {}
config["code_files"] = args.code
config["test_file"] = args.tests
config["verbose"] = args.verbose
config["pbt"] = args.pbt
config["unwind"] = str(args.unwind)
config["memory"] = args.memory
config["pbt_tries"] = args.pbttries
config["cbmc_dir"] = ""
config["tmp_dir"] = base + "/tmp/"

## Ensure we have a tmp-dir
if not os.path.isdir(config['tmp_dir']):
    os.mkdir(config['tmp_dir'])

## We cant use memory analysis and PBT at the same time
if config["pbt"] and config["memory"]:
    print("Memory analysis and PBT is not compatible.")
    exit()

if args.include:
    config["includes"] = args.include
else:
    config["includes"] = []

if args.memfile:
    config["memfiles"] = args.memfile
else:
    config["memfiles"] = []

if args.define:
    config["defines"] = args.define
else:
    config["defines"] = []

## Call falsify with theconfig
falsify(config)


