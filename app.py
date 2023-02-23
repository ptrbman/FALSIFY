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
args = parser.parse_args()


## Figure out which folder we are in, and use this to access local files
filename = inspect.getframeinfo(inspect.currentframe()).filename
base = os.path.dirname(os.path.abspath(filename))
config = {}
config["code_files"] = args.code
config["test_file"] = args.tests
config["cbmc_dir"] = ""
config["tmp_dir"] = base + "/tmp/"

## Ensure we have a tmp-dir
if not os.path.isdir(config['tmp_dir']):
    os.mkdir(config['tmp_dir'])

if args.include:
    config["includes"] = args.include
else:
    config["includes"] = []

if args.define:
    config["defines"] = args.define
else:
    config["defines"] = []

## Call falsify with theconfig
falsify(config)


