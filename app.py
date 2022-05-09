from falsify.falsify import falsify
# from falsify.coverage import branch_coverage
import sys
import os

import inspect, os.path

import argparse


# Maybe add support for coverage?
# Add check for .c and .tests

parser = argparse.ArgumentParser()
parser.add_argument("code", help="Program code", nargs='+')
parser.add_argument("tests", help="Tests")
parser.add_argument("--include", help="Directory of headers", action='append')
parser.add_argument("--define", help="C macros", action='append')
args = parser.parse_args()


filename = inspect.getframeinfo(inspect.currentframe()).filename
base = os.path.dirname(os.path.abspath(filename))
config = {}
config["code_files"] = args.code
config["test_file"] = args.tests
config["cbmc_dir"] = ""
config["tmp_dir"] = base + "/tmp/"
if args.include:
    config["includes"] = args.include
else:
    config["includes"] = []
if args.define:
    config["defines"] = args.define
else:
    config["defines"] = []

falsify(config)


