### Main file for running COVERAGE

from falsify.cparser import parse_functions, parse_facts
from falsify.eldarica import check_formula

def coverage(config):
    # Extract all the functions:
    funs = parse_functions(config["code_file"])

    print("Found", len(funs), "functions to be checked...")
    # Extract all the unit-facts
    facts = parse_facts(config["facts_file"])

    print("Found", len(facts), "facts to be checked...")

    errors = []

    # For each function, go through the unit facts and figure out the calls for
    # the function, and for each function call what is the parameter space
    for fun in funs:
        calls = []
        for fact in facts:
            newCalls = facts[fact].find_call(fun)
            calls = calls + newCalls
        # We want to find an assignment of arguments which is outside all the calls,
        # If an assignment is outside on of the arguments, means that the negation is satisfied,
        # outside all assignments, means the conjunction of negations are satsified
        conj = []
        for call in calls:
            negated = "!(" + call + ")"
            conj.append(negated)
        formula = " && ".join(conj)
        ret = check_formula(formula, len(funs[fun].arguments), config)
        if ret:
            errors.append(fun + ": is missing ( " + ret + ")")

    if errors:
        print("\nCoverage is *not* complete:")
        for e in errors:
            print(e)
    else:
        print("\nCoverage is complete for all functions found: ", ",".join(funs))


