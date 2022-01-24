from falsify.falsify import check_code_and_facts
from falsify.coverage import coverage_code_and_facts

def falsify(code, facts):
    check_code_and_facts(code, facts)

def coverage(code, facts):
    coverage_code_and_facts(code, facts)
