import re
import subprocess
from falsify.cbmc import get_counterexample

def free_variables(context):
    vars = []
    for l in context:
        if "_" in l:
            rint = re.findall("int (.*) = _;", l)

            if rint:
                vars.append(rint[0])
            else:
                raise Exception("Unmatched free variable")
        else:
            ()
    return vars

def context_to_cbmc(context):
    cbmc = ["void pbt() {"]
    for l in context:
        refree = re.findall("(.*)= _;", l)
        reassume = re.fullmatch("\s*#ASSUME (.*)", l)
        reassert = re.fullmatch("\s*#ASSERT (.*)", l)
        if refree:
            cbmc.append(refree[0] + "= nondet_int();")
        elif reassume:
            cbmc.append("__CPROVER_assume(" + reassume.groups()[0] + ");")
        elif reassert:
            cbmc.append("__CPROVER_assert(" + reassert.groups()[0] + ", \"assert\");")
        else:
            cbmc.append(l)
    cbmc.append("}")
    return cbmc

def get_assignment(cbmc, free_vars, values_tried, config):
    pbt_file = config["tmp_dir"] + "pbt.c"
    fout = open(pbt_file, "w")
    for l in cbmc[:-2]: # Drop final __CPROVER_assert(0 == 1) and }
        fout.write(l + "\n")

    for vt in values_tried:
        cond = []
        for k in vt:
            cond.append(k + " != " + vt[k])
        fout.write("__CPROVER_assume(" + " || ".join(cond) + ");\n")

    fout.write("__CPROVER_assert(0 == 1, \"fail\");\n")
    fout.write("}\n")
    fout.close()

    cex = get_counterexample(pbt_file, "pbt", free_vars, config)
    assignments = cex.split(",")
    values = {}
    for a in assignments:
        aa = a.split(":")
        values[aa[0].strip()] = aa[1].strip()
    return values

def new_context(old_context, free_vars, values):
    # Get lines which are not assumptions or declaration of free variables
    ctx = []
    for l in old_context:
        refree = re.findall("int (.*)= _;", l)
        reassume = re.fullmatch("\s*#ASSUME (.*)", l)

        if refree:
            v = refree[0].strip()
            ctx.append("int " + v + " = " + values[v] + ";")
        elif reassume:
            ()
        else:
            ctx.append(l)
    return ctx

def compile(otherlines, body, config):
    main_file = config["tmp_dir"] + "main.c"
    fout = open(main_file, "w")
    fout.write("#include <assert.h>\n")
    for ol in otherlines:
        fout.write(ol + "\n")
    fout.write("\n\n")
    for l in body:
        fout.write(l + "\n")
    fout.close()

    includes = []
    for i in config["includes"]:
        includes.append("-I")
        includes.append(i)

    command = ["gcc"] + includes + config["code_files"] + [main_file]
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if config["verbose"]:
        print("Compilation result:")
        print(result)
    # ASSUME THIS WORKS FOR NOW ...

def parse_stderr(stderr):
    if "Assertion failed" in stderr:
        return True
    return False

def run(config):
    command = ["./a.out"]
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stderr = result.stderr.decode('utf-8')
    if config["verbose"]:
        print("./a.out STDERR:")
        print(stderr)
    return parse_stderr(stderr)
 
def run_pbt(otherlines, testlines, test, config):
    ctx = test.context()
    free_vars = free_variables(ctx)
    fail_ctx = ctx
    ctx.append("#ASSERT 0 == 1")
    cbmc = context_to_cbmc(ctx)

    values_tried = []
    for i in range(config["pbt_tries"]):
        # CBMC model to find value assignments
        values = get_assignment(cbmc, free_vars, values_tried, config)

        # Generate new context
        new_ctx = new_context(ctx[:-1], free_vars, values) # Throw away ASSERT 0 == 1

        # compile and run code?
        body = test.cbmcModel(False, new_ctx)
        compile(otherlines, body, config)
        if run(config):
            return values
        else:
            if config["verbose"]:
                print("PBT: PASS (" + str(values) + ")")
            values_tried.append(values)
    return None
