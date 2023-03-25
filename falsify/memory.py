import re

def parse_memfile(memfile):
    f = open(memfile, "r")
    last_memory = 0 # we deafult to zero
    meminfo = {}
    for l in f:
        refun = re.findall("(int|void) (.*)\\((.*)\\)", l)
        remem = re.findall("#MEMORY (.*)", l)
        if refun:
            meminfo[refun[0][1].strip()] = last_memory
            last_memory = 0
        elif remem:
            last_memory = remem[0]
        else:
            ()
    return meminfo

def get_memory_info(memfiles):
    meminfo = {}
    for mf in memfiles:
        mi = parse_memfile(mf)
        meminfo.update(mi)
    return meminfo
