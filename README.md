# FALSIFY

FALSIFY is a prototype framework for test analysis. It works with rich tests over C-code. 

## Installation

Begin by cloning the source code

```shell
git clone https://github.com/ptrbman/FALSIFY.git
```

To execute FALSIFY there are two requirements:
* Python (tested with 3.7.6)
Install from, e.g., https://www.python.org
* CBMC (tested with 5.76.1)
install from, e.g., http://www.cprover.org/cbmc/

## Usage

With all prerequisites, you can execute FALSIFY using:

```shell
python3 app.py

usage: app.py [-h] [--include INCLUDE] [--define DEFINE] [--memory]
              [--memfile MEMFILE] [--verbose] [--unwind UNWIND] [--pbt]
              [--pbttries PBTTRIES]
              code [code ...] tests

```

For example, to execute the $max$ test, use:
```shell
python3 app.py --include examples/ examples/max.c examples.max.tests

Found 8 test(s) to be checked...
Test  max_test_0 : true
Test  max_test_1 : false ( b: 1 )
Test  max_test_2 : true
Test  max_test_3 : true
Test  max_test_a_greater_than_b : true
Test  max_test_a_smaller_than_b : true
Test  max_test_a_greater_than_or_equal_to_b : true
Test  max_test_a_smaller_than_or_equal_to_b : true
```

The ```--include``` options tells FALSIFY where to find header files. The other two arguments are the code-file (containing the code to be tested) and the test file (containing the rich tests). Note that it is possible to have more than one code file, but only a single test file. 

### Unwindings

```--unwind``` controls the number of unwindings CBMC should perform, a too low number can yield an insufficient unwindings error:

```shell
python3 app.py --include examples examples/sum.c examples/sum.tests

Found 1 test(s) to be checked...
Test  sum_test_1 : unknown (insufficient unwindings)
```

To handle this we can increase the unwindings:

```shell
python3 app.py --include examples examples/sum.c examples/sum.tests 40

Found 1 test(s) to be checked...
Test  sum_test_1 : false ( len: 38 )
```

### Memory testing
```-memfile``` can be use to enable memory testing:

```shell
python3 app.py --include examples examples/memory.c examples/memory.tests --memfile examples/memory.mem --memory --unwind 5

Found 1 test(s) to be checked...
Test  mem_test : true
```

## Regression

To run all the examples you can execute (on Linux or MacOS) the ```regression.sh``` script:

```shell
./regression.sh

<<<Regression testing>>>

/---\
|abs|
\---/
Found 2 test(s) to be checked...
Test  test_abs_1 : true
Test  test_abs_2 : true
.. should both work

...
...
...

/--------\
|triangle|
\--------/
Found 17 test(s) to be checked...
Test  triangle_test_0 : true
Test  triangle_test_1 : true
Test  triangle_test_2 : true
Test  triangle_test_3 : true
Test  triangle_test_4 : true
Test  triangle_test_5 : true
Test  triangle_test_6 : true
Test  triangle_test_7 : true
Test  triangle_test_8 : true
Test  triangle_test_9 : true
Test  triangle_test_10 : true
Test  triangle_test_11 : true
Test  triangle_test_12 : true
Test  triangle_test_13 : true
Test  triangle_test_14 : true
Test  triangle_test_15 : true
Test  triangle_test_equilateral : false ( s1: 1459451514, s2: 1459451514, s3: 1459451514 )
... should all work except last one
```




