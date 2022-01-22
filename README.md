# FALSIFY
FALSIFY tool


## Usage
FALSIFY takes two files as input, a source-code file and a unit-facts file. A unit-fact has three parts to it. A pre-conditon, a block of code, and a post-condition.

Consider **max.c**:
````c
int max(int a, int b) {
  if (a > b) {
    return a;
  } else {
    return b;
  }
}
````

And **max.facts**
````c
void max_fact_0() {
  int a = 0;
  int b = 1;
  int ret = max(a,b);
  #FACT ret == 1
}
````

The following executes and tries to falsify the facts:
````console
ptr@host:~$ falsify max.c max.facts
    Found 1 fact to be checked...
Fact max_fact_0: true

1/1 facts were true.
````


