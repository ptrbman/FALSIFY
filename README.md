# FALSIFY
FALSIFY tool


## Unit Facts
The main component of *falsify* is the unit fact. It looks a bit like a unit test, but with two key differences:

### Facts
While a unit test has assertions, instead a unit fact has *facts*, which are written as pragma-statements #FACT formula, where formula is more or less equivalent to an assertion.

### Assumptions
A unit test has a set-up a segment where variables are initialzed to their desired values. In a unit fact we have a similar section, but it can also include *assumption*, which allows for more generic statements. They are written using pragma-statements #ASSUME.

A unit fact consists of three parts: set-up, code block and facts. The set-up initializes variables to specific values, to nothing at all or with an assumption. The code block should describe the behaviour which should be tested, and the facts describe statements of the system which should be proven to hold. Consider the following:

````c
void max_fact_0() {
  // Set-up
  int a = 0;
  int b = 1;
 
  // Code block
  int ret = max(a,b);
 
  // Facts
  #FACT ret == 1
}
````



## Example: *max.c* 
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
ptr@host:~$ ./falsify.sh max.c max.facts
Found 1 fact to be checked...
Fact max_fact_0: true

1/1 facts were true.
````

Moreover, consider we try and add the following fact to the **max.facts** file:
````c
void max_fact_1() {
  int a = 0;
  int b = _;
  int ret = max(a,b);
  #FACT ret == 0
}
````
where *b = _;* states that we do not wish to specify a specific value for *b*. Of course, now the fact is no longer true, so if we try to run **falsify** again:
````console
ptr@host:~$ ./falsify.sh max.c max.facts
Found 2 facts to be checked...
Fact  max_fact_0 : true
Fact  max_fact_1 : false ( a: 0 b: -1 ret: 0  )

1/2 facts were true.
````

So far we've seen assigning a specific value or no value to a variable. But it is also possible to specify a constraint on a variable:
````c
void max_fact_2() {
  int a = 0;
  int b = _;
  #ASSUME b < 0
  int ret = max(a,b);
  #FACT ret == 0
}
````

Now the fact is true, and thus we will get the following:
````console
ptr@host:~$ ./falsify.sh max.c max.facts
Found 3 facts to be checked...
Fact  max_fact_0 : true
Fact  max_fact_1 : false ( a: 0 b: 1 ret: 1  )
Fact  max_fact_2 : true

2/3 facts were true.
````

Now we are ready to make more interesting facts, for example we can say **if a is positive and b is negative, then max(a,b) will be equal to a**:
````c
void max_fact_3() {
  int a = _;
  int b = _;
  #ASSUME a > 0
  #ASSUME b < 0
  int ret = max(a,b);
  #FACT ret == a
}
````
Once again, running this will not falsify this fact:

````console
ptr@host:~$ ./falsify.sh max.c max.facts
Found 4 facts to be checked...
Fact  max_fact_0 : true
Fact  max_fact_1 : false ( a: 0 b: 1 ret: 1  )
Fact  max_fact_2 : true
Fact  max_fact_4 : true

3/4 facts were true.
````

Actually, since this function is quite simple we can actually cover the entire input space with two facts (subsuming the above facts):
````c
void max_fact_a_greater_than_b() {
  int a = _;
  int b = _;
  #ASSUME a > b
  int ret = max(a,b);
  #FACT ret == a
}

void max_fact_a_smaller_than_b() {
  int a = _;
  int b = _;
  #ASSUME a < b
  int ret = max(a,b);
  #FACT ret == b
}
````

From now on, we consider **max.facts** to only contain the last two unit facts:

````console
ptr@host:~$ ./falsify.sh max.c max.facts
Found 2 facts to be checked...
Fact  max_fact_a_greater_than_b : true
Fact  max_fact_a_smaller_than_b : true

2/2 facts were true.
````


### Coverage check
It is possible to check if all of the input space has been covered by the unit-facts. Note, for coverage to be well-defined the input space must be specificed. Currently, we check each function and see with what range of arguments it has been called. This process is *incomplete* and only takes into account variables which have been set during the set-up phase. To do this, use **coverage**:
````console
ptr@host:~$ ./coverage.sh -cover max.c max.facts
Found 1 functions to be checked...
Found 2 facts to be checked...

Coverage is *not* complete:
max: is missing ( ARG0: 0 ARG1: 0 )
````

This indicates that our coverage is not complete, and after checking the two unit facts it is indeed the case that none of the unit facts covers the case when *a* equals *b*. We mitigate it by weakening the strong inequality:

````c
void max_fact_a_greater_than_or_equal_to_b() {
  int a = _;
  int b = _;
  #ASSUME a >= b
  int ret = max(a,b);
  #FACT ret == a
}

void max_fact_a_smaller_than_or_equal_to_b() {
  int a = _;
  int b = _;
  #ASSUME a <= b
  int ret = max(a,b);
  #FACT ret == b
}
````

If we re-check coverage we see that all cases are now covered:

````console
ptr@host:~$ ./falsify.sh max.c max.facts
Found 1 functions to be checked...
Found 2 facts to be checked...

Coverage is complete for all functions found:  max
````
