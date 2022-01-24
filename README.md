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

# Verification-Driven Development
As an analogue to test-driven development (TDD), we propose using unit-facts as a driving force for development. The developer gives facts (instead of tests) about the software intended to be written. When such a fact is falsified, the implementation is adjusted accordingly to make sure it becomes true. Then the code can be refactored, and all written facts can be used for regression. 

We demonstrate this methodology by writing a simple library capable of doing min and max. 

## Example: minmax
The goal here is to write a simple library which can return the maximum or minimum of two integers. We begin with the **max** function. The first step is to write the simples implementation possible:
````c
int max(int a, int b) {
    return 0;
}
````

We save this in the file **src/minmax.c**. Next we write our first fact:

````c
void max_fact_b_greater_than_a() {
    // Set-up
    int a = _;
    int b = _;
    #ASSUME a <= b
    
    int real = max(a, b);
    
    #FACT real == b
}
````

This is saved to the file **facts/minmax.facts**. Now we are ready to take the second step and check that our fact fails:

````console
ptr@host:~$ falsify src/max.c test/max.facts

Found 1 facts to be checked...
Fact  max_fact_0 : false ( a: 0 b: 1 real: 0  )

0/1 facts were true.
````

Here we see that in the case of *a* equals 0, and *b* equals 1, we get 0 (when we should have one). Let's fix the implementation. In the spirit of VDD, we make the smallest fix possible, i.e., always return b:

````c
int max(int a, int b) {
    return b;
}
````
Of course this will work for our single fact, but we add the symmetrical one:
````c
void max_fact_b_smaller_than_a() {
    // Set-up
    int a = _;
    int b = _;
    #ASSUME a >= b
    
    int real = max(a, b);
    
    #FACT real == a
}
````

Our check will now fail:

````console
ptr@host:~$ falsify src/max.c test/max.facts

Found 2 facts to be checked...
Fact  max_fact_b_greater_than_a : true
Fact  max_fact_b_smaller_than_a : false ( a: 0 b: -1 real: -1  )

1/2 facts were true.
````

The counter-example (*a* is zero, *b* is negative one) leads us to fix our implementation:

````c
int max(int a, int b) {
  if (a < b)
    return b;
  else
    return a;
````

Which will pass all test. We add the corresponding tests for the min-function (still in **minmax.facts**):
````c
void min_fact_b_greater_than_a() {
    // Set-up
    int a = _;
    int b = _;
    #ASSUME a <= b
    
    int real = min(a, b);
    
    #FACT real == a
}

void min_fact_b_smaller_than_a() {
    // Set-up
    int a = _;
    int b = _;
    #ASSUME a >= b
    
    int real = min(a, b);
    
    #FACT real == b
}
````
This will fail with dummy-implementation (now shown), so we write *min* using our already written *max* code:
````c
int min(int a, int b) {
  return a + b - max(a,b);
}
````

And in fact, this passes all the tests:

````console
ptr@host:~$ ./falsify.sh max.c max.facts
Found 4 facts to be checked...
Fact  max_fact_b_greater_than_a : true
Fact  max_fact_b_smaller_than_a : true
Fact  min_fact_b_greater_than_a : true
Fact  min_fact_b_smaller_than_a : true

4/4 facts were true.
````

We conclude our *minmax*-example by checking that we actually have full coverage with our facts:
````console
ptr@host:~$ ./falsify.sh max.c max.facts
Found 2 functions to be checked...
Found 4 facts to be checked...

Coverage is complete for all functions found:  max,min
````
