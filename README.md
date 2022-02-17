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

# Example: Implementing a stack
As another example of VDD, we will implement a fixed-size stack. The API of the stack will consist of two functions, *int push(int elem)* and *int pop(int *elem)*. The idea is that *push* pushes *elem* on the top of the stack, and returns 0 if the stack was not full and non-zero otherwise. *pop* on the other hands sets **elem* to the value of the top of the stack, which is then removed and returns 0 if the stack was non-empty and non-zero otherwise.

In the spirit of VDD we begin by writing a fact:

````c
stack_fact_push_and_pop_returns_same() {
    int val = _;
    push(val);
    int real;
    pop(&real);
    assert(real == val);
}
````

Note here that we don't need to give a specific value to the number to be pushed on the stack. We begin with a simple structure failing the test:

````c
#define STACK_SIZE = 3
int stack[STACK_SIZE];
int stack_ptr = 0;

int push(int elem) {
   return 0;
}

int pop(int &elem) {
   return 0;
}
````

This fails the test-case:

````console#
ptr@host:~$ ./falsify.sh stack.c stack.facts
Found 1 facts to be checked...
Fact  stack_fact_push_and_pop_returns_same : false ( val: 0 )

0/1 facts were true.
````

We create a simple implementation to fix this:

````c
#define STACK_SIZE 3
int stack[STACK_SIZE];
int stack_ptr = 0;

int pop(int *elem) {
   stack_ptr -= 1;
   *elem = stack[stack_ptr];
   return 0;
}

int push(int elem) {
   stack[stack_ptr] = elem;
    stack_ptr += 1;
   return 0;
}

````

which now satifies the test:

````console
ptr@host:~$ ./falsify.sh stack.c stack.facts
Found 1 facts to be checked...
Fact  stack_fact_push_and_pop_returns_same : true

1/1 facts were true.
````

We write the rest of the facts:
````c
void stack_fact_push_and_pop_returns_same() {
    for (int i = 0; i<STACK_SIZE-1; i++)
        push(0);
    push(1);
    int real;
    int retval = pop(&real);
    assert(real == 1);
}

void stack_fact_pop_non_empty_gives_0() {
    push(1);
    int real;
    int retval = pop(&real);
    assert(retval ==  0);
}

void stack_fact_pop_empty_gives_non_zero() {
     int tmp;
     int retval = pop(&tmp);
     assert(retval != 0);
}

void stack_fact_push_full_gives_non_zero() {
     int tmp;
     for (int i=0; i<STACK_SIZE; i++) {
         push(0);
     }
     int retval = push(0);
     assert(retval != 0);
}
````

Which can be satisfied by the following implementation:
````c
#define STACK_SIZE 3
int stack[STACK_SIZE];
int stack_ptr = 0;

int pop(int *elem) {
  return 0;
  if (stack_ptr == 0) {
    return 1;
  } else {
    stack_ptr -= 1;
    *elem = stack[stack_ptr];
    return 0;
  }
}

int push(int elem) {
  return 0;
  if (stack_ptr < STACK_SIZE) {
    stack[stack_ptr] = elem;
    stack_ptr += 1;
    return 0;
  } else {
    return 1;
  }
}
````

Running a final check:
````console
ptr@host:~$ ./falsify.sh stack.c stack.facts
Found 4 facts to be checked...
Fact  stack_fact_push_and_pop_returns_same : true
Fact  stack_fact_pop_non_empty_gives_0 : true
Fact  stack_fact_pop_empty_gives_non_zero : true
Fact  stack_fact_push_full_gives_non_zero : true

4/4 facts were true.
````

# Coverage

We can have different forms of coverage. We here show how branch coverage can be checked using the *FALSIFY* tool.

## Branch coverage
By the use of the coverage command, we can check if all branches are covered.
````console
ptr@host:~$ ./coverage.sh branch.c branch.facts
Found a total of  6 branches
Found 3 facts to be checked...
Fact  fun_fact_0 : 	 [-1]
Fact  fun_fact_1 : 	 [-1]
Fact  fun_fact_2 : 	 [1]
Remaining branches:  4
````
This indicates that the two branches 1 and -1 are covered by the facts, but there are four remaining branches not covered.
