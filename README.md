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
ptr@host:~$ falsify max.c max.facts
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
  #ASSUMPTION b < 0
  int ret = max(a,b);
  #FACT ret == 0
}
````

Now the fact is true, and thus we will get the following:
````console
ptr@host:~$ falsify max.c max.facts
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
  #ASSUMPTION a > 0
  #ASSUMPTION b < 0
  int ret = max(a,b);
  #FACT ret == a
}
````


