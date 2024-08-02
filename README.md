# Example using Coq with only one numeric type

The objective of this experiment is to study the design of a library where
users only have to handle one numeric type, the type of real numbers, to
formalize mathematics.

The advantage of doing so is that all operations on numbers satisfy the
field properties.

Natural numbers are still provided, but as a subset of real numbers.
Functions defined by recursion on natural numbers should also be available,
but as function of type R to R, where the value is *undefined* when the input
is not a natural number.

As a first example, we provide a function Rnat_iter, which takes a number
n, a function f, and an initial value e, and returns the value f ^ n(e), when
n is a real number in the subset of natural numbers.

Using such a function, it is possible to compute the sequence of all real
numbers from 0 to n - 1 (a sequence of length n, containing only real
numbers that are in the subset of natural numbers), and to show that the
sum of all these numbers is (n * (n - 1) / 2).  Because we are working with
real numbers, subtraction and division do not need to be treated separately
(the ring and field tactic behave nicely).

Files should be separated in two layers:

 - A layer that is visible by the library developer, where all the surface
  concepts and the surface theorems are defined.  This layer may contain
  the usual inductive datatypes encountered in Coq.  It is used to guarantee
  that the library is consistent with traditional usage.

 - A layer that is visible by the library users, where only the surface
  concepts may be used: no value of type `nat` or `Z` should be used there.
  This layer should contain instructive examples.

# A discussion about types in an education context

The notion of type is quite natural, students understand naturally
that all numbers share a lot in common and are distinguished from
other objects in the mathematical world.  for instance, you can apply
the basic operations to a number (with the slight difficulty of
division and 0), but it is not straightforward what it means to apply
a basic operation like addition on a pair of number, and vice-versa, it is
straightforward to project a pair of numbers to its first component,
but taking the first component of a number hardly makes any sense.

However, the tradition of type-theory based proof systems is to make a
strong distinction between several types of numbers, especially as a way
to explain how the mathematical world is "constructed".  Often, one
starts by explaining the existence of a type of natural numbers,
followed by integers, rational numbers, and most often real numbers.

There are real benefits to doing so, in particular because most of the
basic operations can be described as programs, and the usual
properties of these operations are a consequence of the definition.
Let's list here some of the benefits:

 - In many of these types, numbers have a *canonical form*, which can
   be understood as *the value* of a formula.  When a number is given
   as a combination of operations on known values, the computation of
   all the programs can be required and the result displayed to the
   user.  This makes that the proof assistant can be used as
   calculator, for instance to perform experimental mathematics.

 - Each type of numbers comes with reasoning facilities that make it
   possible to get an intuitive grasp of important concepts from
   mathematics.  For instance, the type of natural numbers comes with
   the possibility to define recursive functions, which
   gives an opportunity to define many kinds of recursive sequences.
   Once the definitions are made, it is also possible to prove
   properties using the scheme of proof by induction, and the proof
   assistant helps students understanding the discipline that should
   come with this proving technique (be clear about what statement
   will be proved by induction, etc).

However, there are a few oddities that make the whole construction at
odds with usual mathematical practice.

 - Type theory requires every function to be defined for every
   argument in the input type.  As a result, subtraction
   *m - n* has to be defined even
   when *n* is larger than m.  The usual practice is to decide that in
   this case *m - n = 0*, but this makes some properties of operations
   awkward to use:  For instance, the equality *m - (m - n) = n* holds
   only when *n* is smaller than, or equal to *m*.  On the other hand,
   the mathematical practice
   concerning this kind of partial function is multiple.  For
   subtraction, people actually think that *m - n* exists when *n* is
   larger than *m*, but falls outside the set of natural number.  For
   division, another approach is used, which we shall discuss again
   later (TODO).

 - Computation, as provided by the concept of reduction in type
   theory, is only available for the types of numbers that are easily
   defined as inductive types.  However, the type of real numbers does
   not belong to that collection, and it is less straight forward to give
   a meaning to the sentence "compute a formula".  For instance, what
   is the meaning of computing *PI + 1*?  The value *4.14* might be
   what the user expects, but it is an incorrect answer.

# A predicate for each type of number

We propose to design a new library, staying at the level of
elementary facts, where different types of numbers are actually viewed
as subsets of the type of real numbers.  Several methods can be
used to define these subsets, either using inductive predicates, or
using the image of the functions injecting natural numbers and integers
in the real numbers.  In file `R_subsets.v` we show an implementation
using inductive predicates.  In file `R_nat_ind.v`, we show an implementation
using images of injections.  The file `binomial/binomial_exp.v` also contains
experiments based on inductive types, but this file is destined to be
decomposed in several smaller files.

Once the subsets corresponding to natural numbers and integers are defined,
one should also include tools to facilitate proofs that some real numbers
do belong in the subsets.  A first stage is to recover the facilities that
were automatically provided by typing: since addition, multiplication,
were automatically given as operations within the types nat and Z, we now have
to express stability laws.  Here, we see that subtraction and division must be
treated in an ad-hoc way: the subtraction of two natural numbers is an integer,
the division of two natural numbers or integers is a rational number
(at early stage of this library's development, the subset of rational numbers
has not been described yet).

Then, theorems should also be provided to express under what
conditions the subtraction of two numbers is a natural number, and this
comes with the notion of order.  Here we can exploit the existing order
between real numbers and all the monotonicity properties that basic operations
enjoy with respect to this order.

Similarly, one should study under what conditions the division of two integers
is a rational number.  This study brings about the notion of divisibility.

Thanks to this approach, the subtraction between two numbers is always written
as a subtraction between real numbers, and the meaning of this operation is
always "natural" to the eye of mathematicians and students.  Whether the result
is a natural number can be explained and reasoned about.  By comparison,
if one had been using subtraction between natural numbers, reasoning on the
fact that the result is a natural number is not really possible
(it is a natural number by force due to typing) and what needs to be
reasoned about is whether the result computed by the proof assistant
is the expected value, which makes the proof assistant look bad.

# Defining functions on integers and natural numbers

Once numeric functions are all defined as function from type R to type
R, there remains the difficulty that some functions are really meant
as functions from integers or natural numbers to natural numbers.  How could
these functions be defined, so that their usage remains natural.  We
propose that definitions visible by students should rely on one of the
following approaches:

 - For any function f of type A -> A, we can compute n iterations of
   f, where n is a real number in the natural number subset.

 - For any real numbers m and n, where n is a real number in the natural
   number subset, we can construct the sequence of numbers
   (m, m + 1, ... , m + n).  We should then provide a big-op construction
   (as in math-comp) for iteration of binary operations over such a sequence.
   This gives a nice way to describe the factorial function, for instance.

 - One should provide a syntax for the definition of recursive sequences
   of natural numbers.  This should make it possible to use multi-step
   recursion, as would be needed to define the Fibonacci sequence.

In all three cases, proof by induction on natural numbers should be enough
to make it possible for students to reason on the value of functions defined
using these tools.

Whatever the techniques used, many of the theorems explaining the
behavior of functions will have as pre-condition the fact that the
argument should be in the intended domain of definition (a natural
number or an integer).

# Replacing the support of type-checking by automatic proofs

To reason on expressions containing real functions that represent
natural number functions, this approach will rely on a collection of
theorems that have as premise the fact that the function's inputs are
indeed natural numbers.  This means many proof obligations will be
added that are only concerned with checking that some arguments of
type real satisfy the predicate "being a natural number".  For many of
these arguments, the proof should happen automatically, because the
considered arguments satisfy the predicate by assumption or by
construction.

For instance, the definition of a function describing the Fibonacci sequence
introduces a function `fib` and a theorem describing its behavior that
has the following shape:
```
fib 0 = 0 /\ fib 1 = 1 /\
forall n, Rnat (n - 2) -> fib n = fib (n - 2) + fib (n - 1)
```
Every time the third clause in this definition is used, a membership condition
in the `Rnat` subset needs to be proved.  This is non-trivial, because
subtraction is not automatically guaranteed to be a natural number,
even if the inputs are natural numbers.

An alternative presentation of the first clause is also possible:
```
forall n, Rnat n -> fib (n + 2) = fib n + fib (n + 1)
```
This presentation leads to membership condition that are easier to prove,
but instances of the equation's left hand side are then harder to detect.

In the context of mathematics education, the question is how much time do
the educators think the student should spend on verifying these
membership conditions.
## a form of weak typing

The proof that a formula satisfies a "sub-type" predicate usually
exploits stability properties with respect to the basic operations.
To this, "sub-type" information should be added to the functions being
considered.  For instance, it should be recorded that the factorial
function maps integers to integers (or even natural numbers to natural
numbers).

Having recorded that the `Rnat` subset is stable under addition,
multiplication, factorial, and that the immediate constants 0, 1, 2, etc
are natural numbers, it is a matter of automatic proof to show that
```
3 + 5 * factorial 12
```
is a member of `Rnat`.

Moreover, in the presence of an unknown `n` such that `Rnat n` holds,
the automatic procedure can also prove that
```
n + 5 * factorial n
```
is a member of `Rnat`.

When defining a new function, such as the `fib` function used in a previous
example, proving that such a function always returns a natural number is
also possible.  It should probably be used as an exercise in natural number
recursion at early stages of training, but this kind of proof can probably also
be automated (see file `rec_def_examples.v`).

Sometimes, the "weak typing information" is part of the folklore, but
it may not be easily recoverable from the definition, or at least not
without a proof.  For instance, when a formula contains a subtraction
of natural numbers, it is not guaranteed that the result will be a
natural number (but it will be an integer).  

A typical difficulty appears when using division or subtraction to
define a new value.  For instance, file binomial/binomial_exp.v
contains a definition of binomial n m as a division of factorials.
Because factorial returns integers, we can expect the result to be a
rational number, but specific properties of this function (which require
a specific proof, actually based on induction) guarantee that the
result is always an integer if the inputs are within the correct bounds.

# Recovering partial computation capabilities

One of the great qualities of Type Theory based proof system is that
they can be used to perform experimental mathematics: the inductive
type used for natural numbers and integers support the definition of
recursive functions whose value can be computed in fairly short time, as
long as they are applied to *immediate* natural number or integer values.

when using the type of real numbers, computations are blocked, because
multiplication, addition, etc, are now opaque constants with the computation
behavior only described by rewriting theorems.

However, it is possible to develop a computation facility that relies on
a mapping from functions on real numbers to functions on integers.  A command
`R_compute` is described in file `R_compute.v`.  Examples of usage are
presented in `rec_def_examples.v`

As a first stage, it is possible to provide this computation facility without
formal guarantees, where the educator provides a `Z` function for each
`R` function and no equivalence theorem.  This immediately provides the
possibility to compute values, but not to use such a computation in proofs.
The pairs of functions are simply stored in a table and a symbolic
manipulation transforms the formula to compute (of type R) into a formula
(of type Z) where the proof assistant's conversion mechanism can reduce
the `Z` functions.

Here is an example.  The system comes with the following pairs already
recorded : `(Rplus, Z.add)`, `(Rminus, Z.sub)`, `(Ropp, Z.opp)`, and each
number for instance the number `42` is automatically in correspondence with
the same number `42` in type Z.  The educator provides definitions for
the `fib` sequence and the `factorial` function using the recursive
definition command developed for this purpose.  The function
`fib_Z_mirror` and `factorial_Z_mirror` are generated automatically using
another command described in file `R_compute.v` and automatically added
in the database.

```
Recursive (def fib such that fib 0 = 0 /\ fib 1 = 1 /\
  (forall n, Rnat (n - 2) -> fib (n - 2) = fib (n - 2) + fib (n - 1))).

Elpi mirror_recursive_definition fib.

Recursive (def factorial such that factorial 0 = 1 /\
  forall n, Rnat (n - 1) -> factorial n = n * factorial (n - 1)).

Elpi mirror_recursive_definition factorial.

Elpi R_compute (42 + fib (factorial 4)).
```

Under the hood, this work by replacing the formula
```
Rplus (IZR 42) (fib (factorial (IZR 4)))
```
with the following formula:
```
IZR (Z.add 42 (fib_Z_mirror (factorial_Z_mirror 5)))
```
There is a single `IZR` instance in this new formula and its argument
is a formula that the proof assistant's conversion capability can
reduce to a numeric constant (in this case a number whose decimal has around
30 digits).

The replacement is performed by a simple traversal program that builds the
translated formula recursively, using elements of the function pair table to
construct a well-typed integer expression that can then be reduced by the
proof assistant.

When correctness theorems are provided for the pairs of functions, these
theorems can be used inside proofs.  An advanced version of the computation
capabilities should provided a tactic equivalent to the `R_compute` function
described above.  It is not clear whether such a computation capability inside
proofs will be very useful in an educational context.

# Definition of recursive functions under the hood

It is quite easy to define a recursor of type:

```
Rnat_rec : A -> (R -> A -> A) -> R -> A
```
where the first argument is the value in 0, the second argument tells how
to compute the value in n+1, given the value n and the value in n.

However, a definition given using `Rnat_rec` is not as readable as desired.
For instance, the recursive function on natural numbers such that
`f 0 = v0` and  `f n = B n (f (n - 1))` when `n` is a natural larger than
0 would be described as :
```
Definition f := Rnat_rec v0 (fun n v => B n v).
```
It is not immediately visible that `f n = B n (f (n - 1))`.

Instead, we propose to write a piece of code that takes as input the
expected theorem explaining the behavior of the function, in this form:
```
Recursive (def f such that (f 0 = v0 /\
    (forall n, Rnat (n - 1) -> f n = B n (f (n - 1))).
```
From this expression, the command would generate the value (or something
similar):
```
Rnat_rec v0 B
```

This command can be adaptable to the case, where several initial
values are provided for base cases (for inputs 0, 1, and maybe more)
and the expression B make take more recursive calls (to (n - 1), (n -2), and
maybe more).

A first version of this command is described in file `rec_def.v` using the
`coq-elpi` metaprogramming extension of Coq.  At the time of writing these
lines, This command accepts multiple step recursion, where
several base values `f 0`, `f 1`, ... `f (k - 1)` and in the general case the
value of `f n` can depend all preceding values between `f (n - 1)`
`f (n - k)`.  This command defines the function `f` and also provides a single
theorem called `f_eqn` stating that `f` satisfies the required specification.

For instance, for the Fibonacci sequence, one write the following command.

```
Recursive (def fib such that f 0 = 0 /\ f 1 = 1 /\
      forall n, Rnat (n - 2) -> f n = f (n - 2) + f (n - 1)).
```

Executing this command has the effect of adding two constants in the
Coq context.  A constant `fib` and a constant `fib_eqn` such that `fib` has
type `R -> R` and `fib_eqn` is a proof of

```
f 0 = 0 /\ f 1 = 1 /\
forall n : R, Rnat (n - 2) -> f n = f (n - 2) + f (n - 1)
```

Note that `fib_eqn` can help reason on the value of `fib` for any argument
that is a real number in the `Rnat` subset.  It does not provide any help to
reason about the value of `f` for inputs that are not natural numbers.  In
a sense, `f` is undefined outside the subset of natural numbers.

Another provided command (`Elpi mirror_recursive_definition`) constructs a
similar function of type `Z -> Z` where
all operations on `R` replaced by corresponding operation on `Z`.  This
extra function to perform computations by exploiting the reductions facilities
that come with inductive types in the proof assistant.

# A few benefitting examples

## binomial function

The factorial function can be defined either as the product of
the sequence of the n first positive integers or as a recursive
sequence of integers.  Once the factorial function is provided, the binomial
of `n` and `m` can be defined using the ratio of factorials.

```
Definition binomial (n m : R) :=
  factorial n / (factorial (n - m) * factorial m).
```

This is well defined only when `n`, `m`, and `n - m` are natural numbers.

Traditional presentations in mathematics also rely on an alternative
presentation given by the following equalities (where n and m are natural
numbers and m < n).  This is known as Pascal's triangle.
```
binomial 0 0 = 1
binomial n 0 = 1
binomial n n = n
binomial (n + 1) (m + 1) = binomial n (m + 1) + binomial n m
```
And since traditional presentations in proof assistants rely on the type of
natural numbers, the binomial function is also extended to the case where
(m > n) by taking as convention that the binomial function returns 0 in that
case.

If we take the definition with the ratio of factorials, the various equations
in Pascal's triangle can be proved to hold, using a proof by induction.
