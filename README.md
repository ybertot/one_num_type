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
is a rational numbers.  This brings about the notion of divisibility.

Thanks to this approach, the subtraction between two numbers is always written
as a subtraction between real numbers, and the meaning of this operation is
always "natural" to the eye of mathematicians and students.  Whether the result
is a natural number can be explained and reasoned about.  By comparison,
if one had been using subtraction between natural numbers, reasoning on the
fact that the result is a natural number is really possible (it is a natural
number by force due to typing) and what needs to be reasoned about is whether
the result is the expected value.

# Defining functions on integers and natural numbers

Once numeric functions are all defined as function from type R to type
R, there remains the difficulty that some functions are really meant
as functions from integers or natural numbers to natural numbers.  How could
these functions be defined, so that their use remains natural.  We
propose that definitions should rely on one of the following
approaches:

# TODO rework starting from here
 - We can define a function IRZ (resp. IRN) from R to Z (resp. nat) which
   associates to every real
   number the corresponding integer (resp. natural number).  The key
   property of this
   function is that when x is an integer real number, then IZR (IRZ x)
   = x.  This function can then be composed with existing function on
   type Z to obtain the corresponding function on real numbers.  The
   students should never have to study this definition, and the main
   *defining* properties of the functions should be provided by the
   library developer (these properties can usually be proved from the
   definition).  An example of this approach is given in file
   `binomial/binomial_exp.v` for the factorial function.
 - We can use an induction principle on the property of "being an
   integer" or "being a natural number" to show that the value
   expected for a function can be defined, and then use Hilbert's
   choice operator to define the function satisfying the expected
   recursive equation.  I expect that a fairly large amount of
   apparatus should be provided to make this kind of definitions
   practical.
 - We can provide once and for all a function taking as input a
   real number n, and returning the sequence 0 1, ..., n (here the
   sequence can be chosen to be either undetermined if n is not a
   natural number, or the sequence limited to the integral part of n
   in all cases, i.e., the largest real number k that is a natural
   number such that k <= n).  This sequence can then be passed as
   argument to a recursive function on lists, or to an iterated
   operator.  If this kind of definition needs to be shown to
   students, then they need to have a good understanding of iterated
   operations (big sums and big products), or maybe they need to have
   a training in programming recursive function on sequences.

If we think of the factorial function, it should be rather easy to
define using any of these technique.  On the other hand, sequences
that are naturally given by a recursive scheme, like the Fibonacci
sequence, will probably better rely on the second technique, which
needs to receive proper attention.

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

## a form of weak typing

The proof that a formula satisfies a "sub-type" predicate usually
exploits stability properties with respect to the basic operations.
To this, "sub-type" information should be added to the functions being
considered.  For instance, it should be recorded that the factorial
function maps integers to integers (or even natural numbers to natural
numbers).

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
recursive function whose value can be computed in fairly short time.

If the objective is to use a type theory based proof system to help
students learn mathematics, it may be counter-productive to teach them
all the competence required to program recursively with these
datatypes.  However, the library developer may want to provide
experimenting facilities so that students test running the functions
provided to them in personal experiments.  In the current setting,
We have been experimenting with the capability to compute functions
from real numbers to real numbers, even though this type is not an
inductive type and thus not equipped with the same computation
capability.

The key to this capability to compute is to exploit the theorem
stating that IZR is the left inverse of IRZ and the fact that any
integer constant in Coq is given as an instance of IZR.  For instance,
the file binomial/binomial_exp.v contains an instance of a tactic
called `compute_factorial` which recognizes instances of the factorial
function applied to an integer constant and replace these instances by
their value.

This tactic should be made more generic, so that it can easily be
extended to compute the value of any real number function, as soon as
an executable representant is provided by the library developer as
function from Z to Z.

# Definition of recursive functions

It is quite easy to define a recursor of type:

```
Rnat_rec : A -> (R -> A -> A) -> R -> A
```
where the argument is the value in 0, the second argument tells how
to compute the value in n+1, given the value n and the value in n.

However, a definition given using `Rnat_rec` is not as readable as desired.
For instance, the recursive function on natural numbers such that
`f 0 = v0` and  `f n = B n (f (n - 1))` when `n` is a natural larger than
0 would be described as :
```
Definition f := Rnat_rec v0 (fun n v => B n v).
```
It is not immediately visible that `f n = B n (f (n - 1))`.

Instead, we propose to write a piece of code that takes as input, the
expected theorem explaining the behavior of the function, in this form:
```
Recursive (def f such that (f 0 = v0 /\
    (forall n, Rnat (n - 1) -> f n = B n (f (n - 1))).
```
From this expression, the command would generate the value:
```
Rnat_rec v0 B
```

This command should be made adaptable to the case, where several initial
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

Recursive (def fib such that f 0 = 0 /\ f 1 = 1 /\
      forall n, Rnat (n - 2) -> f n = f (n - 2) + f (n - 1)).

Executing this commands has the effect of adding two constants in the
Coq context.  A constant `fib` and a constant `fib_eqn` such that `fib` has
type `R -> R` and `fib_eqn` is a proof of

```
f 0 = 0 /\ f 1 = 1 /\
forall n : R, Rnat (n - 2) -> f n = f (n - 2) + f (n - 1)
```

Note that `fib_eqn` can help reason on the value of `fib` for any argument
that is a real number in the `Rnat` subset.  It does not provide any help to
reason about the value of `f` for inputs that are not natural numbers.

# computation

When defining a function over an inductive type, computation is provided for
free.  Thus after defining addition and multiplication as they are given
for natural numbers, we can use the proof assistant as a pocket calculator and
obtain values for arbitrary inputs.

For instance, we can ask to compute the value `4237 + 1345` by just typing
the following command, in a context where numerical values are automatically
interpreted as natural numbers or integers.

```
Compute 4237 + 1345.
```
This returns the expeected value `5582`

On the other hand, when the numerical values are automatically interpreted as
real numbers, such a computation returns a disappointing result.

```
Require Import Reals.

Open Scope R_scope.

Compute 4237 + 1345.
```
The result is 
```
    = R1 +
       (R1 + R1) *
       ((R1 + R1) *
        (R1 +
         (R1 + R1) *
         (R1 +
          (R1 + R1) *
          ((R1 + R1) *
           ((R1 + R1) *
            ((R1 + R1) *
             (R1 +
              (R1 + R1) * ((R1 + R1) * ((R1 + R1) * ((R1 + R1) * (R1 + R1))))))))))) +
       (R1 +
        (R1 + R1) *
        ((R1 + R1) *
         ((R1 + R1) *
          ((R1 + R1) *
           ((R1 + R1) *
            ((R1 + R1) *
             (R1 + (R1 + R1) * ((R1 + R1) * (R1 + (R1 + R1) * (R1 + R1))))))))))
     : R
```
This is not interesting: this result is actually the sum of two numbers,
where each of them is described as binary encoding (successions of
multiplication by 2 and additions of 1).

If we wish to recover computing capabilities we need to exploit the following
characteristics.

 - A numeral in R, when it is a natural number, is represented as `IZR z`,
  where `z` is the corresponding integer (of type `Z`).
 - There is a collections of theorems expressing the morphism properties of
  the injection of integers into real numbers.  In particular for addition,
  there is a theorem named `plus_IZR` with the following statement.

```
    forall n m : Z, IZR (n + m) = IZR n + IZR m
```
  - The expression `4237 + 1345` can be rewritten thanks to `plus_IZR` into
    `IZR (4237 + 1345)` where the expressions between parentheses is
    an integer of type `Z`, and Coq can compute that addition to a ground
    value.  In the context of a goal, this can be done in this manner.

```
    match goal with |- context [IZR ?v] => 
      let v' := eval compute in v in change v with v'
    end.
```

  - If the expression one wishes to compute contains only basic operations,
    the `ring_simplify` tactic can be used instead.

  - However, a recursive definition like `fib` can be coupled with a `fibz`
    function of type `Z -> Z` such that `fib (IZR z) = IZR (fibz z)`.  The
    function `fibz` can be computed by Coq.  the function `fibz` should be
    constructed automatically at the time `fib` is constructed: it has
    the same definition, just replacing operations on real numbers with
    operations on integers.