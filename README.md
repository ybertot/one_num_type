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
a basic operation on a pair of number, and vice-versa, it is
straightforward to project a pair of numbers to its first component,
but taking the first component of a number hardly makes any sense.

However, the tradition of type-theory based proof systems is to make a
strong distinction between several types of numbers, especially as way
to explain how the mathematical world is "constructed".  Often, one
starts by explaining the existence of type of natural numbers,
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
   will be prove by induction, etc).

However, there are a few oddities that make the whole construction at
odds with usual mathematical practice.

 - Type theory requires every function to be defined for every
   argument.  As a result, subtraction *m - n* has to be defined even
   when *n* is larger than m.  The usual practice is to decide that in
   this case *m - n = 0*, but this makes some properties of operations
   awkward to use:  For instance, *m - (m - n) = n* is true only when
   *n* is smaller than, or equal to *m*.  The mathematical practice
   concerning this kind of partial function is multiple.  For
   subtraction, people actually think that *m - n* exists when *n* is
   larger than *m*, but falls outside the set of natural number.  For
   division, another approach is used, which we shall discuss again
   later (TODO).

 - Computation, as provided by the concept of reduction in type
   theory, is only available for the types of numbers that are easily
   defined as inductive types.  However, the type of real numbers does
   not belong to that collection, and is less straight forward to give
   a meaning to the sentence "compute a formula".  For instance, what
   is the meaning of computing *PI + 1*?  The value *4.14* might be
   what the user expects, but it is an incorrect answer.

# A predicate for each type of number

In higher-order logic proof assistants, like Isabelle/HOL or HOL,
inductive type are defined by first exhibiting an inductive subset of
the working universe.  This 