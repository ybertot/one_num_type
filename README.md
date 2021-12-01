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