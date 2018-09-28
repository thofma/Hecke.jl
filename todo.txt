General
------

DONE * Provide an assert macro with different levels
DONE * Provide a macro for verbose print 
 * Provide (prototype) documentation in the following formats:
   REPL using @doc, html, as well as pdf
 * Copyright information (BSD 2-clause) in each file
 * (Move hecke to own julia package)
 * Build a (user)sysimage to speed up starting time

NfOrder
-------

 * implement Montes--Nart algorithm
 * composite Dedekind criterion
 * composite Round Two algorithm
(DONE) * clever maximal order computation using the above
 * implement information about containment (O_1 \sub O_2) 
 * save prime factors of discriminant
DONE * allow maximal order computation with information about prime divisors
 * write tests
 * write doc

NfMaximalOrder
--------------

delete * implement it so that transition PariMaximalOrder -> NfMaximalOrder is smooth
 * write tests
 * write doc

Lattices?
---------

 * think about it

Polynomials
-----------
  
  * trail vs trailing_coefficient ...

General:
--------
(DONE) * divisors, square_divisors, prime_divisors of ideals, integers, polys
   as iterators (replacing the terrible function in ElipticCurve)
DONE * inverse_phi

