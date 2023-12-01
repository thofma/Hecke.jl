# Hecke

## About

Hecke is a software package for algebraic number theory maintained by Claus Fieker, Carlo Sircana and Tommy Hofmann.
It is written in [julia](https://www.julialang.org) and is based on the computer algebra package [Nemo](https://github.com/Nemocas/Nemo.jl).

- <https://github.com/thofma/Hecke.jl> (Source code)
- <https://thofma.github.io/Hecke.jl/dev/> (Online documentation)

So far, Hecke provides the following features:

  - Orders (including element and ideal arithmetic) in number fields
  - Computation of maximal orders
  - Verified residue computations of Dedekind zeta functions
  - Class and Unit group computation, S-units, PID testing
  - Lattice enumeration
  - Sparse linear algebra
  - Normal forms for modules over maximal orders
  - Extensions of number fields, non-simple extensions of number fields
  - Orders and ideals in extensions of fields
  - Abelian groups
  - Ray class groups, quotients of ray class groups
  - Invariant subgroups
  - Class Field Theory
  - Associative Algebras

## Installation

To use Hecke, a julia version of 1.6 is necessary (the latest stable julia version will do).
Please see <https://julialang.org/downloads/> for instructions on how to obtain julia for your system.
Once a suitable julia version is installed, use the following steps at the julia prompt to install Hecke:

```julia
julia> using Pkg
julia> Pkg.add("Hecke")
```

## Quick start

Here is a quick example of using Hecke:

```julia
julia> using Hecke

Welcome to

    _    _           _
   | |  | |         | |
   | |__| | ___  ___| | _____
   |  __  |/ _ \/ __| |/ / _ \
   | |  | |  __/ (__|   <  __/
   |_|  |_|\___|\___|_|\_\___|

Version 0.22.8...
 ... which comes with absolutely no warranty whatsoever
(c) 2015-2023 by Claus Fieker, Tommy Hofmann and Carlo Sircana


julia> Qx, x = polynomial_ring(FlintQQ, "x");

julia> f = x^3 + 2;

julia> K, a = number_field(f, "a");

julia> O = maximal_order(K);

julia> O
Maximal order of Number field of degree 3 over QQ
with basis nf_elem[1, a, a^2]
```

The documentation of the single functions can also be accessed at the julia prompt. Here is an example:

```
help?> absolute_degree
search: absolute_degree absolute_inertia_degree absolute_coordinates is_absolutely_irreducible

  absolute_degree(a::FqField)

  Return the degree of the given finite field over the prime field.

  ─────────────────────────────────────────────────────────────────────────────────────────────────

  absolute_degree(L::NumField) -> Int

  Given a number field L/K, this function returns the degree of L over \mathbf Q.
```

