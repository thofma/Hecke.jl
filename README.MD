# Hecke

**Builds**

[![Build Status](https://travis-ci.org/thofma/Hecke.jl.svg?branch=master)](https://travis-ci.org/thofma/Hecke.jl)
[![Build status](https://ci.appveyor.com/api/projects/status/3qb0ce2h5melsjeb?svg=true)](https://ci.appveyor.com/project/thofma/hecke-jl)


## About

Hecke is a software package for algebraic number theory maintained by Claus Fieker, Tommy Hofmann and Carlo Sircana.
It is written in [julia](http://www.julialang.org) and is based on the computer algebra packages [Nemo](http://www.nemocas.org) and [AbstractAlgebra](https://github.com/Nemocas/AbstractAlgebra.jl).

- [https://github.com/thofma/Hecke.jl](https://github.com/thofma/Hecke.jl) (Source code)
- [http://thofma.github.io/Hecke.jl/latest/](http://thofma.github.io/Hecke.jl/latest/) (Online documentation)

So far, Hecke provides the following features:

  - Orders (including element and ideal arithmetic) in relative and absolute number fields
  - Class and unit group computation
  - Computation of maximal orders
  - Extensions of number Fields (relative fields)
  - Non-simple fields
  - Lattice enumeration
  - Sparse linear algebra
  - Class field theory
  - Abelian Groups

## Installation

To use Hecke, a julia version of 1.0 is necessary (the latest stable julia version will do).
Please see [http://julialang.org/downloads](http://julialang.org/downloads/) for instructions on how to obtain julia for your system.
Once a suitable julia version is installed, use the following steps at the julia prompt to install Hecke:

```julia
julia> using Pkg
julia> Pkg.add("Hecke")
```

## Quick start

Here is a quick example of using Hecke:

```julia
julia> using Hecke
...

Welcome to 

  _    _           _        
 | |  | |         | |       
 | |__| | ___  ___| | _____ 
 |  __  |/ _ \/ __| |/ / _ \
 | |  | |  __/ (__|   <  __/
 |_|  |_|\___|\___|_|\_\___|
  
Version 0.5 ... 
 ... which comes with absolutely no warrant whatsoever
(c) 2015-2018 by Claus Fieker, Tommy Hofmann and Carlo Sircana

julia> Qx, x = PolynomialRing(FlintQQ, "x");
julia> f = x^3 + 2;
julia> K, a = NumberField(f, "a");
julia> O = maximal_order(K);
julia> O
Maximal order of Number field over Rational Field with defining polynomial x^3 + 2 
with basis [1,a,a^2]
```

## Documentation

The online documentation can be found here: [http://thofma.github.io/Hecke.jl/latest/](http://thofma.github.io/Hecke.jl/latest/)

The documentation of the single functions can also be accessed at the julia prompt. Here is an example:

```
help?> signature
search: signature

  ----------------------------------------------------------------------------

  signature(O::NfMaximalOrder) -> Tuple{Int, Int}

  |  Returns the signature of the ambient number field of \mathcal O.
```
