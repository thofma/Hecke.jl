# Hecke

**Builds**

[![Docs dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://thofma.github.io/Hecke.jl/dev)
[![Docs stable](https://img.shields.io/badge/docs-stable-blue.svg)](https://thofma.github.io/Hecke.jl/stable)
[![Build status](https://github.com/thofma/Hecke.jl/workflows/Run%20long%20tests/badge.svg?branch=master)](https://github.com/thofma/Hecke.jl/actions?query=workflow%3A%22Run-tests%22+branch%3Amaster)
[![Build status](https://ci.appveyor.com/api/projects/status/3qb0ce2h5melsjeb?svg=true)](https://ci.appveyor.com/project/thofma/hecke-jl)
[![Codecov](https://codecov.io/github/thofma/Hecke.jl/coverage.svg?branch=master&token=)](https://codecov.io/gh/thofma/Hecke.jl)

## About

Hecke is a software package for algebraic number theory maintained by Claus Fieker, Tommy Hofmann and Carlo Sircana.
It is written in [julia](https://www.julialang.org) and is based on the computer algebra packages [Nemo](https://www.nemocas.org) and [AbstractAlgebra](https://github.com/Nemocas/AbstractAlgebra.jl).
Hecke is part of the [OSCAR](https://oscar.computeralgebra.de/) project and the development is supported by the Deutsche Forschungsgemeinschaft DFG within the Collaborative Research Center TRR 195.

- <https://github.com/thofma/Hecke.jl> (Source code)
- <https://thofma.github.io/Hecke.jl/dev/> (Online documentation)

So far, Hecke provides the following features:

  - Number fields (absolute, relative, simple and non-simple)
  - Orders and ideals in number fields
  - Class and unit group computations of orders
  - Lattice enumeration
  - Sparse linear algebra
  - Class field theory
  - Abelian groups
  - Associative algebras
  - Ideals and orders in (semsimple) associative algebras
  - Locally free class groups of orders in semisimple algebras

## Installation

To use Hecke, a julia version of 1.0 is necessary (the latest stable julia version will do).
Please see <https://julialang.org/downloads/> for instructions on how to obtain julia for your system.
Once a suitable julia version is installed, use the following steps at the julia prompt to install Hecke:

```julia
julia> using Pkg
julia> Pkg.add("Hecke")
```

## Citing Hecke

If your research depends on computations done with Hecke, please consider giving us a formal citation:

- Claus Fieker, William Hart, Tommy Hofmann and Fredrik Johansson, [Nemo/Hecke: Computer Algebra and Number Theory Packages
  for the Julia Programming Language](https://doi.acm.org/10.1145/3087604.3087611). In: Proceedings of ISSAC '17, pages 157–164, New York, NY, USA, 2017. ACM.

```bib
@inproceedings{nemo,
    author = {Fieker, Claus and Hart, William and Hofmann, Tommy and Johansson, Fredrik},
     title = {Nemo/Hecke: Computer Algebra and Number Theory Packages for the Julia Programming Language},
 booktitle = {Proceedings of the 2017 ACM on International Symposium on Symbolic and Algebraic Computation},
    series = {ISSAC '17},
      year = {2017},
     pages = {157--164},
  numpages = {8},
       url = {https://doi.acm.org/10.1145/3087604.3087611},
       doi = {10.1145/3087604.3087611},
 publisher = {ACM},
   address = {New York, NY, USA},
}
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

Version 0.10.12...
 ... which comes with absolutely no warrant whatsoever
(c) 2015-2019 by Claus Fieker, Tommy Hofmann and Carlo Sircana

julia> Qx, x = PolynomialRing(FlintQQ, "x");
julia> f = x^3 + 2;
julia> K, a = NumberField(f, "a");
julia> O = maximal_order(K);
julia> O
Maximal order of Number field over Rational Field with defining polynomial x^3 + 2
with basis [1,a,a^2]
```

## Documentation

The online documentation can be found here:
- [stable](https://thofma.github.io/Hecke.jl/stable/)
- [dev](https://thofma.github.io/Hecke.jl/dev/)
