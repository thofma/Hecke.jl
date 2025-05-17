# Hecke

**Builds**

[![Docs dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://docs.hecke.thofma.com/dev)
[![Docs stable](https://img.shields.io/badge/docs-stable-blue.svg)](https://docs.hecke.thofma.com/stable)
[![Build status](https://github.com/thofma/Hecke.jl/workflows/Run%20long%20tests/badge.svg?branch=master)](https://github.com/thofma/Hecke.jl/actions?query=workflow%3A%22Run-tests%22+branch%3Amaster)
[![Codecov](https://codecov.io/github/thofma/Hecke.jl/coverage.svg?branch=master&token=)](https://codecov.io/gh/thofma/Hecke.jl)

## About

Hecke is a software package for algebraic number theory maintained by Claus Fieker and Tommy Hofmann.
It is written in [julia](https://www.julialang.org) and is based on the computer algebra packages [Nemo](https://github.com/Nemocas/Nemo.jl) and [AbstractAlgebra](https://github.com/Nemocas/AbstractAlgebra.jl).
Hecke is part of the [OSCAR](https://www.oscar-system.org/) project and the development is supported by the Deutsche Forschungsgemeinschaft DFG within the Collaborative Research Center TRR 195.

- <https://github.com/thofma/Hecke.jl> (Source code)
- <https://docs.hecke.thofma.com> (Online documentation)

So far, Hecke provides the following features:

  - Number fields (absolute, relative, simple and non-simple)
  - Orders and ideals in number fields
  - Class and unit group computations of orders
  - Lattice enumeration
  - Sparse linear algebra
  - Class field theory
  - Abelian groups
  - Associative algebras
  - Ideals and orders in (semisimple) associative algebras
  - Locally free class groups of orders in semisimple algebras
  - Quadratic and Hermitian forms and lattices

An overview of the functionality of Hecke (in connection with OSCAR) can be found in

> "Number Theory", T. Hofmann & C. Fieker, in: The Computer Algebra System OSCAR. Springer Cham, 2025, 81-105.

available [here](https://doi.org/10.1007/978-3-031-62127-7_3) or from the [arXiv](https://arxiv.org/abs/2404.06858).

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

```
julia> using Hecke
 _    _           _          
| |  | |         | |         |  Software package for
| |__| | ___  ___| | _____   |  algorithmic algebraic number theory
|  __  |/ _ \/ __| |/ / _ \  |  
| |  | |  __/ (__|   <  __/  |  Manual: https://thofma.github.io/Hecke.jl
|_|  |_|\___|\___|_|\_\___|  |  Version 0.34.6

julia>  Qx, x = polynomial_ring(QQ, "x");

julia> f = x^3 + 2;

julia> K, a = number_field(f, "a");

julia> O = maximal_order(K);

julia> O
Maximal order of number field of degree 3 over QQ
with basis [1, a, a^2]
```

## Documentation

The online documentation can be found here:
- [stable](https://thofma.github.io/Hecke.jl/stable/)
- [dev](https://thofma.github.io/Hecke.jl/dev/)
