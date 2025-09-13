```@raw html
---
# https://vitepress.dev/reference/default-theme-home-page
layout: home

hero:
  name: "Hecke.jl"
  text: Computational number theory for everyone
  tagline: A fast, open-source computer algebra system for computational number theory
  image:
    src: /assets/modular/Hecke_logo_modular2.png
    alt: Hecke.jl
  actions:
    - theme: brand
      text: Getting Started
      link: /#Getting-Started
    - theme: alt
      text: Manual
      link: /manual/
    - theme: alt
      text: View on Github
      link: https://github.com/thofma/Hecke.jl

features:
  - title: What is Hecke?
    details: Hecke is a software package for computational algebraic number theory. It is written in the Julia programming language and makes use of the computer algebra packages Nemo.jl and AbstractAlgebra.jl.
    link: /#features

  - title: OSCAR
    details: Hecke is part of the OSCAR computer algebra system, which covers algebraic geometry, group theory, and polyhedral geometry in addition to number theory and commutative algebra.
    link: https://www.oscar-system.org/
---
```


# Getting Started

Hecke.jl is a software package for the Julia programming language.
Currently, Hecke.jl requires that a Julia version of at least 1.0 is installed (the latest stable Julia version will do).
See <https://julialang.org/downlaods/> for instructions on how to install Julia for your system.

Once a suitable version of Julia is installed, users can start a Julia REPL (e.g. by typing `julia` in the command line) and
then enter the following commands to add Hecke.jl to their installation.

```julia
julia> using Pkg

julia> Pkg.add("Hecke")
```

Afterwards, to use Hecke.jl in Julia, users can simply include the `using Hecke` command at the beginning of any session.

```julia
julia> using Hecke
 _    _           _
| |  | |         | |         |  Software package for
| |__| | ___  ___| | _____   |  algorithmic algebraic number theory
|  __  |/ _ \/ __| |/ / _ \  |
| |  | |  __/ (__|   <  __/  |  Manual: https://thofma.github.io/Hecke.jl
|_|  |_|\___|\___|_|\_\___|  |  Version 0.37.6

julia>
```

Here's a quick example of using Hecke.jl to define a number field and compute its class group.

```jldoctest
julia> using Hecke

julia> Qx, x = QQ[:x];

julia> f = x^2 - 2*3*5*7;

julia> K, a = number_field(f, :a);

julia> OK = maximal_order(K);

julia> C, mC = class_group(OK);

julia> C
(Z/2)^2
```

Other examples of Hecke's usage can be found in the [How-to Guides](@ref) section of this website.
More in-depth resources are provided by our [Tutorials](@ref hecke_tutorials), which are guided walkthroughs to using Hecke, and by the [Manual](@ref), which gives a complete list of Hecke's implemented functionality.

# Features

Hecke currently provides functionliaty to enable a number of computations in number theory and commutative algebra. Some of the features implemented by Hecke include:

- Number fields (absolute, relative, simple and non-simple),
- Orders and ideals in number fields,
- Class and unit group computations of orders,
- Lattice enumeration,
- Sparse linear algebra,
- Class field theory,
- Abelian groups,
- Associative algebras,
- Ideals and orders in (semisimple) associative algebras,
- Locally free class groups of orders in semisimple algebras,
- Quadratic and Hermitian forms and lattices.

See the [Manual](@ref) for a complete list of implemented functionality.

# Citing Hecke

If your research depends on computations done with Hecke, please consider giving us a formal citation:

- Claus Fieker, William Hart, Tommy Hofmann and Fredrik Johansson, [Nemo/Hecke: Computer Algebra and Number Theory Packages
  for the Julia Programming Language](https://doi.acm.org/10.1145/3087604.3087611). In: Proceedings of ISSAC '17, pages 157–164, New York, NY, USA, 2017. ACM.

```
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

# Contributing to Hecke

Hecke is an open-source software package licensed under the permissive BSD 2-Clause "Simplified" License. Copyright is held by Hecke's contributors <https://github.com/thofma/Hecke.jl/graphs/contributors>.

For users that would like to contribute to the development of Hecke.jl, please see the [For Developers](@ref) section of the manual.

# Acknowledgement

Hecke is part of the [OSCAR](https://www.oscar-system.org/) project and the development is supported by the Deutsche Forschungsgemeinschaft DFG within the Collaborative Research Center TRR 195.
