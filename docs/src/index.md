```@raw html
---
# https://vitepress.dev/reference/default-theme-home-page
layout: home

hero:
  name: "Hecke"
  tagline: Computational number theory for everyone
  actions:
    - theme: alt
      text: Getting Started
      link: /start/
    - theme: alt
      text: Manual
      link: /manual/
    - theme: alt
      text: View on Github
      link: https://github.com/thofma/Hecke.jl

features:
  - title: What is Hecke?
    details: Hecke is a software package for computational algebraic number theory. It is written in julia and makes use of the computer algebra packages Nemo and AbstractAlgebra.
  - title: OSCAR
    details: Hecke is part of the [OSCAR](https://www.oscar-system.org/) system, which covers, in addition to number theory, also commutative algebra, algebraic geometry, group theory and polyhedral geometry.
---
```

## Features

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
- Quadratic and Hermitian forms and lattices

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

## Acknowledgement

Hecke is part of the [OSCAR](https://www.oscar-system.org/) project and the development is supported by the Deutsche Forschungsgemeinschaft DFG within the Collaborative Research Center TRR 195.
