# Changelog

All notable changes to this project will be documented in this file.

## [0.35.15](https://github.com/thofma/Hecke/releases/tag/v0.35.15) - 2025-03-16

The following gives an overview of the changes compared to the previous release. This list is not
complete, many more internal or minor changes were made, but we tried to only list those changes
which we think might affect some users directly.

### Other changes

#### Bugfix

- [#1807](https://github.com/thofma/Hecke.jl/pull/1807) Fix interminated doctest

## [0.35.14](https://github.com/thofma/Hecke/releases/tag/v0.35.14) - 2025-03-15

The following gives an overview of the changes compared to the previous release. This list is not
complete, many more internal or minor changes were made, but we tried to only list those changes
which we think might affect some users directly.

### Number fields

#### New features or extended functionality

- [#1798](https://github.com/thofma/Hecke.jl/pull/1798) Add official support for `subfield`
- [#1797](https://github.com/thofma/Hecke.jl/pull/1797) Add `is_isomorphic` for local fields

### Noncommutative algebras

#### Bugfix

- [#1793](https://github.com/thofma/Hecke.jl/pull/1793) Disallow standard quaternion algebras in characteristic 2
- [#1791](https://github.com/thofma/Hecke.jl/pull/1791) Restore caching of maximal orders
- [#1789](https://github.com/thofma/Hecke.jl/pull/1789) Remove wrong `degree(::MatAlgebra)` implementation

#### New features or extended functionality

- [#1802](https://github.com/thofma/Hecke.jl/pull/1802) Add `schur_index_over_center` for arbitrary algebras
- [#1795](https://github.com/thofma/Hecke.jl/pull/1795) Improvements for quaternion algebra (elements)

### Other changes

#### New features or extended functionality

- [#1790](https://github.com/thofma/Hecke.jl/pull/1790) Add group theoretic `rank` for finitely generated abelian groups

## [0.35.13](https://github.com/thofma/Hecke/releases/tag/v0.35.13) - 2025-03-01

The following gives an overview of the changes compared to the previous release. This list is not
complete, many more internal or minor changes were made, but we tried to only list those changes
which we think might affect some users directly.

### Number fields

#### New features or extended functionality

- [#1779](https://github.com/thofma/Hecke.jl/pull/1779) Add `is_cyclotomic_polynomial_with_data`

### Function fields

#### New features or extended functionality

- [#1781](https://github.com/thofma/Hecke.jl/pull/1781) Add factoring over inseparable extensions

### Other changes

#### Bugfix

- [#1785](https://github.com/thofma/Hecke.jl/pull/1785) Fix `euler_phi_inv(1)`

