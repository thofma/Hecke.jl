# Sparse linear algebra

```@meta
CurrentModule = Hecke
```

## Introduction

This chapter deals with sparse linear algebra over commutative rings and fields.

Sparse linear algebra, that is, linear algebra with sparse matrices, 
plays an important role in various algorithms in algebraic number theory. For
example, it is one of the key ingredients in the computation of class groups
and discrete logarithms using index calculus methods.

## Sparse rows

Building blocks for sparse matrices are sparse rows, which are modelled by
objects of type \texttt{SRow}. More precisely, the type is of parametrized form
objects of type `SRow`. More precisely, the type is of parametrized form
`SRow{T}`, where `T` is the element type of the base ring $R$. For example,
`SRow{fmpz}` is the type for sparse rows over the integers.

It is important to note that sparse rows do not have a fixed number of columns,
that is, they represent elements of
$\{ (x_i)_i \in R^{\mathbb{N}} \mid x_i = 0 \text{ for almost all }i\}$.
In particular any two sparse rows over the same base ring can be added.

### Creation

```@docs
sparse_row(::FlintIntegerRing, ::Vector{Tuple{Int, fmpz}})
sparse_row(::FlintIntegerRing, ::Vector{Tuple{Int, Int}})
sparse_row(::FlintIntegerRing, ::Vector{Int}, ::Vector{fmpz})
```

### Basic operations

```@docs
==(::SRow{fmpz}, ::SRow{fmpz})
+(::SRow{fmpz}, ::SRow{fmpz})
getindex(::SRow{fmpz}, ::Int)
*(::fmpz, ::SRow{fmpz})
div(::SRow{fmpz}, ::fmpz)
divexact(::SRow{fmpz}, ::fmpz)
add_scaled_row(::SRow{fmpz}, ::SRow{fmpz}, ::fmpz)
```

### Change of base ring

```@docs
change_base_ring(::FlintIntegerRing, ::SRow{fmpz})
```

### Maximum, minimum and 2-norm

```@docs
maximum(::SRow{fmpz})
minimum(::SRow{fmpz})
norm2(::SRow{fmpz})
```

### Functionality for integral sparse rows

```@docs
lift(::SRow{nmod})
mod!(::SRow{fmpz}, ::fmpz)
mod_sym!(::SRow{fmpz}, ::fmpz)
maximum(::typeof(abs), ::SRow{fmpz})
```

## Sparse matrices

Let $R$ be a commutative ring. Sparse matrices with base ring $R$ are modelled by
objects of type `SMat`. More precisely, the type is of parametrized form `SRow{T}`, where `T` is the element type of the base ring.
For example, `SMat{fmpz}` is the type for sparse matrices over the integers.

In constrast to sparse rows, sparse matrices have a fixed number of rows and columns,
that is, they represent elements of the matrices space $\mathrm{Mat}_{n\times m}(R)$.
Internally, sparse matrices are implemented as an array of sparse rows. 
As a consequence, Unlike their dense counterparts, sparse matrices have a mutable number of rows and it is very performant to add additional rows.

### Construction
```@docs
sparse_matrix(::Ring)
```

Sparse matrices can also be created from dense matrices as well as from julia arrays:

```@docs
sparse_matrix(::MatElem; keepzrows)
sparse_matrix(::Array{T, 2}) where {T}
sparse_matrix(::Ring, ::Array{T, 2}) where {T}
```
The normal way however, is to add rows:

```@docs
push!(::SMat, ::SRow)
```


