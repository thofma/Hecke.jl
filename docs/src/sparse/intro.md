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

Rows support the usual operations:

- `+`, `-`, `==`
- multiplication by scalars
- `div`, `divexact`

```@docs
getindex(::SRow{fmpz}, ::Int)
add_scaled_row(::SRow{fmpz}, ::SRow{fmpz}, ::fmpz)
add_scaled_row(::SRow{T}, ::SRow{T}, ::T) where {T}
transform_row(::SRow{T}, ::SRow{T}, ::T, ::T, ::T, ::T) where {T}
length(::SRow)
```

### Change of base ring

```@docs
change_base_ring(::FlintIntegerRing, ::SRow{fmpz})
```

### Maximum, minimum and 2-norm

```@docs
maximum(::SRow)
maximum(::SRow{fmpz})
minimum(::SRow{fmpz})
minimum(::SRow)
norm2(::SRow{fmpz})
```

### Functionality for integral sparse rows

```@docs
lift(::SRow{nmod})
mod!(::SRow{fmpz}, ::fmpz)
mod_sym!(::SRow{fmpz}, ::fmpz)
mod_sym!(::SRow{fmpz}, ::Integer)
maximum(::typeof(abs), ::SRow{fmpz})
```

## Sparse matrices

Let $R$ be a commutative ring. Sparse matrices with base ring $R$ are modelled by
objects of type `SMat`. More precisely, the type is of parametrized form `SRow{T}`, where `T` is the element type of the base ring.
For example, `SMat{fmpz}` is the type for sparse matrices over the integers.

In constrast to sparse rows, sparse matrices have a fixed number of rows and columns,
that is, they represent elements of the matrices space $\mathrm{Mat}_{n\times m}(R)$.
Internally, sparse matrices are implemented as an array of sparse rows.
As a consequence, unlike their dense counterparts, sparse matrices have a mutable number of rows and it is very performant to add additional rows.

### Construction
```@docs
sparse_matrix(::Ring)
```

Sparse matrices can also be created from dense matrices as well as from julia arrays:

```@docs
sparse_matrix(::MatElem; keepzrows)
sparse_matrix(::Matrix{T}) where {T}
sparse_matrix(::Ring, ::Matrix{T}) where {T}
```
The normal way however, is to add rows:

```@docs
push!(::SMat{T}, ::SRow{T}) where {T}
```

Sparse matrices can also be concatenated to form larger ones:
```@docs
vcat!(::SMat{T}, ::SMat{T}) where {T}
vcat(::SMat{T}, ::SMat{T}) where {T}
hcat!(::SMat{T}, ::SMat{T}) where {T}
hcat(::SMat{T}, ::SMat{T}) where {T}
```
(Normal julia ``cat`` is also supported)

There are special constructors:
```@docs
identity_matrix(::Type{SMat}, ::Ring, ::Int)
zero_matrix(::Type{SMat}, ::Ring, ::Int)
zero_matrix(::Type{SMat}, ::Ring, ::Int, ::Int)
```
Slices:
```@docs
sub(::SMat{T}, ::UnitRange, ::UnitRange) where {T}
```

Transpose:
```@docs
transpose(A::SMat)
```

### Elementary Properties
```@docs
sparsity(::SMat)
density(::SMat)
nnz(::SMat)
nrows(::SMat)
ncols(::SMat)
isone(::SMat)
iszero(::SMat)
isupper_triangular(::SMat)
maximum(::SMat)
minimum(::SMat)
maximum(::typeof(abs), ::SMat{fmpz})
elementary_divisors(::SMat{fmpz})
Hecke.solve_dixon_sf(::SMat{fmpz}, ::SRow{fmpz})
Hecke.hadamard_bound2(::SMat)
Hecke.echelon_with_transform(::SMat{nmod})
Hecke.reduce_full(::SMat{fmpz}, ::SRow{fmpz})
hnf!(::SMat{fmpz})
hnf(::SMat{fmpz})
snf(::SMat{fmpz})
hnf_extend!(::SMat{fmpz}, ::SMat{fmpz})
is_diagonal(::SMat)
det(::SMat{fmpz})
det_mc(::SMat{fmpz})
valence_mc(::SMat)
saturate(::SMat{fmpz})
Hecke.hnf_kannan_bachem(::SMat{fmpz})
diagonal_form(::SMat{fmpz})
```
### Manipulation/ Access
```@docs
getindex(::SMat{T}, ::Int, ::Int) where {T}
getindex(::SMat{T}, ::Int) where {T}
setindex!(::SMat{T}, ::SRow{T}, ::Int) where {T}
swap_rows!(::SMat, ::Int, I::Int)
swap_cols!(::SMat, ::Int, I::Int)
scale_row!(::SMat{T}, ::Int, ::T) where {T}
add_scaled_col!(::SMat{T}, ::Int, ::Int, ::T) where {T}
add_scaled_row!(::SMat{T}, ::Int, ::Int, ::T) where {T}
transform_row!(::SMat{T}, ::Int, ::Int, ::T, ::T, ::T, ::T) where {T}
diagonal(::SMat)
reverse_rows!(::SMat)
mod_sym!(::SMat{fmpz}, ::fmpz)
find_row_starting_with(::SMat, ::Int)
reduce(::SMat{fmpz}, ::SRow{fmpz}, ::fmpz)
reduce(::SMat{fmpz}, ::SRow{fmpz})
reduce(::SMat{T}, ::SRow{T}) where {T <: FieldElement}
rand_row(::SMat{T}) where {T}
```

Changing of the ring:
```@docs
map_entries(f, ::SMat)
change_base_ring(::Ring, ::SMat)
```

### Arithmetic
Matrices support the usual operations as well

- `+`, `-`, `==`
- `div`, `divexact` by scalars
- multiplication by scalars

Various products:
```@docs
Hecke.mul(::SMat{T}, ::AbstractVector{T}) where {T}
Hecke.mul(::SMat{T}, ::AbstractMatrix{T})  where {T}
Hecke.mul(::SMat{T}, ::MatElem{T}) where {T}
Hecke.mul(::SRow{T}, ::SMat{T}) where {T}
```

Other:
```@docs
sparse(::SMat)
fmpz_mat(::SMat{fmpz})
fmpz_mat(::SMat{T}) where {T <: Integer}
Array(::SMat{T}) where {T}
```

