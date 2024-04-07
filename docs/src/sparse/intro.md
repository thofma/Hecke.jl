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
objects of type `SRow`. More precisely, the type is of parametrized form
`SRow{T}`, where `T` is the element type of the base ring $R$. For example,
`SRow{ZZRingElem}` is the type for sparse rows over the integers.

It is important to note that sparse rows do not have a fixed number of columns,
that is, they represent elements of
$\{ (x_i)_i \in R^{\mathbb{N}} \mid x_i = 0 \text{ for almost all }i\}$.
In particular any two sparse rows over the same base ring can be added.

### Creation

```@docs; canonical=false
sparse_row(::ZZRing, ::Vector{Tuple{Int, ZZRingElem}})
sparse_row(::ZZRing, ::Vector{Tuple{Int, Int}})
sparse_row(::ZZRing, ::Vector{Int}, ::Vector{ZZRingElem})
```

### Basic operations

Rows support the usual operations:

- `+`, `-`, `==`
- multiplication by scalars
- `div`, `divexact`

```@docs; canonical=false
getindex(::SRow{ZZRingElem}, ::Int)
add_scaled_row(::SRow{ZZRingElem}, ::SRow{ZZRingElem}, ::ZZRingElem)
add_scaled_row(::SRow{T}, ::SRow{T}, ::T) where {T}
transform_row(::SRow{T}, ::SRow{T}, ::T, ::T, ::T, ::T) where {T}
length(::SRow)
```

### Change of base ring

```@docs; canonical=false
change_base_ring(::ZZRing, ::SRow{ZZRingElem})
```

### Maximum, minimum and 2-norm

```@docs; canonical=false
maximum(::SRow)
maximum(::SRow{ZZRingElem})
minimum(::SRow{ZZRingElem})
minimum(::SRow)
norm2(::SRow{ZZRingElem})
```

### Functionality for integral sparse rows

```@docs; canonical=false
lift(::SRow{zzModRingElem})
mod!(::SRow{ZZRingElem}, ::ZZRingElem)
mod_sym!(::SRow{ZZRingElem}, ::ZZRingElem)
mod_sym!(::SRow{ZZRingElem}, ::Integer)
maximum(::typeof(abs), ::SRow{ZZRingElem})
```

### Conversion to/from julia and AbstractAlgebra types

```@docs; canonical=false
Vector(r::SRow, n::Int)
sparse_row(A::MatElem)
dense_row(r::SRow, n::Int)
```

## Sparse matrices

Let $R$ be a commutative ring. Sparse matrices with base ring $R$ are modelled by
objects of type `SMat`. More precisely, the type is of parametrized form `SRow{T}`, where `T` is the element type of the base ring.
For example, `SMat{ZZRingElem}` is the type for sparse matrices over the integers.

In contrast to sparse rows, sparse matrices have a fixed number of rows and columns,
that is, they represent elements of the matrices space $\mathrm{Mat}_{n\times m}(R)$.
Internally, sparse matrices are implemented as an array of sparse rows.
As a consequence, unlike their dense counterparts, sparse matrices have a mutable number of rows and it is very performant to add additional rows.

### Construction
```@docs; canonical=false
sparse_matrix(::Ring)
sparse_matrix(::Ring, ::Int, ::Int)
```

Sparse matrices can also be created from dense matrices as well as from julia arrays:

```@docs; canonical=false
sparse_matrix(::MatElem; keepzrows)
sparse_matrix(::Matrix{T}) where {T}
sparse_matrix(::Ring, ::Matrix{T}) where {T}
```
The normal way however, is to add rows:

```@docs; canonical=false
push!(::SMat{T}, ::SRow{T}) where {T}
```

Sparse matrices can also be concatenated to form larger ones:
```@docs; canonical=false
vcat!(::SMat{T}, ::SMat{T}) where {T}
vcat(::SMat{T}, ::SMat{T}) where {T}
hcat!(::SMat{T}, ::SMat{T}) where {T}
hcat(::SMat{T}, ::SMat{T}) where {T}
```
(Normal julia ``cat`` is also supported)

There are special constructors:
```@docs; canonical=false
identity_matrix(::Type{SMat}, ::Ring, ::Int)
zero_matrix(::Type{SMat}, ::Ring, ::Int)
zero_matrix(::Type{SMat}, ::Ring, ::Int, ::Int)
block_diagonal_matrix(xs::Vector{<:SMat{T}}) where {T}
```
Slices:
```@docs; canonical=false
sub(::SMat{T}, ::AbstractUnitRange, ::AbstractUnitRange) where {T}
```

Transpose:
```@docs; canonical=false
transpose(A::SMat)
```

### Elementary Properties
```@docs; canonical=false
sparsity(::SMat)
density(::SMat)
nnz(::SMat)
number_of_rows(::SMat)
number_of_columns(::SMat)
isone(::SMat)
iszero(::SMat)
is_upper_triangular(::SMat)
maximum(::SMat)
minimum(::SMat)
maximum(::typeof(abs), ::SMat{ZZRingElem})
elementary_divisors(::SMat{ZZRingElem})
Hecke.solve_dixon_sf(::SMat{ZZRingElem}, ::SRow{ZZRingElem})
Hecke.hadamard_bound2(::SMat)
Hecke.echelon_with_transform(::SMat{zzModRingElem})
Hecke.reduce_full(::SMat{ZZRingElem}, ::SRow{ZZRingElem})
hnf!(::SMat{ZZRingElem})
hnf(::SMat{ZZRingElem})
snf(::SMat{ZZRingElem})
hnf_extend!(::SMat{ZZRingElem}, ::SMat{ZZRingElem})
is_diagonal(::SMat)
det(::SMat{ZZRingElem})
det_mc(::SMat{ZZRingElem})
valence_mc(::SMat)
saturate(::SMat{ZZRingElem})
Hecke.hnf_kannan_bachem(::SMat{ZZRingElem})
diagonal_form(::SMat{ZZRingElem})
```
### Manipulation/ Access
```@docs; canonical=false
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
mod_sym!(::SMat{ZZRingElem}, ::ZZRingElem)
find_row_starting_with(::SMat, ::Int)
reduce(::SMat{ZZRingElem}, ::SRow{ZZRingElem}, ::ZZRingElem)
reduce(::SMat{ZZRingElem}, ::SRow{ZZRingElem})
reduce(::SMat{T}, ::SRow{T}) where {T <: FieldElement}
rand_row(::SMat{T}) where {T}
```

Changing of the ring:
```@docs; canonical=false
map_entries(f, ::SMat)
change_base_ring(::Ring, ::SMat)
```

### Arithmetic
Matrices support the usual operations as well

- `+`, `-`, `==`
- `div`, `divexact` by scalars
- multiplication by scalars

Various products:
```@docs; canonical=false
*(::SMat{T}, ::AbstractVector{T}) where {T}
*(::SMat{T}, ::AbstractMatrix{T})  where {T}
*(::SMat{T}, ::MatElem{T}) where {T}
*(::SRow{T}, ::SMat{T}) where {T}
```

```@docs; canonical=false
dot(::SRow{T}, ::SMat{T}, ::SRow{T}) where T
dot(::MatrixElem{T}, ::SMat{T}, ::MatrixElem{T}) where T
dot(::AbstractVector{T}, ::SMat{T}, ::AbstractVector{T}) where T
```

Other:
```@docs; canonical=false
sparse(::SMat)
ZZMatrix(::SMat{ZZRingElem})
ZZMatrix(::SMat{T}) where {T <: Integer}
Matrix(::SMat)
Array(::SMat)
```

