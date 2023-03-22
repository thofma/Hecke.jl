export AbstractLat
export AbstractSpace
export AbstractSpaceRes
export HermLat
export HermSpace
export QuadLat
export QuadSpace
export TorQuadModule
export TorQuadModuleElem
export TorQuadModuleMor
export VecSpaceRes
export ZLat

################################################################################
#
#  Abstract types
#
################################################################################

# abstract spaces

# TODO: add docs and jldotest
abstract type AbstractSpace{S} end

# abstract lattices

# TODO: add docs and jldotest
abstract type AbstractLat{S} end

################################################################################
#
#  DictWrapper
#
################################################################################

mutable struct DictWrapper{T}
  x::T
end

function Base.:(==)(x::DictWrapper{T}, y::DictWrapper{S}) where {S, T}
  return S === T && x.x == y.x
end

function Base.hash(x::DictWrapper, h::UInt)
  Base.hash(x.x, h)
end

###############################################################################
#
#  Quadratic spaces
#
###############################################################################

const QuadSpaceID = AbstractAlgebra.CacheDictType{Any, Any}()

# TODO: add docs and jldotest
@attributes mutable struct QuadSpace{S, T} <: AbstractSpace{S}
  K::S
  gram::T
  # Temporary variables for _inner_product
  # We need fast access, so no attribute things
  temp1 # Vector{elem_type(S)}
  temp2 # elem_type(S)

  function QuadSpace(K::S, G::T, cached::Bool) where {S, T}
    return AbstractAlgebra.get_cached!(QuadSpaceID, DictWrapper(G), cached) do
      z = new{S, T}(K, G)
      z.temp1 = zeros(K, nrows(G))
      z.temp2 = K()
      return z
    end::QuadSpace{S, T}
  end
end

################################################################################
#
#  Quadratic lattices
#
################################################################################

# TODO: add docs and jldotest
@attributes mutable struct ZLat <: AbstractLat{QQField}
  space::QuadSpace{QQField, QQMatrix}
  rational_span::QuadSpace{QQField, QQMatrix}
  basis_matrix::QQMatrix
  gram_matrix::QQMatrix
  aut_grp_gen::QQMatrix
  aut_grp_ord::ZZRingElem
  automorphism_group_generators::Vector{ZZMatrix} # With respect to the
                                                  # basis of the lattice
  automorphism_group_order::ZZRingElem
  minimum::QQFieldElem

  scale::QQFieldElem
  norm::QQFieldElem

  function ZLat(V::QuadSpace{QQField, QQMatrix}, B::QQMatrix)
    z = new()
    z.space = V
    z.basis_matrix = B
    return z
  end
end

# TODO: add docs and jldotest
@attributes mutable struct QuadLat{S, T, U} <: AbstractLat{S}
  space::QuadSpace{S, T}
  pmat::U
  gram::T                        # gram matrix of the matrix part of pmat
  rational_span::QuadSpace{S, T}
  base_algebra::S
  automorphism_group_generators::Vector{T}
  automorphism_group_order::ZZRingElem
  generators
  minimal_generators
  norm
  scale

  function QuadLat{S, T, U}() where {S, T, U}
    return new{S, T, U}()
  end

  function QuadLat(K::S, G::T, P::U) where {S, T, U}
    space = quadratic_space(K, G)
    z = new{S, T, U}(space, P)
    z.base_algebra = K
    return z
  end

  function QuadLat(K::S, G::T) where {S, T}
    n = nrows(G)
    M = pseudo_matrix(identity_matrix(K, n))
    return QuadLat(K, G, M)
  end
end

################################################################################
#
#  Hermitian spaces
#
################################################################################

const HermSpaceID = AbstractAlgebra.CacheDictType{Any, Any}()

# TODO: add docs and jldotest
@attributes mutable struct HermSpace{S, T, U, W} <: AbstractSpace{S}
  E::S
  K::T
  gram::U
  involution::W

  function HermSpace(E::S, K::T, gram::U, involution::W, cached::Bool) where {S, T, U, W}
    return AbstractAlgebra.get_cached!(HermSpaceID, DictWrapper(gram), cached) do
      new{S, T, U, W}(E, K, gram, involution)
    end::HermSpace{S, T, U, W}
  end
end

###############################################################################
#
#  Hermitian lattices
#
###############################################################################

# TODO: add docs and jldotest
@attributes mutable struct HermLat{S, T, U, V, W} <: AbstractLat{S}
  space::HermSpace{S, T, U, W}
  pmat::V
  gram::U
  rational_span::HermSpace{S, T, U, W}
  base_algebra::S
  involution::W
  automorphism_group_generators::Vector{U}
  automorphism_group_order::ZZRingElem
  generators
  minimal_generators
  norm
  scale

  function HermLat{S, T, U, V, W}() where {S, T, U, V, W}
    z = new{S, T, U, V, W}()
    return z
  end
end

###############################################################################
#
#  Torsion quadratic modules
#
###############################################################################

### Modules

@doc Markdown.doc"""
    TorQuadModule

# Example:
```jldoctest
julia> A = matrix(ZZ, [[2,0,0,-1],[0,2,0,-1],[0,0,2,-1],[-1,-1,-1,2]]);

julia> L = Zlattice(gram = A);

julia> T = Hecke.discriminant_group(L)
Finite quadratic module over Integer Ring with underlying abelian group
GrpAb: (Z/2)^2
Gram matrix of the quadratic form with values in Q/2Z
[   1   1//2]
[1//2      1]
```

We represent torsion quadratic modules as quotients of $\Z$-lattices
by a full rank sublattice.

We store them as a $\Z$-lattice `M` together with a projection `p : M -> A`
onto an abelian group `A`. The bilinear structure of `A` is induced via `p`,
that is `<a, b> = <p^-1(a), p^-1(a)>` with values in $\Q/n\Z$, where $n$
is the modulus and depends on the kernel of `p`.

Elements of A are basically just elements of the underlying abelian group.
To move between `M` and `A`, we use the `lift` function `lift : M -> A`
and coercion `A(m)`.

# Examples
```jldoctest
julia> R = rescale(root_lattice(:D,4),2);

julia> D = discriminant_group(R);

julia> A = abelian_group(D)
GrpAb: (Z/2)^2 x (Z/4)^2

julia> d = D[1]
[1, 0, 0, 0]

julia> d == D(A(d))
true

julia> lift(d)
4-element Vector{QQFieldElem}:
 1
 1
 3//2
 1
```

N.B. Since there are no elements of $\Z$-latties, we think of elements of `M` as
elements of the ambient vector space. Thus if `v::Vector` is such an element
then the coordinates with respec to the basis of `M` are given by
`solve_left(basis_matrix(M), v)`.
"""
@attributes mutable struct TorQuadModule
  ab_grp::GrpAbFinGen             # underlying abelian group
  cover::ZLat                     # ZLat -> ab_grp, x -> x * proj
  rels::ZLat
  proj::ZZMatrix                  # is a projection and respects the forms
  gens_lift::Vector{Vector{QQFieldElem}}
  gens_lift_mat::QQMatrix
  modulus::QQFieldElem
  modulus_qf::QQFieldElem
  value_module::QmodnZ
  value_module_qf::QmodnZ
  gram_matrix_bilinear::QQMatrix
  gram_matrix_quadratic::QQMatrix
  gens
  is_normal::Bool

  TorQuadModule() = new()
end

### Elements

# TODO: add docs and jldotest
mutable struct TorQuadModuleElem
  data::GrpAbFinGenElem
  parent::TorQuadModule

  TorQuadModuleElem(T::TorQuadModule, a::GrpAbFinGenElem) = new(a, T)
end

elem_type(::Type{TorQuadModule}) = TorQuadModuleElem

### Maps

# TODO: add docs and jldotest
mutable struct TorQuadModuleMor <: Map{TorQuadModule, TorQuadModule, HeckeMap, TorQuadModuleMor}
  header::MapHeader{TorQuadModule, TorQuadModule}
  map_ab::GrpAbFinGenMap

  function TorQuadModuleMor(T::TorQuadModule, S::TorQuadModule, m::GrpAbFinGenMap)
    z = new()
    z.header = MapHeader(T, S)
    z.map_ab = m
    return z
  end
end

###############################################################################
#
#  Map for restriction/extension of scalars
#
###############################################################################

# TODO: add docs and jldotest
mutable struct VecSpaceRes{S, T}
  field::S
  domain_dim::Int
  codomain_dim::Int
  absolute_basis::Vector{T}
  absolute_degree::Int
end

function VecSpaceRes(K::S, n::Int) where {S}
  B = absolute_basis(K)
  d = absolute_degree(K)
  domain_dim = n * d
  codomain_dim = n

  return VecSpaceRes{S, elem_type(K)}(K, domain_dim, codomain_dim, B, d)
end

@doc Markdown.doc"""
    AbstractSpaceRes

A container type for map of restriction of scalars from an abstract space `W` over a field `E`
to an abstract space `V` over a field `K`.

The underlying map `f` is actually considered as a map from `V` to `W`. The type stores the
domain `V` and the codomain `W`, as well as particular bases $B_V$ and $B_W$ for `V` and `W`
respectively - `f` is defined in such a way that $B_W$ corresponds to $B_V$ by restriction of
scalars, and conversely, $B_V$ corresponds to $B_W$ while extending scalars along `f`.

By default, the map makes correspond the standard bases of `V` and `W`.

Note that `E` must be a finite extensions of `K`. Currently, only the case $K = \mathbb{Q}$
and `E` a number field is available.
"""
mutable struct AbstractSpaceRes{S, T} <: Map{S, T, HeckeMap, AbstractSpaceRes}
  header::MapHeader{S, T}
  btop::MatrixElem        # A given basis for the top space
  ibtop::MatrixElem       # The inverse of the previous base matrix, to avoid computing it everytime
  bdown::MatrixElem       # A given basis the bottom space
  ibdown::MatrixElem      # Same as ibtop

  function AbstractSpaceRes(D::S, C::T, btop::MatrixElem, bdown::MatrixElem) where {S, T}
    z = new{S, T}()
    z.header = MapHeader{S, T}(D, C)
    z.btop = btop
    z.ibtop = inv(btop)
    z.bdown = bdown
    z.ibdown = inv(bdown)
    return z
  end
end

