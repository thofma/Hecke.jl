export AbstractLat
export AbstractSpace
export AbstractSpaceRes
export HermSpace
export QuadSpace
export VecSpaceRes

################################################################################
#
#  Abstract types
#
################################################################################

# abstract spaces
abstract type AbstractSpace{S} end

# abstract lattices
abstract type AbstractLat{S} end

################################################################################
#
#  Quadratic spaces
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

const QuadSpaceID = AbstractAlgebra.CacheDictType{Any, Any}()

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
#  Hermitian spaces
#
################################################################################

const HermSpaceID = AbstractAlgebra.CacheDictType{Any, Any}()

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
#  Map for restriction/extension of scalars
#
###############################################################################

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
A container type for map of restriction of scalars for an abstract space `W` over a field `E`
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

