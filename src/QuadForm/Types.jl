################################################################################
#
#  Abstract types
#
################################################################################

# abstract spaces
abstract type AbsSpace{S} end

# abstract lattices
abstract type AbsLat{S} end

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

@attributes mutable struct QuadSpace{S, T} <: AbsSpace{S}
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

@attributes mutable struct HermSpace{S, T, U, W} <: AbsSpace{S}
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

