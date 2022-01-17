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

const QuadSpaceID = AbstractAlgebra.CacheDictType{Any, Any}()

@attributes mutable struct QuadSpace{S, T} <: AbsSpace{S}
  K::S
  gram::T

  function QuadSpace(K::S, G::T) where {S, T}
    return new{S, T}(K, G)
  end

  function QuadSpace(K::S, G::T, cached::Bool) where {S, T}
    return AbstractAlgebra.get_cached!(QuadSpaceID, G, cached) do
      new{S, T}(K, G)
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
    return AbstractAlgebra.get_cached!(HermSpaceID, gram, cached) do
      new{S, T, U, W}(E, K, gram, involution)
    end::HermSpace{S, T, U, W}
  end
end
