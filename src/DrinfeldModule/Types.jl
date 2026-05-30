################################################################################
#
#  DrinfeldModule/Types.jl : Types for Ore polynomial rings and Drinfeld modules
#
################################################################################

################################################################################
#
#  OrePolyRing / OrePoly
#
#  Ore polynomial ring K{tau} with the commutation rule tau*a = a^q * tau
#  where q = order(F_q) for a fixed base finite field F_q.
#
################################################################################

# Non-commutative ring K{tau}
mutable struct OrePolyRing{T} <: NCRing
  base_ring::Ring
  q::ZZRingElem    # order of F_q; the twist map is a -> a^q
  var::Symbol

  function OrePolyRing{T}(K::Ring, q::ZZRingElem, var::Symbol) where {T}
    return new{T}(K, q, var)
  end
end

# Element of K{tau}: a_0 + a_1*tau + ... + a_d*tau^d
mutable struct OrePoly{T} <: NCRingElem
  parent::OrePolyRing{T}
  coeffs::Vector{T}  # coeffs[i+1] = coefficient of tau^i (1-indexed)

  function OrePoly{T}(R::OrePolyRing{T}, coeffs::Vector{T}) where {T}
    n = length(coeffs)
    while n > 0 && iszero(coeffs[n])
      n -= 1
    end
    return new{T}(R, coeffs[1:n])
  end

  function OrePoly{T}(R::OrePolyRing{T}) where {T}
    return new{T}(R, T[])
  end
end

################################################################################
#
#  DrinfeldModule
#
#  A Drinfeld module phi: A = F_q[T] -> K{tau} is determined by the image
#  phi_T of the generator T. The constant coefficient of phi_T is gamma(T),
#  the image of T under the base morphism gamma: A -> K.
#
################################################################################

@attributes mutable struct DrinfeldModule{T}
  function_ring::PolyRing         # A = F_q[T]
  ore_poly_ring::OrePolyRing{T}   # K{tau}
  gen::OrePoly{T}                 # phi_T in K{tau}

  function DrinfeldModule{T}(A::PolyRing, phi_T::OrePoly{T}) where {T}
    @req degree(phi_T) >= 1 "generator must have positive degree (rank >= 1)"
    R = parent(phi_T)
    return new{T}(A, R, phi_T)
  end
end

################################################################################
#
#  DrinfeldModuleMorphism
#
#  A morphism phi -> psi is an Ore polynomial f in K{tau} such that
#    f * phi_T = psi_T * f
#
################################################################################

mutable struct DrinfeldModuleMorphism{T}
  domain::DrinfeldModule{T}
  codomain::DrinfeldModule{T}
  ore_poly::OrePoly{T}

  function DrinfeldModuleMorphism{T}(phi::DrinfeldModule{T},
                                     psi::DrinfeldModule{T},
                                     f::OrePoly{T}) where {T}
    return new{T}(phi, psi, f)
  end
end
