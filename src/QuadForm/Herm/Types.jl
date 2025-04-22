###############################################################################
#
#  Hermitian genera
#
###############################################################################

### Local

# Need to make this type stable once we have settled on a design
mutable struct HermLocalGenus{S, T}
  E::S                                # Field
  p::T                                # prime of base_field(E)
  data::Vector{Tuple{Int, Int, Int}}  # data
  norm_val::Vector{Int}               # additional norm valuation
                                      # (for the dyadic case)
  is_dyadic::Bool                      # 2 in p
  is_ramified::Bool                    # p ramified in E
  is_split::Bool                       # p split in E
  non_norm_rep::FieldElem             # u in K*\N(E*)
  ni::Vector{Int}                     # ni for the ramified, dyadic case

  function HermLocalGenus{S, T}() where {S, T}
    z = new{S, T}()
    return z
  end
end

### Global

mutable struct HermGenus{S, T, U, V}
  E::S
  primes::Vector{T}
  LGS::Vector{U}
  rank::Int
  signatures::V

  function HermGenus(E::S, r, LGS::Vector{U}, signatures::V) where {S, U, V}
    K = base_field(E)
    primes = Vector{ideal_type(order_type(K))}(undef, length(LGS))

    for i in 1:length(LGS)
      primes[i] = prime(LGS[i])
      @assert r == rank(LGS[i])
    end
    z = new{S, eltype(primes), U, V}(E, primes, LGS, r, signatures)
    return z
  end
end

###############################################################################
#
#  Hermitian lattices
#
###############################################################################

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

