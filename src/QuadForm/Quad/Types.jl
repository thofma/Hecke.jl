###############################################################################
#
#  Integer genera
#
###############################################################################

### Local

@doc raw"""
    ZZLocalGenus

Local genus symbol over a p-adic ring.

The genus symbol of a component `p^m A` for odd prime `= p` is of the
form `(m,n,d)`, where

- `m` = valuation of the component
- `n` = rank of A
- `d = det(A) \in \{1,u\}` for a normalized quadratic non-residue `u`.

The genus symbol of a component `2^m A` is of the form `(m, n, s, d, o)`,
where

- `m` = valuation of the component
- `n` = rank of `A`
- `d` = `det(A)` in `{1,3,5,7}`
- `s` = 0 (or 1) if even (or odd)
- `o` = oddity of `A` (= 0 if s = 0) in `Z/8Z`
      = the trace of the diagonalization of `A`

The genus symbol is a list of such symbols (ordered by `m`) for each
of the Jordan blocks `A_1,...,A_t`.

Reference: [CS99](@cite) Chapter 15, Section 7.


# Arguments
- `prime`: a prime number
- `symbol`: the list of invariants for Jordan blocks `A_t,...,A_t` given
  as a list of lists of integers
"""
mutable struct ZZLocalGenus
  _prime::ZZRingElem
  _symbol::Vector{Vector{Int}}

  function ZZLocalGenus(prime, symbol, check=true)
    if check
      if prime == 2
        @assert all(length(g)==5 for g in symbol)
        @assert all(s[3] in [1,3,5,7] for s in symbol)
      else
        @assert all(length(g)==3 for g in symbol)
      end
    end
    deleteat!(symbol, [i for (i,s) in enumerate(symbol) if s[2]==0])
    g = new()
    g._prime = prime
    g._symbol = symbol
    return g
  end
end

### Global

@doc raw"""
    ZZGenus

A collection of local genus symbols (at primes)
and a signature pair. Together they represent the genus of a
non-degenerate integer_lattice.
"""
@attributes mutable struct ZZGenus
  _signature_pair::Tuple{Int, Int}
  _symbols::Vector{ZZLocalGenus} # assumed to be sorted by their primes
  _representative::ZZLat

  function ZZGenus(signature_pair, symbols::Vector{ZZLocalGenus})
    G = new()
    G._signature_pair = signature_pair
    sort!(symbols, by = x->prime(x))
    deleteat!(symbols, [i for (i,s) in enumerate(symbols) if prime(s)!=2 && is_unimodular(s)])
    G._symbols = symbols
    return G
  end

  function ZZGenus(signature_pair, symbols, representative::ZZLat)
    G = ZZGenus(signature_pair, symbols)
    G._representative = representative
    return G
  end
end

###############################################################################
#
#  Isometry classes of quadratic spaces
#
###############################################################################

### Local

mutable struct LocalQuadSpaceCls{S, T, U}
  K::S    # the base field
  p::T    # a finite place
  hass_inv::Int
  det::U
  dim::Int
  dim_rad::Int
  witt_inv

  function LocalQuadSpaceCls{S, T, U}(K) where {S, T, U}
    z = new{typeof(K), ideal_type(order_type(K)), elem_type(K)}()
    z.dim = -1
    z.K = K
    return z
  end
end

### Global

mutable struct QuadSpaceCls{S, T, U, V}
  K::S  # the underlying field
  dim::Int
  dim_rad::Int
  det::U # of the non-degenerate part
  LGS::Dict{T, LocalQuadSpaceCls{S, T, U}}
  signature_tuples::Dict{V, Tuple{Int,Int,Int}}

  function QuadSpaceCls{S, T, U, V}(K) where {S, T, U, V}
    z = new{typeof(K), ideal_type(order_type(K)), elem_type(K), place_type(K)}()
    z.K = K
    z.dim = -1
    return z
  end
end

###############################################################################
#
#  Quadratic genera
#
###############################################################################

### Jordan decomposition

# This holds invariants of a local Jordan decomposition
#
# L = L_1 \perp ... \perp L_r
#
# In the non-dyadic case we store
# - ranks
# - scales
# - determinant (classes)
# of the L_i
#
# In the dyadic case we store
# - norm generators of L_i
# - (valuation of ) weights
# - determinant (classes)
# - Witt invariants

mutable struct JorDec{S, T, U}
  K::S
  p::T
  is_dyadic::Bool
  ranks::Vector{Int}
  scales::Vector{Int}

  # dyadic things
  normgens::Vector{U}
  weights::Vector{Int}
  dets::Vector{U}
  witt::Vector{Int}

  JorDec{S, T, U}() where {S, T, U} = new{S, T, U}()
end

### Local

# This holds invariants of a local Genus symbol
#
# L = L_1 \perp ... \perp L_r
#
# In the non-dyadic case we store
# - ranks
# - scales
# - determinant (classes)
# of the L_i = L^(s_i)
#
# In the dyadic case we store
# - norm generators of L^(s_i)
# - (valuation of ) weights of L^(s_i)
# - determinant (classes) of L^(s_i)
# - Witt invariants of L_i

mutable struct QuadLocalGenus{S, T, U}
  K::S
  p::T
  is_dyadic::Bool
  witt_inv::Int
  hass_inv::Int
  det::U
  rank::Int

  uniformizer::U

  ranks::Vector{Int}
  scales::Vector{Int}
  detclasses::Vector{Int}

  # dyadic things
  normgens::Vector{U}
  weights::Vector{Int}
  f::Vector{Int}
  dets::Vector{U}
  witt::Vector{Int}
  norms::Vector{Int}

  # Sometimes we know a jordan decomposition
  jordec::JorDec{S, T, U}

  function QuadLocalGenus{S, T, U}() where {S, T, U}
    z = new{S, T, U}()
    z.rank = 0
    z.witt_inv = 0
    z.hass_inv = 0
    return z
  end
end

### Global

mutable struct QuadGenus{S, T, U}
  K::S
  primes::Vector{T}
  LGS::Vector{QuadLocalGenus{S, T, U}}
  rank::Int
  signatures::Dict{InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}, Int}
  d::U
  space

  function QuadGenus{S, T, U}(K) where {S, T, U}
    z = new{typeof(K), ideal_type(order_type(K)), elem_type(K)}()
    z.rank = -1
    return z
  end
end

### Legacy

mutable struct LocalGenusSymbol{S}
  P
  data
  x
  iseven::Bool
  E
  is_ramified
  non_norm
end

################################################################################
#
#  Quadratic lattices
#
################################################################################

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

###############################################################################
#
#  Spinor genera
#
###############################################################################

# To keep track of ray class groups
mutable struct SpinorGeneraCtx
  mR::MapRayClassGrp # ray class group map
  mQ::FinGenAbGroupHom # quotient
  rayprimes::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}
  criticalprimes::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}

  function SpinorGeneraCtx()
    return new()
  end
end

###############################################################################
#
#  Local multiplicative group modulo squares map
#
###############################################################################

# Move this to a proper place
#
# TODO: Cache this in the dyadic case (on the lattice or the field)
mutable struct LocMultGrpModSquMap <: Map{FinGenAbGroup, FinGenAbGroup, HeckeMap, LocMultGrpModSquMap}
  domain::FinGenAbGroup
  codomain::AbsSimpleNumField
  is_dyadic::Bool
  p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
  e::AbsSimpleNumFieldElem
  pi::AbsSimpleNumFieldElem
  piinv::AbsSimpleNumFieldElem
  hext::NfToFinFldMor{FqField}
  h::AbsOrdQuoMap{AbsNumFieldOrder{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsSimpleNumFieldOrderElem}
  g::GrpAbFinGenToAbsOrdQuoRingMultMap{AbsNumFieldOrder{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsSimpleNumFieldOrderElem}
  i::FinGenAbGroupHom
  mS::FinGenAbGroupHom

  function LocMultGrpModSquMap(K::AbsSimpleNumField, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
    R = order(p)
    @assert nf(R) === K
    @assert is_absolute(K)
    z = new()
    z.codomain = K
    z.p = p
    z.is_dyadic = is_dyadic(p)

    if !is_dyadic(p)
      pi = elem_in_nf(uniformizer(p))
      k, h = residue_field(R, p)
      hext = extend(h, K)
      e = elem_in_nf(h\non_square(k))
      G = abelian_group([2, 2])

      z.domain = G
      z.e = e
      z.pi = pi
      z.hext = hext
      return z
    else
      pi = elem_in_nf(uniformizer(p))
      e = ramification_index(p)
      dim = valuation(norm(p), 2) * e + 2
      #V = vector_space(F, dim)
      I = p^(2*e + 1)
      Q, h = quo(R, I)
      U, g = unit_group(Q)
      M, i = quo(U, 2, false)
      SS, mSS = snf(M)
      @assert SS.snf == ZZRingElem[2 for i in 1:(dim - 1)]
      #@assert ngens(S) == dim - 1
      piinv = anti_uniformizer(p)
      G = abelian_group([2 for i in 1:dim])
      z.domain = G
      z.pi = pi
      z.piinv = piinv
      z.h = h
      z.g = g
      z.i = i
      z.mS = mSS
      return z
    end
  end
end

