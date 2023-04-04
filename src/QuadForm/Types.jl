export AbstractLat
export AbstractSpace
export AbstractSpaceMor
export AbstractSpaceRes
export HermGenus
export HermLat
export HermLocalGenus
export HermSpace
export JorDec
export LatCloseEnumCtx
export LineEnumCtx
export LocMultGrpModSquMap
export LocalGenusSymbol
export LocalQuadSpaceCls
export QuadGenus
export QuadLat
export QuadLocalGenus
export QuadSpace
export QuadSpaceCls
export SCPComb
export SpinorGeneraCtx
export TorQuadModule
export TorQuadModuleElem
export TorQuadModuleMor
export VecSpaceRes
export VectorList
export ZGenus
export ZLat
export ZLatAutoCtx
export ZetaFunction
export ZpGenus

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

################################################################################
#
#  Integer lattices
#
################################################################################

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

################################################################################
#
#  Integer genera
#
################################################################################

@doc raw"""
    ZpGenus

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
mutable struct ZpGenus
  _prime::ZZRingElem
  _symbol::Vector{Vector{Int}}

  function ZpGenus(prime, symbol, check=true)
    if check
      if prime == 2
        @assert all(length(g)==5 for g in symbol)
        @assert all(s[3] in [1,3,5,7] for s in symbol)
      else
        @assert all(length(g)==3 for g in symbol)
      end
    end
    g = new()
    g._prime = prime
    g._symbol = symbol
    return g
  end
end

@doc raw"""
    ZGenus

A collection of local genus symbols (at primes)
and a signature pair. Together they represent the genus of a
non-degenerate Zlattice.
"""
@attributes mutable struct ZGenus
  _signature_pair::Tuple{Int, Int}
  _symbols::Vector{ZpGenus} # assumed to be sorted by their primes
  _representative::ZLat

  function ZGenus(signature_pair, symbols)
    G = new()
    G._signature_pair = signature_pair
    G._symbols = sort!(symbols, by = x->prime(x))
    return G
  end

  function ZGenus(signature_pair, symbols, representative::ZLat)
    G = new()
    G._signature_pair = signature_pair
    G._symbols = sort!(symbols, by = x->prime(x))
    G._representative = representative
    return G
  end
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

################################################################################
#
#  Quadratic genera
#
################################################################################

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

mutable struct QuadGenus{S, T, U}
  K::S
  primes::Vector{T}
  LGS::Vector{QuadLocalGenus{S, T, U}}
  rank::Int
  signatures::Dict{InfPlc{AnticNumberField, NumFieldEmbNfAbs}, Int}
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

###############################################################################
#
#  Hermitian genera
#
###############################################################################

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
#  Morphism between abstract spaces
#
###############################################################################

@attributes mutable struct AbstractSpaceMor{D, T} <: Map{D, D, HeckeMap, AbstractSpaceMor}
  header::MapHeader{D, D}
  matrix::T

  function AbstractSpaceMor(V::D, W::D, B::T) where {D, T}
    z = new{D, T}()
    z.header = MapHeader{D, D}(V, W)
    z.matrix = B
    return z
  end
end

###############################################################################
#
#  Map of change of scalars
#
###############################################################################

mutable struct VecSpaceRes{S, T}
  field::S
  domain_dim::Int
  codomain_dim::Int
  absolute_basis::Vector{T}
  absolute_degree::Int

  function VecSpaceRes(K::S, n::Int) where {S}
    B = absolute_basis(K)
    d = absolute_degree(K)
    domain_dim = n * d
    codomain_dim = n

    return VecSpaceRes{S, elem_type(K)}(K, domain_dim, codomain_dim, B, d)
  end
end


@doc raw"""
    AbstractSpaceRes

A container type for map of change of scalars between vector spaces $V$ and $W$,
each equiped with a non-degenerate sesquilinear form, where $V$ is a $K$-vector
space for some number field $K$ and $W$ is a $E$-vector space for some finite simple
extension `$E/K$.

Note: currently, only the case $K = \mathbb{Q}$ and $E$ a number field is available.

The underlying map `f` is actually considered as a map from $V$ to $W$. So in
particular, $f(v)$ for some $v \in V$ is used to extend the scalars from $K$ to
$E$, while the preimage $f\(w)$ for $w \in W$ is used to restrict scalars from
$E$ to $K$.

Let $(a_1, \ldots, a_n)\in E^n$ be a $K$-basis of $E$, $B_V = (v_1, \ldots, v_l)$ be a
$K$-basis of $V$ and $B_W = (w_1, \ldots, w_m)$ be an $E$-basis of $W$ where
$l = m\times n$.
Then, the map `f` defines a $K$-linear bijection from $V$ to $W$ by sending the
$K$-basis $(v_1, \ldots, v_l)$ of $V$ to the $K$-basis
$(a_1w_1, a_2w_1, \ldots, a_nw_1, a_1w_2, \ldots, a_nw_m)$ of $W$.

One can choose the different bases $B_V$ and $B_W$. However, for now, the basis of
$E$ over $K = \mathbb{Q}$ is fixed by [`absolute_basis`](@ref).

By default, $B_V$ is the standard $K$-basis of $V$ and $B_W$ is the standard $E$-basis
of $W$
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

###############################################################################
#
#  Torsion quadratic modules
#
###############################################################################

@doc raw"""
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

mutable struct TorQuadModuleElem
  data::GrpAbFinGenElem
  parent::TorQuadModule

  TorQuadModuleElem(T::TorQuadModule, a::GrpAbFinGenElem) = new(a, T)
end

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
#  Contexts and iterators
#
###############################################################################

# Iterate over the lines in K^n, that is, over the points of projective
# space P^(n-1)(K).
#
# Important: In the prime case, this must always be lexicographically ordered

mutable struct LineEnumCtx{T, S}
  K::T
  a::S # primitive element
  dim::Int
  depth::Int
  v::Vector{S}
  length::BigInt
end

# To keep track of ray class groups
mutable struct SpinorGeneraCtx
  mR::MapRayClassGrp # ray class group map
  mQ::GrpAbFinGenMap # quotient
  rayprimes::Vector{NfAbsOrdIdl{AnticNumberField, nf_elem}}
  criticalprimes::Vector{NfAbsOrdIdl{AnticNumberField, nf_elem}}

  function SpinorGeneraCtx()
    return new()
  end
end

mutable struct LatCloseEnumCtx{S, elem_type}
  short_vector_iterator::S
  e::QQFieldElem
  d::Int
end

###############################################################################

# This is (with permission) a port of the program ISOM and AUTO by Bernd
# Souvignier which implemented an algorithm published in
# W. PLESKEN, B. SOUVIGNIER, Computing Isometries of Lattices,
# Journal of Symbolic Computation, Volume 24, Issues 3-4, September 1997,
# Pages 327-334, ISSN 0747-7171, 10.1006/jsco.1996.0130.
# (https://www.sciencedirect.com/science/article/pii/S0747717196901303)

mutable struct SCPComb
  rank::Int
  trans::ZZMatrix
  coef::ZZMatrix
  F::Vector{ZZMatrix}

  SCPComb() = new()
end

mutable struct VectorList{S, T}
  vectors::Vector{S}
  lengths::Vector{Vector{T}}
  lookup::Dict{S, Int}
  issorted::Bool
  use_dict::Bool

  function VectorList{S, T}() where {S, T}
    return new{S, T}()
  end
end

mutable struct ZLatAutoCtx{S, T, V}
  G::Vector{T}
  Gtr::Vector{T}
  dim::Int
  max::S
  V::VectorList{V, S}
  v::Vector{T}
  per::Vector{Int}
  fp::Matrix{Int}
  fp_diagonal::Vector{Int}
  std_basis::Vector{Int}
  scpcomb::SCPComb

  orders::Vector{Int}
  ng::Vector{Int}
  nsg::Vector{Int}
  g::Vector{Vector{T}}
  prime::S

  is_symmetric::BitArray{1}
  operate_tmp::V

  function ZLatAutoCtx(G::Vector{ZZMatrix})
    z = new{ZZRingElem, ZZMatrix, ZZMatrix}()
    z.G = G
    z.Gtr = ZZMatrix[transpose(g) for g in G]
    z.dim = nrows(G[1])
    z.is_symmetric = falses(length(G))
    z.operate_tmp = zero_matrix(FlintZZ, 1, ncols(G[1]))

    for i in 1:length(z.G)
      z.is_symmetric[i] = is_symmetric(z.G[i])
    end

    return z
  end

  function ZLatAutoCtx{S, T, V}() where {S, T, V}
    return new{S, T, V}()
  end
end

###############################################################################
#
#  Miscalleneous
#
###############################################################################

# Move this to a proper place
#
# TODO: Cache this in the dyadic case (on the lattice or the field)
mutable struct LocMultGrpModSquMap <: Map{GrpAbFinGen, GrpAbFinGen, HeckeMap, LocMultGrpModSquMap}
  domain::GrpAbFinGen
  codomain::AnticNumberField
  is_dyadic::Bool
  p::NfAbsOrdIdl{AnticNumberField, nf_elem}
  e::nf_elem
  pi::nf_elem
  piinv::nf_elem
  hext::NfToFinFldMor{FqField}
  h::AbsOrdQuoMap{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}
  g::GrpAbFinGenToAbsOrdQuoRingMultMap{NfAbsOrd{AnticNumberField,nf_elem},NfAbsOrdIdl{AnticNumberField,nf_elem},NfAbsOrdElem{AnticNumberField,nf_elem}}
  i::GrpAbFinGenMap
  mS::GrpAbFinGenMap

  function LocMultGrpModSquMap(K::AnticNumberField, p::NfAbsOrdIdl{AnticNumberField, nf_elem})
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

mutable struct ZetaFunction
  K::AnticNumberField
  coeffs::Vector{ZZRingElem}
  dec_types

  function ZetaFunction(K::AnticNumberField)
    z = new()
    z.K = K
    z.coeffs = ZZRingElem[]
    dec_types = []
    return z
  end
end

