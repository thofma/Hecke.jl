export AbstractLat
export AbstractSpace
export AbstractSpaceMor
export AbstractSpaceRes
export TorQuadModule
export TorQuadModuleElem
export TorQuadModuleMor
export VecSpaceRes
export ZZLat

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

################################################################################
#
#  Quadratic spaces
#
################################################################################

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

### Between vector spaces

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

### Between abstract spaces

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
#  Integer lattices
#
###############################################################################

@attributes mutable struct ZZLat <: AbstractLat{QQField}
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

  function ZZLat(V::QuadSpace{QQField, QQMatrix}, B::QQMatrix)
    z = new()
    z.space = V
    z.basis_matrix = B
    return z
  end
end

###############################################################################
#
#  Torsion quadratic modules
#
###############################################################################

### Parent

@doc raw"""
    TorQuadModule

# Examples
```jldoctest
julia> A = matrix(ZZ, [[2,0,0,-1],[0,2,0,-1],[0,0,2,-1],[-1,-1,-1,2]]);

julia> L = integer_lattice(gram = A);

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
  cover::ZZLat                     # ZZLat -> ab_grp, x -> x * proj
  rels::ZZLat
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

### Element

mutable struct TorQuadModuleElem
  data::GrpAbFinGenElem
  parent::TorQuadModule

  TorQuadModuleElem(T::TorQuadModule, a::GrpAbFinGenElem) = new(a, T)
end

### Maps

@doc raw"""
    TorQuadModuleMor

Type for abelian group homomorphisms between torsion quadratic modules. It
consists of a header which keeps track of the domain and the codomain of type
`TorQuadModule` as well as the underlying abelian group homomorphism.

# Examples
```jldoctest
julia> L = rescale(root_lattice(:A,3), 3)
Quadratic lattice of rank 3 and degree 3 over the rationals

julia> T = discriminant_group(L)
Finite quadratic module over Integer Ring with underlying abelian group
GrpAb: (Z/3)^2 x Z/12
Gram matrix of the quadratic form with values in Q/2Z
[2//3      0   1//3]
[   0      0   2//3]
[1//3   2//3   1//4]

julia> N, f = normal_form(T)
(TorQuadModule: [1//4 0 0 0; 0 4//3 0 0; 0 0 4//3 0; 0 0 0 4//3], Map with following data
Domain:
=======
TorQuadModule [2//3 0 1//3; 0 0 2//3; 1//3 2//3 1//4]
Codomain:
=========
TorQuadModule [1//4 0 0 0; 0 4//3 0 0; 0 0 4//3 0; 0 0 0 4//3])


julia> domain(f)
Finite quadratic module over Integer Ring with underlying abelian group
GrpAb: (Z/3)^2 x Z/12
Gram matrix of the quadratic form with values in Q/2Z
[2//3      0   1//3]
[   0      0   2//3]
[1//3   2//3   1//4]

julia> codomain(f)
Finite quadratic module over Integer Ring with underlying abelian group
(General) abelian group with relation matrix
[4 0 0 0; 0 3 0 0; 0 0 3 0; 0 0 0 3]
with structure of GrpAb: (Z/3)^2 x Z/12

Gram matrix of the quadratic form with values in Q/2Z
[1//4      0      0      0]
[   0   4//3      0      0]
[   0      0   4//3      0]
[   0      0      0   4//3]

julia> abelian_group_homomorphism(f)
Map with following data
Domain:
=======
Abelian group with structure: (Z/3)^2 x Z/12
Codomain:
=========
(General) abelian group with relation matrix
[4 0 0 0; 0 3 0 0; 0 0 3 0; 0 0 0 3]
with structure of Abelian group with structure: (Z/3)^2 x Z/12
```

Note that an object of type `TorQuadModuleMor` needs not to be a morphism
of torsion quadratic modules, i.e. it does not have to preserve the
respective bilinear or quadratic forms of its domain and codomain. Though,
it must be a homomorphism between the underlying finite abelian groups.

# Examples
```jldoctest
julia> L = rescale(root_lattice(:A,3), 3);

julia> T = discriminant_group(L)
Finite quadratic module over Integer Ring with underlying abelian group
GrpAb: (Z/3)^2 x Z/12
Gram matrix of the quadratic form with values in Q/2Z
[2//3      0   1//3]
[   0      0   2//3]
[1//3   2//3   1//4]

julia> T6 = rescale(T, 6)
Finite quadratic module over Integer Ring with underlying abelian group
GrpAb: (Z/3)^2 x Z/12
Gram matrix of the quadratic form with values in Q/12Z
[4   0      2]
[0   0      4]
[2   4   3//2]

julia> f = hom(T, T6, gens(T6))
Map with following data
Domain:
=======
TorQuadModule [2//3 0 1//3; 0 0 2//3; 1//3 2//3 1//4]
Codomain:
=========
TorQuadModule [4 0 2; 0 0 4; 2 4 3//2]

julia> T[1]*T[1] == f(T[1])*f(T[1])
false

julia> is_bijective(f)
true
```

Hecke provides several constructors for objects of type `TorQuadModuleMor`, see
for instance [`hom(::TorQuadModule, ::TorQuadModule, ::ZZMatrix)`](@ref),
[`hom(::TorQuadModule, ::TorQuadModule, ::Vector{TorQuadModuleElem})`](@ref),
[`identity_map(::TorQuadModule)`](@ref) or [`trivial_morphism(::TorQuadModule)`](@ref).
"""
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
#  Lines iterators
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

###############################################################################
#
#  Close vectors
#
###############################################################################

mutable struct LatCloseEnumCtx{S, elem_type}
  short_vector_iterator::S
  e::QQFieldElem
  d::Int
end

###############################################################################
#
#  Plesken-Souvignier
#
###############################################################################

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
#  Zeta function
#
###############################################################################

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

