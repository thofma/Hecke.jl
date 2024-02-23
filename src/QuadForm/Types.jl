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

    return new{S, elem_type(K)}(K, domain_dim, codomain_dim, B, d)
  end
end

### Between abstract spaces

@doc raw"""
    AbstractSpaceRes

A container type for map of change of scalars between vector spaces $V$ and $W$,
each equipped with a non-degenerate sesquilinear form, where $V$ is a $K$-vector
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
  ibtop::MatrixElem       # The inverse of the previous base matrix, to avoid computing it every time
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
Finite quadratic module
  over integer ring
Abelian group: (Z/2)^2
Bilinear value module: Q/Z
Quadratic value module: Q/2Z
Gram matrix quadratic form:
[   1   1//2]
[1//2      1]
```

We represent torsion quadratic modules as quotients of $\mathbb{Z}$-lattices
by a full rank sublattice.

We store them as a $\mathbb{Z}$-lattice `M` together with a projection `p : M -> A`
onto an abelian group `A`. The bilinear structure of `A` is induced via `p`,
that is `<a, b> = <p^-1(a), p^-1(a)>` with values in $\mathbb{Q}/n\mathbb{Z}$, where $n$
is the modulus and depends on the kernel of `p`.

Elements of A are basically just elements of the underlying abelian group.
To move between `M` and `A`, we use the `lift` function `lift : M -> A`
and coercion `A(m)`.

# Examples
```jldoctest
julia> R = rescale(root_lattice(:D,4),2);

julia> D = discriminant_group(R);

julia> A = abelian_group(D)
(Z/2)^2 x (Z/4)^2

julia> d = D[1]
Element
  of finite quadratic module: (Z/2)^2 x (Z/4)^2 -> Q/2Z
with components [1 0 0 0]

julia> d == D(A(d))
true

julia> lift(d)
4-element Vector{QQFieldElem}:
 1
 1
 3//2
 1
```

N.B. Since there are no elements of $\mathbb{Z}$-lattices, we think of elements of `M` as
elements of the ambient vector space. Thus if `v::Vector` is such an element
then the coordinates with respec to the basis of `M` are given by
`solve(basis_matrix(M), v; side = :left)`.
"""
@attributes mutable struct TorQuadModule
  ab_grp::FinGenAbGroup             # underlying abelian group
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
  data::FinGenAbGroupElem
  parent::TorQuadModule

  TorQuadModuleElem(T::TorQuadModule, a::FinGenAbGroupElem) = new(a, T)
end

### Maps

@doc raw"""
    TorQuadModuleMap

Type for abelian group homomorphisms between torsion quadratic modules. It
consists of a header which keeps track of the domain and the codomain of type
`TorQuadModule` as well as the underlying abelian group homomorphism.

# Examples
```jldoctest
julia> L = rescale(root_lattice(:A,3), 3)
Integer lattice of rank 3 and degree 3
with gram matrix
[ 6   -3    0]
[-3    6   -3]
[ 0   -3    6]

julia> T = discriminant_group(L)
Finite quadratic module
  over integer ring
Abelian group: (Z/3)^2 x Z/12
Bilinear value module: Q/Z
Quadratic value module: Q/2Z
Gram matrix quadratic form:
[2//3      0   1//3]
[   0      0   2//3]
[1//3   2//3   1//4]

julia> N, f = normal_form(T)
(Finite quadratic module: (Z/3)^2 x Z/12 -> Q/2Z, Map: finite quadratic module -> finite quadratic module)


julia> domain(f)
Finite quadratic module
  over integer ring
Abelian group: (Z/3)^2 x Z/12
Bilinear value module: Q/Z
Quadratic value module: Q/2Z
Gram matrix quadratic form:
[2//3      0   1//3]
[   0      0   2//3]
[1//3   2//3   1//4]

julia> codomain(f)
Finite quadratic module
  over integer ring
Abelian group: (Z/3)^2 x Z/12
Bilinear value module: Q/Z
Quadratic value module: Q/2Z
Gram matrix quadratic form:
[1//4      0      0      0]
[   0   4//3      0      0]
[   0      0   4//3      0]
[   0      0      0   4//3]

julia> abelian_group_homomorphism(f)
Map
  from (Z/3)^2 x Z/12
  to finitely generated abelian group with 4 generators and 4 relations
```

Note that an object of type `TorQuadModuleMap` needs not to be a morphism
of torsion quadratic modules, i.e. it does not have to preserve the
respective bilinear or quadratic forms of its domain and codomain. Though,
it must be a homomorphism between the underlying finite abelian groups.

# Examples
```jldoctest
julia> L = rescale(root_lattice(:A,3), 3);

julia> T = discriminant_group(L)
Finite quadratic module
  over integer ring
Abelian group: (Z/3)^2 x Z/12
Bilinear value module: Q/Z
Quadratic value module: Q/2Z
Gram matrix quadratic form:
[2//3      0   1//3]
[   0      0   2//3]
[1//3   2//3   1//4]

julia> T6 = rescale(T, 6)
Finite quadratic module
  over integer ring
Abelian group: (Z/3)^2 x Z/12
Bilinear value module: Q/6Z
Quadratic value module: Q/12Z
Gram matrix quadratic form:
[4   0      2]
[0   0      4]
[2   4   3//2]

julia> f = hom(T, T6, gens(T6))
Map
  from finite quadratic module: (Z/3)^2 x Z/12 -> Q/2Z
  to finite quadratic module: (Z/3)^2 x Z/12 -> Q/12Z

julia> T[1]*T[1] == f(T[1])*f(T[1])
false

julia> is_bijective(f)
true
```

Hecke provides several constructors for objects of type `TorQuadModuleMap`, see
for instance [`hom(::TorQuadModule, ::TorQuadModule, ::ZZMatrix)`](@ref),
[`hom(::TorQuadModule, ::TorQuadModule, ::Vector{TorQuadModuleElem})`](@ref),
[`identity_map(::TorQuadModule)`](@ref) or [`trivial_morphism(::TorQuadModule)`](@ref).
"""
mutable struct TorQuadModuleMap <: Map{TorQuadModule, TorQuadModule, HeckeMap, TorQuadModuleMap}
  header::MapHeader{TorQuadModule, TorQuadModule}
  map_ab::FinGenAbGroupHom

  function TorQuadModuleMap(T::TorQuadModule, S::TorQuadModule, m::FinGenAbGroupHom)
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

mutable struct VectorList{S, T}
  vectors::Vector{S} # list of (short) vectors
  lengths::Vector{Vector{T}} # lengths[i] contains the lengths of vectors[i] wrt to several forms
  lookup::Dict{S, Int} # v => i iff vectors[i] == v
  issorted::Bool # whether the vectors are sorted
  use_dict::Bool # whether lookup is used

  function VectorList{S, T}() where {S, T}
    return new{S, T}()
  end
end

# scalar product combinations
mutable struct SCPComb{S, V}
  scpcombs::VectorList{V, S} # list of vectors s with <w, e_i> = s_i for w a short vector
  trans::ZZMatrix # transformation matrix mapping the vector sums to a basis
  coef::ZZMatrix # "inverse" of trans: maps the basis to the vector sums
  F::Vector{ZZMatrix} # Gram matrices of the basis

  xvectmp::ZZMatrix # length(scpcombs.vectors) x dim
  xbasetmp::ZZMatrix # nrows(trans) x dim
  multmp1::ZZMatrix # nrows(trans) x dim
  multmp2::ZZMatrix # nrows(trans) x nrows(trans)
  multmp3::ZZMatrix # length(scpcombs.vectors) x dim

  SCPComb{S, V}() where {S, V} = new{S, V}()
end

# Bacher polynomials
# In theory, this is a polynomial, but for the application we only need the
# coefficients.
# `coeffs` is assumed to be of length n := `maximal_degree - minimal_degree + 1` and
# the corresponding polynomial is
#     coeffs[n] * X^maximal_degree + coeffs[n - 1] * X^(maximal_degree - 1)
#   + ... + coeffs[1] * X^minimal_degree \in ZZ[X]
mutable struct BacherPoly{T}
  coeffs::Vector{Int}
  minimal_degree::Int
  maximal_degree::Int
  sum_coeffs::Int # = sum(coeffs)
  S::T # the scalar product w.r.t. which the polynomial is constructed

  BacherPoly{T}() where {T} = new{T}()
end

mutable struct ZLatAutoCtx{S, T, V}
  G::Vector{T} # Gram matrices
  GZZ::Vector{ZZMatrix} # Gram matrices (of type ZZMatrix)
  Gtr::Vector{T} # transposed Gram matrices
  dim::Int
  max::S
  V::VectorList{V, S} # list of (short) vectors
  v::Vector{Vector{V}} # list of list of vectors (n x 1 matrices),
                       # v[i][j][k] is the dot product of V[j] with
                       # the k-th row of G[i]
                       # v[i][j] is the (matrix) product G[i]*V[j]
  per::Vector{Int} # permutation of the basis vectors such that in every step
                   # the number of possible continuations is minimal
  fp::Matrix{Int} # the "fingerprint": fp[1, i] = number vectors v such that v
                  # has same length as b_i for all forms
  fp_diagonal::Vector{Int} # diagonal of the fingerprint matrix
  std_basis::Vector{Int} # index of the the standard basis vectors in V.vectors

  # Vector sum stuff
  scpcomb::Vector{SCPComb{S, V}} # cache for the vector sum optimization
  depth::Int # depth of the vector sums (0 == no vector sums)

  # Bacher polynomial stuff
  bacher_polys::Vector{BacherPoly{S}}
  bacher_depth::Int # For how many base vectors the Bacher polynomial should be
                    # used. Between 0 (none at all) and `dim`

  orders::Vector{Int} # orbit length of b_i under <g[i], ..., g[end]>
  nsg::Vector{Int} # the first nsg[i] elements of g[i] lie in <g[1], ..., g[i-1]>
  g::Vector{Vector{T}} # generators for (subgroups of) the iterative stabilizers:
                       # <g[1], ..., g[i]> is the point-wise stabilizer of the
                       # basis vectors b_1, ..., b_{i - 1} in the full automorphism
                       # group
  prime::S

  is_symmetric::BitArray{1} # whether G[i] is symmetric
  operate_tmp::V # temp storage for orbit computation
  dot_product_tmp::V # temp storage for dot product computation

  function ZLatAutoCtx(G::Vector{ZZMatrix})
    z = new{ZZRingElem, ZZMatrix, ZZMatrix}()
    z.G = G
    z.Gtr = ZZMatrix[transpose(g) for g in G]
    z.dim = nrows(G[1])
    z.is_symmetric = falses(length(G))
    z.operate_tmp = zero_matrix(FlintZZ, 1, ncols(G[1]))
    z.dot_product_tmp = zero_matrix(FlintZZ, 1, 1)

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
  K::AbsSimpleNumField
  coeffs::Vector{ZZRingElem}
  dec_types

  function ZetaFunction(K::AbsSimpleNumField)
    z = new()
    z.K = K
    z.coeffs = ZZRingElem[]
    dec_types = []
    return z
  end
end

