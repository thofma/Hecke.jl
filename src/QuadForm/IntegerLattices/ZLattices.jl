# scope & verbose scope: :Lattice
@doc raw"""
    basis_matrix(L::ZZLat) -> QQMatrix

Return the basis matrix $B$ of the integer lattice $L$.

The lattice is given by the row span of $B$ seen inside of the
ambient quadratic space of $L$.
"""
basis_matrix(L::ZZLat) = L.basis_matrix

ambient_space(L::ZZLat) = L.space

base_ring(L::ZZLat) = ZZ

base_ring_type(::Type{ZZLat}) = ZZRing

base_field(L::ZZLat) = base_ring(gram_matrix(ambient_space(L)))

################################################################################
#
#  Creation
#
################################################################################

@doc raw"""
    integer_lattice([B::MatElem]; gram) -> ZZLat

Return the Z-lattice with basis matrix $B$ inside the quadratic space with
Gram matrix `gram`.

If the keyword `gram` is not specified, the Gram matrix is the identity matrix.
If $B$ is not specified, the basis matrix is the identity matrix.

# Examples
```jldoctest
julia> L = integer_lattice(matrix(QQ, 2, 2, [1//2, 0, 0, 2]));

julia> gram_matrix(L) == matrix(QQ, 2, 2, [1//4, 0, 0, 4])
true

julia> L = integer_lattice(gram = matrix(ZZ, [2 -1; -1 2]));

julia> gram_matrix(L) == matrix(ZZ, [2 -1; -1 2])
true
```
"""
function integer_lattice(B::QQMatrix; gram = identity_matrix(QQ, ncols(B)), check::Bool=true, cached::Bool=true)
  V = quadratic_space(QQ, gram; check, cached)
  return lattice(V, B; check)
end

function integer_lattice(B::ZZMatrix; gram = identity_matrix(QQ, ncols(B)), check::Bool=true, cached::Bool=true)
  V = quadratic_space(QQ, gram; check, cached)
  return lattice(V, B; check)
end

### Documentation in ./Lattices.jl
quadratic_lattice(::QQField, B::Union{ZZMatrix, QQMatrix}; gram = identity_matrix(QQ, ncols(B)), check::Bool = true) = integer_lattice(B; gram, check)

function integer_lattice(;gram, check=true, cached=true)
  n = nrows(gram)
  return lattice(quadratic_space(QQ, gram; check, cached), identity_matrix(QQ, n); check)
end

### Documentation in ./Lattices.jl
quadratic_lattice(::QQField; gram, check::Bool = true, cached=true) = integer_lattice(; gram, check, cached)

### Documentation in ./Lattices.jl
function quadratic_lattice(::QQField, gens::Vector{T}; gram = nothing, check::Bool = true, cached=true) where T <: Union{QQMatrix, ZZMatrix, Vector{RationalUnion}}
  if length(gens) == 0
    @assert gram !== nothing
    B = zero_matrix(QQ, 0, nrows(gram))
    return quadratic_lattice(QQ, B; gram, check, cached)
  end
  @assert length(gens[1]) > 0
  if gram === nothing
    gram = identity_matrix(QQ, length(gens[1]))
  end
  if check
    @assert gram isa MatElem
    @req gram == transpose(gram) "Gram matrix must be symmetric"
    @req all(v -> length(v) == ncols(gram), gens) "Incompatible arguments: elements in gens must all have the same number of entries. This number must be equal to the size of the square matrix gram (if specified)"
  end
  gram = map_entries(QQ, gram)
  V = quadratic_space(QQ, gram; cached)
  B = zero_matrix(QQ, length(gens), length(gens[1]))
  for i in 1:length(gens)
    B[i:i,:] = gens[i]
  end
  return lattice(V, B; isbasis = false)
end

@doc raw"""
    lattice(V::QuadSpace{QQField, QQMatrix}, B::QQMatrix; isbasis=true, check=true) -> ZZLat

Return the $\mathbb Z$-lattice with basis matrix $B$ inside the quadratic space $V$.
"""
function lattice(V::QuadSpace{QQField, QQMatrix}, _B::MatElem{<:RationalUnion}; isbasis::Bool = true, check::Bool = true)
  @req dim(V) == ncols(_B) "Ambient space and the matrix B have incompatible dimension"
  if typeof(_B) !== QQMatrix
    B = map_entries(QQ, _B)
  else
    B = _B
  end

  # We need to produce a basis matrix

  if !isbasis
    BB = QQMatrix(_hnf_integral(FakeFmpqMat(B), :upper_right))
    i = nrows(BB)
    while i > 0 && is_zero_row(BB, i)
      i = i - 1
    end
    return ZZLat(V, BB[1:i, :])
  else
    @req !check || rank(B) == nrows(B) "The rows of B must define a free system of vectors in V"
    return ZZLat(V, B)
  end
end

function lattice_in_same_ambient_space(L::ZZLat, B::MatElem; check::Bool = true, isbasis::Bool=true)
  @req !check || (rank(B) == nrows(B)) "The rows of B must define a free system of vectors"
  V = ambient_space(L)
  return lattice(V, B; check = false, isbasis)
end

@doc raw"""
    rescale(L::ZZLat, r::RationalUnion) -> ZZLat

Return the lattice `L` in the quadratic space with form `r \Phi`.

#  Examples
This can be useful to apply methods intended for positive definite lattices.

```jldoctest
julia> L = integer_lattice(gram=ZZ[-1 0; 0 -1])
Integer lattice of rank 2 and degree 2
with gram matrix
[-1    0]
[ 0   -1]

julia> shortest_vectors(rescale(L, -1))
2-element Vector{Vector{ZZRingElem}}:
 [0, 1]
 [1, 0]
```
"""
function rescale(L::ZZLat, r::RationalUnion; cached::Bool=false)
  if isone(r)
    return L
  end
  B = basis_matrix(L)
  gram_space = gram_matrix(ambient_space(L))
  Vr = quadratic_space(QQ, r*gram_space; check=false, cached)
  R = lattice(Vr, B; isbasis=true, check = false)
  if isdefined(L,:gram_matrix)
    R.gram_matrix = r*L.gram_matrix
  end
  if isdefined(L,:scale)
    R.scale = abs(r)*L.scale
  end
  if isdefined(L,:norm)
    R.norm = abs(r)*L.norm
  end
  return R
end

################################################################################
#
#  Gram matrix
#
################################################################################

@doc raw"""
    gram_matrix(L::ZZLat) -> QQMatrix

Return the gram matrix of $L$.

# Examples
```jldoctest
julia> L = integer_lattice(matrix(ZZ, [2 0; -1 2]));

julia> gram_matrix(L)
[ 4   -2]
[-2    5]
```
"""
function gram_matrix(L::ZZLat)
  if isdefined(L, :gram_matrix)
    return L.gram_matrix
  end
  b = basis_matrix(L)
  V = ambient_space(L)
  if isone(b) && nrows(b) == dim(V)
    G = gram_matrix(V)
  else
    G = inner_product(V, b)
  end

  #G = b * gram_matrix(ambient_space(L)) * transpose(b)
  L.gram_matrix = G
  return G
end

gram_matrix_of_rational_span(L::ZZLat) = gram_matrix(L)

################################################################################
#
#  Rational span
#
################################################################################

@doc raw"""
    rational_span(L::ZZLat) -> QuadSpace

Return the rational span of $L$, which is the quadratic space with Gram matrix
equal to `gram_matrix(L)`.

# Examples
```jldoctest
julia> L = integer_lattice(matrix(ZZ, [2 0; -1 2]));

julia> rational_span(L)
Quadratic space of dimension 2
  over rational field
with gram matrix
[ 4   -2]
[-2    5]
```
"""
function rational_span(L::ZZLat)
  if isdefined(L, :rational_span)
    return L.rational_span
  else
    G = gram_matrix(L)
    V = quadratic_space(QQ, G; cached=false)
    L.rational_span = V
    return V
  end
end

################################################################################
#
#  Direct sums
#
################################################################################

function _biproduct(x::Vector{ZZLat})
  Bs = basis_matrix.(x)
  B = diagonal_matrix(Bs)
  return B
end

@doc raw"""
    direct_sum(x::Vararg{ZZLat}) -> ZZLat, Vector{AbstractSpaceMor}
    direct_sum(x::Vector{ZZLat}) -> ZZLat, Vector{AbstractSpaceMor}

Given a collection of $\mathbb Z$-lattices $L_1, \ldots, L_n$,
return their direct sum $L := L_1 \oplus \ldots \oplus L_n$ as modules,
together with the injections $L_i \to L$.
(seen as maps between the corresponding ambient spaces).

For modules, finite direct sums and finite direct products agree and
they are therefore called biproducts.
If one wants to obtain `L` as a direct product with the projections $L \to L_i$,
one should call `direct_product(x)`.
If one wants to obtain `L` as a biproduct with the injections $L_i \to L$ and
the projections $L \to L_i$, one should call `biproduct(x)`.

!!! warning
    The projections $L\to L_i$ are morphisms of modules but not of lattices,
    since the associated quadratic/hermitian forms are not preserved.
"""
function direct_sum(x::Vector{ZZLat}; cached::Bool=true)
  W, inj = direct_sum(ambient_space.(x); cached)
  B = _biproduct(x)
  return lattice(W, B; check = false), inj
end

direct_sum(x::Vararg{ZZLat}; cached=true) = direct_sum(collect(x); cached)

@doc raw"""
    direct_product(x::Vararg{ZZLat}) -> ZZLat, Vector{AbstractSpaceMor}
    direct_product(x::Vector{ZZLat}) -> ZZLat, Vector{AbstractSpaceMor}

Given a collection of $\mathbb Z$-lattices $L_1, \ldots, L_n$,
return their direct product $L := L_1 \times \ldots \times L_n$ as modules,
together with the projections $L \to L_i$.
(seen as maps between the corresponding ambient spaces).

For modules, finite direct sums and finite direct products agree and
they are therefore called biproducts.
If one wants to obtain `L` as a direct sum with the injections $L_i \to L$,
one should call `direct_sum(x)`.
If one wants to obtain `L` as a biproduct with the injections $L_i \to L$ and
the projections $L \to L_i$, one should call `biproduct(x)`.

!!! warning
    The projections $L\to L_i$ are morphisms of modules but not of lattices,
    since the associated quadratic/hermitian forms are not preserved.
"""
function direct_product(x::Vector{ZZLat}; cached::Bool=true)
  W, proj = direct_product(ambient_space.(x); cached)
  B = _biproduct(x)
  return lattice(W, B; check = false), proj
end

direct_product(x::Vararg{ZZLat}; cached::Bool=true) = direct_product(collect(x);cached)

@doc raw"""
    biproduct(x::Vararg{ZZLat}) -> ZZLat, Vector{AbstractSpaceMor}, Vector{AbstractSpaceMor}
    biproduct(x::Vector{ZZLat}) -> ZZLat, Vector{AbstractSpaceMor}, Vector{AbstractSpaceMor}

Given a collection of $\mathbb Z$-lattices $L_1, \ldots, L_n$,
return their biproduct $L := L_1 \oplus \ldots \oplus L_n$ as modules,
together with the injections $L_i \to L$ and the projections $L \to L_i$.
(seen as maps between the corresponding ambient spaces).

For modules, finite direct sums and finite direct products agree and
they are therefore called biproducts.
If one wants to obtain `L` as a direct sum with the injections $L_i \to L$,
one should call `direct_sum(x)`.
If one wants to obtain `L` as a direct product with the projections $L \to L_i$,
one should call `direct_product(x)`.

!!! warning
    The projections $L\to L_i$ are morphisms of modules but not of lattices,
    since the associated quadratic/hermitian forms are not preserved.
"""
function biproduct(x::Vector{ZZLat}; cached::Bool=true)
  W, inj, proj = biproduct(ambient_space.(x); cached)
  B = _biproduct(x)
  return lattice(W, B; check = false), inj, proj
end

biproduct(x::Vararg{ZZLat};cached::Bool=true) = biproduct(collect(x); cached)

@doc raw"""
    orthogonal_submodule(L::ZZLat, S::ZZLat) -> ZZLat

Return the largest submodule of ``L`` orthogonal to ``S``.
"""
function orthogonal_submodule(L::ZZLat, S::ZZLat)
  @assert ambient_space(L) === ambient_space(S) "L and S must have the same ambient space"
  return orthogonal_submodule(L, basis_matrix(S))
end

@doc raw"""
    orthogonal_submodule(L::ZZLat, S::QQMatrix) -> ZZLat

Return the largest submodule of ``L`` orthogonal to each row of ``S``.
"""
function orthogonal_submodule(L::ZZLat, C::QQMatrix)
  B = basis_matrix(L)
  V = ambient_space(L)
  G = gram_matrix(V)
  M = B * G * transpose(C)
  K = kernel(M, side = :left)
  K = change_base_ring(ZZ, K*denominator(K))
  Ks = saturate(K)
  return lattice(V, Ks*B; check = false)
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, ::MIME"text/plain", L::ZZLat)
  println(io, "Integer lattice of rank $(rank(L)) and degree $(degree(L))")
  println(io, "with gram matrix")
  show(io, MIME"text/plain"(), gram_matrix(L))
end

function show(io::IO, L::ZZLat)
  if is_terse(io)
    print(io, "Integer lattice")
  else
    print(io, "Integer lattice of rank $(rank(L)) and degree $(degree(L))")
  end
end

################################################################################
#
#  Is sublattice
#
################################################################################

function is_sublattice(M::ZZLat, N::ZZLat)
  if ambient_space(M) != ambient_space(N)
    return false
  end

  hassol, _rels = can_solve_with_solution(basis_matrix(M), basis_matrix(N); side=:left)

  if !hassol || !isone(denominator(_rels))
    return false
  end

  return true
end

@doc raw"""
    is_sublattice_with_relations(M::ZZLat, N::ZZLat) -> Bool, QQMatrix

Returns whether $N$ is a sublattice of $M$. In this case, the second return
value is a matrix $B$ such that $B B_M = B_N$, where $B_M$ and $B_N$ are the
basis matrices of $M$ and $N$ respectively.
"""
function is_sublattice_with_relations(M::ZZLat, N::ZZLat)
   if ambient_space(M) != ambient_space(N)
     return false, basis_matrix(M)
   end

   hassol, _rels = can_solve_with_solution(_solve_init(M), basis_matrix(N); side=:left)

   if !hassol || !isone(denominator(_rels))
     return false, basis_matrix(M)
   end

   return true, _rels
 end

################################################################################
#
#  Index
#
################################################################################

@doc raw"""
    index(L::ZZLat, M::ZZLat) -> IntExt

Return the index $[L:M]=|L/M|$ of $M$ in $L$.
"""
function index(L::ZZLat, M::ZZLat)
  b, M = is_sublattice_with_relations(L, M)
  b || error("M must be a sublattice of L to have a well defined index [L:M]")
  if rank(L)>rank(M)
    return inf
  end
  return ZZ(abs(det(M)))
end


################################################################################
#
#  Dual lattice
#
################################################################################

# documented in ../Lattices.jl

function dual(L::ZZLat)
  G = gram_matrix(L)
  new_bmat = inv(G)*basis_matrix(L)
  return lattice(ambient_space(L), new_bmat; check = false)
end

################################################################################
#
#  Scale
#
################################################################################

@doc raw"""
    scale(L::ZZLat) -> QQFieldElem

Return the scale of `L`.

The scale of `L` is defined as the positive generator of the $\mathbb Z$-ideal
generated by $\{\Phi(x, y) : x, y \in L\}$.
"""
function scale(L::ZZLat)
  if isdefined(L, :scale)
    return L.scale
  end
  G = gram_matrix(L)
  s = zero(QQFieldElem)
  for i in 1:nrows(G)
    for j in 1:i
      s = gcd(s, G[i, j])
    end
  end
  L.scale = s
  return s
end

################################################################################
#
#  Norm
#
################################################################################

@doc raw"""
    norm(L::ZZLat) -> QQFieldElem

Return the norm of `L`.

The norm of `L` is defined as the positive generator of the $\mathbb Z$- ideal
generated by $\{\Phi(x,x) : x \in L\}$.
"""
function norm(L::ZZLat)
  if isdefined(L, :norm)
    return L.norm
  end
  n = 2 * scale(L)
  G = gram_matrix(L)
  for i in 1:nrows(G)
    n = gcd(n, G[i, i])
  end
  L.norm = n
  return n
end

###############################################################################
#
#  Level
#
###############################################################################

@doc raw"""
    level(L::ZZLat) -> QQFieldElem

Return the level of $L$, that is, the inverse of the scale of the dual if $L$
is non-zero and $1$ otherwise.

# Examples
```jldoctest
julia> L = root_lattice(:D, 4);

julia> level(L)
2
```
"""
function level(L::ZZLat)
  if rank(L) == 0
    return QQ(1)
  end
  return 1//scale(dual(L))
end

###############################################################################
#
#  Parity
#
###############################################################################

@doc raw"""
    iseven(L::ZZLat) -> Bool

Return whether `L` is even.

An integer lattice `L` in the rational quadratic space $(V,\Phi)$ is called even
if $\Phi(x,x) \in 2\mathbb{Z}$ for all $x in L$.
"""
@attr Bool iseven(L::ZZLat) = is_integral(L) && iseven(numerator(norm(L)))

################################################################################
#
#  Discriminant
#
################################################################################

@doc raw"""
    discriminant(L::ZZLat) -> QQFieldElem

Return the discriminant of the rational span of `L`.
"""
discriminant(L::ZZLat) = discriminant(rational_span(L))

################################################################################
#
#  Determinant
#
################################################################################

@doc raw"""
    det(L::ZZLat) -> QQFieldElem

Return the determinant of the gram matrix of `L`.
"""
@attr QQFieldElem function det(L::ZZLat)
  return det(gram_matrix(L))
end

is_isotropic(L::ZZLat) = is_isotropic(rational_span(L))

################################################################################
#
#  Rank
#
################################################################################

function rank(L::ZZLat)
  return nrows(basis_matrix(L))
end

################################################################################
#
#  Signature
#
################################################################################

@doc raw"""
    signature_tuple(L::ZZLat) -> Tuple{Int,Int,Int}

Return the number of (positive, zero, negative) inertia of `L`.
"""
signature_tuple(L::ZZLat) = signature_tuple(rational_span(L))

################################################################################
#
#  Modularity
#
################################################################################

function is_modular(L::ZZLat, p::IntegerUnion)
  a = scale(L)
  v = valuation(a, p)
  if v * rank(L) == valuation(volume(L), p)
    return true, v
  else
    return false, 0
  end
end

################################################################################
#
#  Local basis matrix
#
################################################################################

# so that abstract lattice functions also work with Z-lattices

local_basis_matrix(L::ZZLat, p) = basis_matrix(L)

################################################################################
#
#  Intersection
#
################################################################################

function intersect(M::ZZLat, N::ZZLat)
  @req ambient_space(M) === ambient_space(N) "Lattices must have same ambient space"
  BM = basis_matrix(M)
  BN = basis_matrix(N)
  dM = denominator(BM)
  dN = denominator(BN)
  d = lcm(dM, dN)
  BMint = change_base_ring(ZZ, d * BM)
  BNint = change_base_ring(ZZ, d * BN)
  H = vcat(BMint, BNint)
  K = kernel(H, side = :left)
  BI = view(K,:, 1:nrows(BM)) * BM
  return lattice(ambient_space(M), BI; isbasis=true, check = false)
end

################################################################################
#
#  Sum
#
################################################################################

function +(M::ZZLat, N::ZZLat)
  @req ambient_space(M) === ambient_space(N) "Lattices must have same ambient space"
  BM = basis_matrix(M)
  if nrows(BM) == 0
    return N
  end
  BN = basis_matrix(N)
  if nrows(BN) == 0
    return M
  end
  B = QQMatrix(_hnf!_integral(FakeFmpqMat(vcat(BM, BN))))
  i = 1
  while is_zero_row(B, i)
    i += 1
  end
  return lattice(ambient_space(M), B[i:end, 1:ncols(B)]; check = false)
end

################################################################################
#
#  Local isometry
#
################################################################################

@doc raw"""
    is_locally_isometric(L::ZZLat, M::ZZLat, p::Int) -> Bool

Return whether `L` and `M` are isometric over the `p`-adic integers.

i.e. whether $L \otimes \mathbb{Z}_p \cong M\otimes \mathbb{Z}_p$.
"""
function is_locally_isometric(L::ZZLat, M::ZZLat, p::Int)
  return is_locally_isometric(L, M, ZZRingElem(p))
end

function is_locally_isometric(L::ZZLat, M::ZZLat, p::ZZRingElem)
  return genus(L, p) == genus(M, p)
end

################################################################################
#
#  Conversion between ZZLat and QuadLat
#
################################################################################

function _to_number_field_lattice(L::ZZLat, K, V)
  LL = lattice(V, change_base_ring(K, basis_matrix(L)))
  return LL
end

function _to_number_field_lattice(L::ZZLat;
                                  K::AbsSimpleNumField = rationals_as_number_field()[1],
                                  V::QuadSpace = quadratic_space(K, gram_matrix(ambient_space(L));cached=false))
  return _to_number_field_lattice(L, K, V)
end


function _to_ZLat(L::QuadLat, K, V)
  pm = pseudo_matrix(L)
  cm = coefficient_ideals(pm)
  pmm = matrix(pm)
  bm = zero_matrix(QQ, rank(L), dim(V))
  for i in 1:nrows(pm)
    a = norm(cm[i])
    for j in 1:ncols(pm)
      bm[i, j] = a * QQ(pmm[i, j])
    end
  end
  return lattice(V, bm; check = false)
end

function _to_ZLat(L::QuadLat;
                  K::QQField = QQ,
                  V::QuadSpace = quadratic_space(K, map_entries(QQ, gram_matrix(ambient_space(L)));cached=false))
  return _to_ZLat(L, K, V)
end

################################################################################
#
#  Mass
#
################################################################################

@doc raw"""
    mass(L::ZZLat) -> QQFieldElem

Return the mass of the genus of `L`.
"""
function mass(L::ZZLat)
  @req is_definite(L) "L must be a definite lattice"
  return mass(genus(L))
end

################################################################################
#
#  Genus representatives
#
################################################################################

@doc raw"""
    genus_representatives(L::ZZLat) -> Vector{ZZLat}

Return representatives for the isometry classes in the genus of `L`.
"""
function genus_representatives(_L::ZZLat)
  if rank(_L) <= 1
    return ZZLat[_L]
  end
  s = scale(_L)
  if s != 1
    L = rescale(_L, 1//s; cached=false)
  else
    L = _L
  end
  if rank(L) == 2
    LL = _to_number_field_lattice(L)
    G = genus_representatives(LL)
    res = ZZLat[]
    for N in G
      push!(res, _to_ZLat(N; K=QQ))
    end
  elseif is_definite(L)
    res = enumerate_definite_genus(L)
  else
    res = spinor_genera_in_genus(L)
  end
  s != 1 && map!(L -> rescale(L, s; cached=false), res, res)
  return res
end

@doc raw"""
    neighbours(L::ZZLat, p::IntegerUnion) -> Vector{ZZLat}

Return all $p$-neighbours of the definite lattice $L$, up to isometry.

# Examples
```jldoctest
julia> L = integer_lattice(gram = matrix(QQ, 3, 3, [2,1,-1,1,2,-1,-1,-1,8]));

julia> N1, N2 = neighbours(L, 3);

julia> N1
Integer lattice of rank 3 and degree 3
with gram matrix
[2   0   1]
[0   2   0]
[1   0   6]

julia> N2
Integer lattice of rank 3 and degree 3
with gram matrix
[2   1   1]
[1   2   1]
[1   1   8]
```
"""
function neighbours(
  L::ZZLat,
  p::Hecke.IntegerUnion,
)
  return _neighbours(L, ZZ(p); mode=:isometry_classes)
end

################################################################################
#
#  Maximal integral lattice
#
################################################################################

@doc raw"""
    even_sublattice(L::ZZLat) -> ZZLat

Given an integral $\mathbb{Z}$-lattice `L`, i.e. such that the bilinear form
on `L` is integral, return the largest even sublattice `L0` of `L`.

If `L` is already even, then $L0 = L$.

# Examples

```jldoctest
julia> L = integer_lattice(; gram=QQ[3 0; 0 16])
Integer lattice of rank 2 and degree 2
with gram matrix
[3    0]
[0   16]

julia> L0 = even_sublattice(L)
Integer lattice of rank 2 and degree 2
with gram matrix
[12    0]
[ 0   16]

julia> index(L, L0)
2
```
"""
function even_sublattice(L::ZZLat)
  @req is_integral(L) "The bilinear form on the lattice must be integral"
  is_even(L) && return L
  diagL = matrix(GF(2; cached=false), rank(L), 1, diagonal(gram_matrix(L)))
  K2 = kernel(diagL)
  K = matrix(QQ, [lift(ZZ, a) for a in K2])
  return lattice_in_same_ambient_space(L, K*basis_matrix(L)) + 2*L
end

# kept for testing
function _maximal_integral_lattice(L::ZZLat)
  LL = _to_number_field_lattice(L)
  M = maximal_integral_lattice(LL)
  return _to_ZLat(M; V = ambient_space(L))
end

@doc raw"""
    maximal_even_lattice(L::ZZLat, p::IntegerUnion) -> ZZLat

Given an integer lattice `L` with integral scale and a prime number `p` such that
$L_p$ is even, return an overlattice `M` of `L` which is maximal even at `p` and
which agrees locally with `L` at all other places.
"""
function maximal_even_lattice(L::ZZLat, p::IntegerUnion)
  while true
    ok, L = is_maximal_even(L, p; check=false)
    if ok
      return L
    end
  end
end

@attr Tuple{ZZMatrix, ZZRingElem} function gram_matrix_integral(L::ZZLat)
  G = gram_matrix(L)
  return _fmpq_mat_to_fmpz_mat_den(G)
end

@doc raw"""
    maximal_even_lattice(L::ZZLat) -> ZZLat

Given an even integer lattice `L`, return a maximal even overlattice `M` of `L`.
"""
function maximal_even_lattice(L::ZZLat)
  @req iseven(L) "The lattice must be even"
  for p in prime_divisors(ZZ(det(L)))
    L = maximal_even_lattice(L, p)
  end
  return L
end

function maximal_integral_lattice(L::ZZLat)
  @req denominator(norm(L)) == 1 "The norm of the lattice is not integral"
  L2 = rescale(L, 2; cached=false)
  LL2 = maximal_even_lattice(L2)
  V = ambient_space(L)
  return lattice(V, basis_matrix(LL2); check=false, isbasis=true)
end

function maximal_integral_lattice(L::ZZLat, p)
  @req denominator(norm(L)) == 1 "The norm of the lattice is not integral"
  if p==2
    L2 = rescale(L, 2; cached=false)
    L2 = maximal_even_lattice(L2, p)
    L2 = lattice_in_same_ambient_space(L, basis_matrix(L2))
  else
    L2 = maximal_even_lattice(L, p)
  end
  return L2
end


@doc raw"""
    is_maximal_even(L::ZZLat, p::IntegerUnion) -> Bool, ZZLat

Given an integer lattice `L` with integral scale and a prime number `p`,
return whether $L_p$ is even and has no proper overlattice satisfying this
property.

If $L_p$ is not even, the second output is `L` by default. Otherwise, either
`L` is maximal at `p` and the second output is `L`, or the second output is
an overlattice `M` of `L` such that $M_p$ is even and $[M:L] = p$.
"""
function is_maximal_even(L::ZZLat, p::IntegerUnion; check=true)
  @req !check || denominator(scale(L)) == 1 "The bilinear form is not integral"
  p != 2 || mod(ZZ(norm(L)), 2) == 0 || return false, L

  # o-maximal lattices are classified
  # see Kirschmer Lemma 3.5.3
  if valuation(det(L), p) <= 1
    return true, L
  end
  G, d = gram_matrix_integral(L)
  k = Native.GF(p)
  Gmodp = change_base_ring(k, G)
  V = kernel(Gmodp, side = :left)
  VZ = lift(V)
  H = divexact(VZ * G * transpose(VZ), p)
  if p != 2
    Hk = change_base_ring(k, H)
    ok, __v = _isisotropic_with_vector_finite(Hk)
    if !ok
      @assert nrows(V) == 2
      return true, L
    end
    _v = matrix(k, 1, length(__v), __v)
    v = lift(_v)
    sp = only(v * H * transpose(v))
    valv = iszero(sp) ? inf : valuation(sp, p)
    v = v * VZ
    sp = only(v * G * transpose(v))
    valv = iszero(sp) ? inf : valuation(sp, p)
    @assert valv >= 2
    v = QQ(1, p) * change_base_ring(QQ,v)
  else
    p = ZZ(p)
    R8 = residue_ring(ZZ, ZZ(8))[1]
    R4 = residue_ring(ZZ, ZZ(4))[1]
    findzero_mod4 = function(HR)
      z = R4(0)
      i = findfirst(==(z), R4.(diagonal(HR)))
      v = zero_matrix(ZZ, 1, nrows(HR))
      if !(i isa Nothing)
        v[1, i] = 1
        return true, v
      else
        return false, v
      end
    end
    n = min(4, nrows(H))
    HR8 = change_base_ring(R8, view(H,1:n,1:n))
    D = deepcopy(HR8)
    ok, v = findzero_mod4(HR8)
    B = identity_matrix(R8, n)
    if !ok
      D, B = _jordan_2_adic!(D, B, HR8)
      ok, v = findzero_mod4(D)
    end
    if !ok
      D, B = _normalize!(D, B, HR8, p)
      ok, v = findzero_mod4(D)
    end
    if !ok
      D, B = _two_adic_normal_forms!(D, B, HR8, p; partial = true)
      ok, v = _is_isotropic_with_vector_mod4(D)
      if !ok
        return true, L
      end
    end
    v = v * B
    v = map_entries(lift, v)
    v = v * @view VZ[1:n,:]
    v = QQ(1,2) * change_base_ring(QQ, v)
  end
  v = v * basis_matrix(L)
  B = vcat(basis_matrix(L), v)
  #B = _hnf!_integral(B)
  #B = B[2:rank(L)+1, :]
  LL = lattice(ambient_space(L), B; isbasis=false, check=false)
  @hassert :Lattice 1 det(L) ==  det(LL) * p^2 && valuation(norm(LL), p) >= 0
  @hassert :Lattice 1 denominator(scale(LL))==1
  @hassert :Lattice 1 p!=2 || mod(ZZ(norm(LL)),2)==0
  return false, LL
end

@doc raw"""
    _is_isotropic_with_vector_mod4(Gnormal) -> Bool, MatElem

Return if `Gnormal` is isotropic mod 4 and an isotropic vector.

Assumes that G is in partial 2-adic normal form.
"""
function _is_isotropic_with_vector_mod4(Gnormal)
  R4 = residue_ring(ZZ, 4)[1]
  G = change_base_ring(R4, Gnormal)
  D = diagonal(G)
  z = R4(0)
  v = zero_matrix(ZZ, 1, ncols(G))
  i = findfirst(==(z), D)
  if !(i isa Nothing)
    v[1, i] = 1
    return true, v
  end
  @assert nrows(G) <= 6 "$G"
  if nrows(G) == 1
    return false, v
  end
  # hardcoded isotropic vector for G in normal form (and no 0 mod 4 on the diag)
  if nrows(G) == 2
    if G[1,2] == 0 && D[1]+D[2] == 0
      v[1,1] = 1
      v[1,2] = 1
      return true, v
    else
      return false, v
    end
  end
  if nrows(G) == 3
    if D[3] in [R4(1), R4(3)]
      return false, v
    end
    @assert D[3] == R4(2)
    if sum(D[2:3]) == 0
      v[1,2] = 1; v[1,3] = 1
      return true, v
    end
    if G[1,2] == 0 && sum(D[1:2]) == 0
      v[1,1] = 1; v[1,2] = 1
      return true, v
    end
    if G[1,2] == 0 && sum(D) == 0
      v[1,1] = 1; v[1,2] = 1; v[1,3] = 1
      return true, v
    end
  end
  n = nrows(G)
  if D[1]+D[n] == 0
    v[1,1] = 1
    v[1,n] = 1
    return true, v
  end
  if D[n-1]+D[n] == 0
    v[1,n-1] = 1
    v[1,n] = 1
    return true, v
  end
  if D[1]+D[n-1] + D[n] == 0
    v[1,1] = 1
    v[1,n-1] = 1
    v[1,n] = 1
    return true, v
  end
  error("Something wrong!")
end

################################################################################
#
#  Scalar multiplication
#
################################################################################

@doc raw"""
    *(a::RationalUnion, L::ZZLat) -> ZZLat

Return the lattice $aM$ inside the ambient space of $M$.
"""
function Base.:(*)(a::RationalUnion, L::ZZLat)
  @assert has_ambient_space(L)
  if is_zero(a)
    B = zero_matrix(QQ, 0, degree(L))
  else
    B = a*basis_matrix(L)
  end
  return lattice_in_same_ambient_space(L, B; check = false)
end

function Base.:(*)(L::ZZLat, a::RationalUnion)
  return a * L
end

################################################################################
#
#  Canonical basis matrix
#
################################################################################

@attr FakeFmpqMat function _canonical_basis_matrix(L::ZZLat)
  return _hnf_integral(FakeFmpqMat(basis_matrix(L)))
end

################################################################################
#
#  Equality and hash
#
################################################################################

@doc raw"""
Return `true` if both lattices have the same ambient quadratic space
and the same underlying module.
"""
function Base.:(==)(L1::ZZLat, L2::ZZLat)
  V1 = ambient_space(L1)
  V2 = ambient_space(L2)
  if V1 != V2
    return false
  end
  return _canonical_basis_matrix(L1) == _canonical_basis_matrix(L2)
end

function Base.hash(L::ZZLat, u::UInt)
  V = ambient_space(L)
  B = _canonical_basis_matrix(L)
  # We compare lattices in the same ambient space, and since hnf for the basis
  # matrix is unique, one just needs to compare them.
  h = xor(hash(V), hash(B))
  return xor(h, u)
end

@doc raw"""
    local_modification(M::ZZLat, L::ZZLat, p)

Return a local modification of `M` that matches `L` at `p`.

INPUT:

- ``M`` -- a `\mathbb{Z}_p`-maximal lattice
- ``L`` -- the a lattice
            isomorphic to `M` over `\QQ_p`
- ``p`` -- a prime number

OUTPUT:

an integral lattice `M'` in the ambient space of `M` such that `M` and `M'` are locally equal at all
completions except at `p` where `M'` is locally isometric to the lattice `L`.
"""
function local_modification(M::ZZLat, L::ZZLat, p; check=true)
  # notation
  _d = denominator(inv(gram_matrix(L)))
  level = valuation(_d, p)
  d = p^(level+1) # +1 since scale(M) <= 1/2 ZZ

  check && @req is_isometric(L.space, M.space, p) "Quadratic spaces must be locally isometric at p"
  s = denominator(scale(L))
  L_max = rescale(L, s; cached=false)
  L_max = maximal_integral_lattice(L_max, p)
  L_max = lattice_in_same_ambient_space(L, basis_matrix(L_max);isbasis=true, check=false)
  # invert the gerstein operations
  GLm, U = padic_normal_form(gram_matrix(L_max), p; prec=level+3)
  R, _ = residue_ring(ZZ, d)
  UR = map_entries(x->(R(ZZ(x))), U)
  UI = map_entries(lift, inv(UR))
  B1 = mul!(inv(basis_matrix(L_max)), UI)

  GM, UM = padic_normal_form(gram_matrix(M), p; prec=level+3)
  # assert GLm == GM at least modulo p^prec
  @assert isone(denominator(B1))
  @assert isone(denominator(UM))
  n = ncols(GM)
  #B2 = B1 * UM * basis_matrix(M)
  #Lp = lattice(ambient_space(M), B2; check = false)

  # the local modification
  #SS = intersect(Lp + d * M, M)

  B = vcat(mul!(B1,UM),mul!(identity_matrix(QQ,n),d))
  B = _hnf!_integral!(B,:upperleft)
  # equvalent to the following but with less allocations
  #B = vcat(ZZ.(mul!(B1,UM)),mul!(identity_matrix(ZZ,n),d))
  #B = hnf!(B)

  V = ambient_space(M)
  S = lattice(V, view(B,1:n,1:n)*basis_matrix(M);isbasis=true, check=false)
  # confirm result
  #@assert S==SS
  @hassert :Lattice 2 genus(S, p) == genus(L, p)
  return S
end

################################################################################
#
#  Kernel lattice
#
################################################################################

@doc raw"""
    kernel_lattice(L::ZZLat, f::MatElem;
                   ambient_representation::Bool = true) -> ZZLat

Given a $\mathbf{Z}$-lattice $L$ and a matrix $f$ inducing an endomorphism of
$L$, return $\ker(f)$ is a sublattice of $L$.

If `ambient_representation` is `true` (the default), the endomorphism is
represented with respect to the ambient space of $L$. Otherwise, the
endomorphism is represented with respect to the basis of $L$.
"""
function kernel_lattice(L::ZZLat, f::MatElem; ambient_representation::Bool = true)
  bL = basis_matrix(L)
  if ambient_representation
    if !is_square(bL)
      fl, finL = can_solve_with_solution(bL, bL * f; side = :left)
      @req fl "f must preserve the lattice L"
    else
      finL = bL * f * inv(bL)
    end
  else
    finL = f
  end
  K = kernel(change_base_ring(ZZ, finL), side = :left)
  return lattice(ambient_space(L), K*basis_matrix(L); check = false)
end

################################################################################
#
#  Co/Invariant lattice
#
################################################################################

@doc raw"""
    invariant_lattice(L::ZZLat, G::Vector{MatElem};
                      ambient_representation::Bool = true) -> ZZLat
    invariant_lattice(L::ZZLat, G::MatElem;
                      ambient_representation::Bool = true) -> ZZLat

Given a $\mathbf{Z}$-lattice $L$ and a list of matrices $G$ inducing
endomorphisms of $L$ (or just one matrix $G$), return the lattice $L^G$,
consisting on elements fixed by $G$.

If `ambient_representation` is `true` (the default), the endomorphism is
represented with respect to the ambient space of $L$. Otherwise, the
endomorphism is represented with respect to the basis of $L$.
"""
function invariant_lattice(L::ZZLat, G::Vector{<:MatElem};
                           ambient_representation::Bool = true)
  if length(G) == 0
    return L
  end

  M = kernel_lattice(L, G[1] - 1; ambient_representation)
  for i in 2:length(G)
    N = kernel_lattice(L, G[i] - 1; ambient_representation)
    M = intersect(M, N)
  end
  return M
end

function invariant_lattice(L::ZZLat, G::MatElem;
                           ambient_representation::Bool = true)
  return kernel_lattice(L, G - 1; ambient_representation)
end

@doc raw"""
    coinvariant_lattice(L::ZZLat, G::Vector{MatElem};
                        ambient_representation::Bool = true) -> ZZLat
    coinvariant_lattice(L::ZZLat, G::MatElem;
                        ambient_representation::Bool = true) -> ZZLat

Given a $\mathbf{Z}$-lattice $L$ and a list of matrices $G$ inducing
endomorphisms of $L$ (or just one matrix $G$), return the orthogonal
complement $L_G$ in $L$ of the fixed lattice $L^G$
(see [`invariant_lattice`](@ref)).

If `ambient_representation` is `true` (the default), the endomorphism is
represented with respect to the ambient space of $L$. Otherwise, the
endomorphism is represented with respect to the basis of $L$.
"""
coinvariant_lattice(L::ZZLat, G::Union{MatElem, Vector{<:MatElem}}; ambient_representation::Bool = true) =
  orthogonal_submodule(L, invariant_lattice(L, G; ambient_representation))

################################################################################
#
#  Membership check
#
################################################################################

@doc raw"""
    Base.in(v::Vector, L::ZZLat) -> Bool

Return whether the vector `v` lies in the lattice `L`.
"""
function Base.in(v::Vector, L::ZZLat)
  @req length(v) == degree(L) "The vector should have the same length as the degree of the lattice."
  V = matrix(QQ, 1, length(v), v)
  return V in L
end

function coordinates(v::Union{QQMatrix,Vector{QQFieldElem}}, L::ZZLat)
  S = _solve_init(L)
  return solve(S, v; side=:left)
end

@attr AbstractAlgebra.Solve.SolveCtx{QQFieldElem, AbstractAlgebra.Solve.RREFTrait, QQMatrix, QQMatrix, QQMatrix} function _solve_init(L::ZZLat)
  return solve_init(basis_matrix(L))
end


@doc raw"""
    Base.in(v::QQMatrix, L::ZZLat) -> Bool

Return whether the row span of `v` lies in the lattice `L`.
"""
function Base.in(v::QQMatrix, L::ZZLat)
  @req ncols(v) == degree(L) "The vector should have the same length as the degree of the lattice."
  @req nrows(v) == 1 "Must be a row vector."
  fl, w = can_solve_with_solution(_solve_init(L), v; side=:left)
  return fl && isone(denominator(w))
end

@doc raw"""
    is_primitive(L::ZZLat, v::Union{Vector, QQMatrix}) -> Bool

Return whether the vector `v` is primitive in `L`.

A vector `v` in a $\mathbb Z$-lattice `L` is called primitive
if for all `w` in `L` such that $v = dw$ for some integer `d`,
then $d = \pm 1$.
"""
is_primitive(::ZZLat, ::Union{Vector, QQMatrix})

function is_primitive(L::ZZLat, v::Vector{<: RationalUnion})
  @req v in L "v is not contained in L"
  is_zero(v) && return true
  M = lattice_in_same_ambient_space(L, matrix(QQ,1,length(v), v); check = false)
  return is_primitive(L, M)
end

function is_primitive(L::ZZLat, v::QQMatrix)
  @req v in L "v is not contained in L"
  is_zero(v) && return true
  M = lattice_in_same_ambient_space(L, v; check = false)
  return is_primitive(L, M)
end

@doc raw"""
    divisibility(L::ZZLat, v::Union{Vector, QQMatrix}) -> QQFieldElem

Return the divisibility of `v` with respect to `L`.

For a vector `v` in the ambient quadratic space $(V, \Phi)$ of `L`,
we call the divisibility of `v` with the respect to `L` the
non-negative generator of the fractional $\mathbb Z$-ideal
$\Phi(v, L)$.
"""
divisibility(::ZZLat, ::Union{Vector, QQMatrix})

function divisibility(L::ZZLat, v::Vector{<: RationalUnion})
  @req length(v) == degree(L) "The vector should have the same length as the degree of the lattice"
  imv = matrix(QQ, 1, length(v), v)*gram_matrix(ambient_space(L))*transpose(basis_matrix(L))
  I = fractional_ideal(ZZ, vec(collect(imv)))
  return gen(I)
end

function divisibility(L::ZZLat, v::QQMatrix)
  @req ncols(v) == degree(L) "The vector should have the same length as the degree of the lattice"
  @req nrows(v) == 1 "v must be a row vector"
  imv = v*gram_matrix(ambient_space(L))*transpose(basis_matrix(L))
  I = fractional_ideal(ZZ, vec(collect(imv)))
  return gen(I)
end



################################################################################
#
#  LLL-reduction
#
################################################################################

function _lll(
  M::ZZMatrix,
  def::Bool,
  ctx::LLLContext = LLLContext(0.99, 0.51, :gram),
)
  if def
    neg = M[1,1] < 0
    if neg
      G2, U = lll_gram_with_transform(-M, ctx)
      G2 = -G2
    else
      G2, U = lll_gram_with_transform(M, ctx)
    end
  elseif (nrows(M) == 3) && (abs(det(M)) == 1)
    G2, U = lll_gram_indef_ternary_hyperbolic(M)
  elseif det(M) == 1
    G2, U = lll_gram_indef_with_transform(M)
  else
    # In the modular case, one may perform another LLL-reduction to obtain
    # a better output
    G21, U21 = lll_gram_indef_with_transform(M)
    G2, U2 = lll_gram_indef_with_transform(G21)
    U = U2*U21
  end
  return G2, U
end

@doc raw"""
    lll(
      L::ZZLat;
      same_ambient::Bool=true,
      redo::Bool=false,
      ctx::LLLContext=LLLContext(0.99, 0.51, :gram),
    ) -> ZZLat

Given an integral $\mathbb Z$-lattice `L` with fixed basis matrix `B`,
compute a basis `C` of `L` such that the gram matrix $G_C$ of `L` with
respect to `C` is LLL-reduced.

By default, it creates the lattice in the same ambient space as `L`. This
can be disabled by setting `same_ambient = false`.

After computation, the new lattice in output remembers that it has a fixed
lll-reduced basis. If one wants to perform the computations again, one should
set `redo` to `true`.

The function works with both definite and indefinite lattices. In the definite
case, one can also speficy the reduction parameters by creating the
appropriate `LLLContext` (see also `lll_gram`).
"""
function lll(
  L::ZZLat;
  same_ambient::Bool=true,
  redo::Bool=false,
  ctx::LLLContext=LLLContext(0.99, 0.51, :gram),
  _is_definite::Bool=is_definite(L)
)
  if !redo && get_attribute(L, :is_lll_reduced, false)
    return L
  end
  rank(L) == 0 && return L
  def = _is_definite
  M, d = _integral_split_gram(L)
  G2, U = _lll(M, def, ctx)
  if same_ambient
    B2 = U*basis_matrix(L)
    Llll = lattice(ambient_space(L), B2; check=false)
  else
    Llll = integer_lattice(; gram=(1//d)*change_base_ring(QQ, G2))
  end
  set_attribute!(Llll, :is_lll_reduced, true)
  return Llll
end

@attr Tuple{ZZMatrix, ZZRingElem} function _integral_split_gram(L::ZZLat)
  return integral_split(gram_matrix(L), ZZ)
end

###############################################################################
#
#  Decomposition of definite lattices
#
###############################################################################

### Irreducible components: splitting in orthogonal direct sums of irreducibles

# Looks like LLL is too powerful: it is hard to get a nontrivial example
# covering all the parts of the code...
@doc raw"""
    irreducible_components(L::ZZLat) -> Vector{ZZLat}

Return the irreducible components ``L_i`` of the definite lattice ``L``.

This yields a maximal orthogonal splitting of `L` as
```math
L = \bigoplus_i L_i.
```
The decomposition is unique up to ordering of the factors.

# Examples
```jldoctest
julia> R = integer_lattice(; gram=2 * identity_matrix(ZZ, 24));

julia> N = maximal_even_lattice(R); # Niemeier lattice

julia> irr_comp = irreducible_components(N)
3-element Vector{ZZLat}:
 Integer lattice of rank 8 and degree 24
 Integer lattice of rank 8 and degree 24
 Integer lattice of rank 8 and degree 24

julia> genus.(irr_comp)
3-element Vector{ZZGenus}:
 Genus symbol: II_(8, 0)
 Genus symbol: II_(8, 0)
 Genus symbol: II_(8, 0)
```
"""
function irreducible_components(L::ZZLat; check::Bool=true)
  @req !check || is_definite(L) "Lattice must be definite"
  # Take care of the trivial cases
  rank(L) == 0 && return ZZLat[]
  rank(L) == 1 && return ZZLat[L]

  s = scale(L)
  # The code assumes positive definite integral lattices
  d = denominator(s)
  if isone(d)
    G = map_entries(ZZ, gram_matrix(L))
  else
    G = map_entries(a -> numerator(d*a), gram_matrix(L))
  end
  if G[1, 1] < 0
    map_entries!(-, G, G)
  end
  # We do a first LLL-reduction to get a first orthogonal decomposition
  _, U = lll_gram_with_transform(G)

  irr = _irreducible_components(G, U)
  V = ambient_space(L)
  return ZZLat[lattice(V, M*basis_matrix(L); isbasis=false, check=false) for M in irr]
end

@doc raw"""
    _is_decomposable(v::ZZMatrix, G::ZZMatrix, m::ZZRingElem, e::Int)
                                            -> Bool, ZZMatrix

Return whether the vector ``v`` given in the coordinates of an integral
positive definite lattice with Gram matrix ``G`` is decomposable.

A nonzero vector ``v`` of a definite lattice ``L`` is called decomposable
if there exist two nonzero vectors ``w1, w2`` which are orthogonal to each
other and such that ``v = w1 + w2``.

In order to determine whether ``v`` is decomposable, we therefore try to
find nontrivial solutions ``w`` (i.e. neither ``0`` nor ``v``) to the
equation ``v.w = w^2``.

The naive approach, currently, is to solve this by iteratively testing whether
any short vector ``w`` of a certain square, ranging from ``m`` to ``v^2``,
satisfies the above equation. In which case, one can write ``v = w + (v-w)``.

The value ``m`` is the minimum norm of a vector in ``L`` and ``e`` is 1 if the
lattice ``L`` is odd, and 2 otherwise.
"""
function _is_decomposable(v::ZZMatrix, G::ZZMatrix, m::ZZRingElem, e::Int)
  a = first(v*G*transpose(v))
  # Since m is the minimum, any vector of norm less than 2*m is indecomposable
  a < 2*m && return false, v

  for b in m:e:ceil(Int, a//2)
    xs = short_vectors_affine(G, v, b, b)
    filter!(!isequal(v), xs)
    isempty(xs) && continue
    return true, first(xs)
  end
  return false, v
end

@doc raw"""
    _irreducible_components(G::ZZMatrix, U::ZZMatrix) -> Vector{ZZMatrix}

Input: Gram matrix ``G`` of an integral positive definite lattice ``L``
       in its standard basis and an LLL-reduced basis ``U``.

Ouput: Basis matrices for the irreducible components of ``L``

We proceed as follows:
- We split ``U`` into its connected components.
- For each connected component ``B`` of ``U``:
  - we compute an LLL-reduction ``UB`` of ``B``, and we let ``_G``
    be the associated Gram matrix.
  - we determine the minimum norm ``m`` of a vector for ``_G`` and we determine
    a set system ``V`` of shortest vectors for ``_G`` which span the sublattice
    of ``UB`` generated by shortest vectors.
  - we iterate on the vectors ``v`` in ``UB`` in the following way:
    - if ``v`` is indecomposable, and not in the `ZZ`-span of ``V``, we add
      ``v`` to ``V``. If the spans of ``V`` and ``UB`` coincide, then we
      stop here.
    - if ``v = w1+w2`` is decomposable, then we add ``w1`` and ``w2`` to a
      temporary list ``tmp``.
    - we iterate the procedure on each vector of ``tmp`` until it is empty,
      or if the span of ``V`` and ``UB`` coincide.
  - eventually ``V`` will consist of a generating system for the span of ``UB``,
    made of indecomposable vectors: we return the connected components of ``V``.

Note that mathematically, since we can decompose all vectors in a basis of ``L``
into a sum of indecomposable vectors, and each such indecomposable vector lies
in a unique irreducible component of ``L``, there exists a generating set made
of indecomposable vectors, and the connected components of any such generating
set span the respective irreducible components of ``L``.

Hence, the algorithm eventually terminates by returning a generating set made
of indecomposable vectors, for each of the irreducible components of ``L``.

!!!
Warning: the approach is naive. It could be certainly improved, for instance
in the decomposability check for vectors, or for finding a generating set made
of indecomposable vectors.
!!!
"""
function _irreducible_components(G::ZZMatrix, U::ZZMatrix)
  components = ZZMatrix[]
  irr = _connected_components_graph(U, G)
  for B in irr
    _G = B*G*transpose(B)
    __G, _U = lll_gram_with_transform(_G)
    _UB = _U*B
    _compB = __irreducible_components(__G)
    for _B in _compB
      push!(components, _B*_UB)
    end
  end
  return components
end


# Subprocedure for _irreducible_components; see the documentation above
# for more details
function __irreducible_components(G)
  # A way to get indecomposable vectors for free, is to look for
  # vectors of minimal norm
  flag, m, B, H = _shortest_vectors_sublattice_gram_integral(G)
  if flag
    return _connected_components_graph!(B, G)
  end
  e = all(iseven, diagonal(G)) ? Int(2) : Int(1)
  n = nrows(G)
  v = zero_matrix(ZZ, 1, n)
  _w = zero(v)
  for j in 1:n
    # We iterate over the basis vectors: some of them could already
    # be in the span of B
    zero!(v)
    v[1, j] = ZZ(1)
    ok, w = _is_decomposable(v, G, m, e)
    if !ok
      # v is indecomposable: we test now if it is in the
      # ZZ-span of B
      zero!(_w)
      add!(_w, _w, w)
      reduce_mod_hnf_ur!(_w, H)
      iszero(_w) && continue
      # We add our vector in B
      push!(B, deepcopy(w))
      H[(n+1):(n+1), :] = _w
      hnf!(H)
      if all(isone(H[i, i]) for i in 1:n) # We have a basis
        return _connected_components_graph!(B, G)
      end
      continue
    end
    # v is decomposable, as w+(v-w): we iteratively decompose them as a sum of
    # indecomposables
    tmp = ZZMatrix[w, v-w]
    while !isempty(tmp)
      w = popfirst!(tmp)
      # We redo all the same as before
      zero!(_w)
      add!(_w, _w, w)
      reduce_mod_hnf_ur!(_w, H)
      iszero(_w) && continue

      ok2, w2 = _is_decomposable(w, G, m, e)
      if !ok
        push!(B, deepcopy(w))
        H[(n+1):(n+1), :] = _w
        hnf!(H)
        if all(isone(H[i, i]) for i in 1:n) # We have a basis
          return _connected_components_graph!(B, G)
        end
        continue
      end
      push!(tmp, w2)
      push!(tmp, w-w2)
    end
  end

  # From here, B should be a generating system made of indecomposable vectors
  return _connected_components_graph!(B, G)
end

@doc raw"""
    _connected_components_graph!(B::Vector{T}, G::T) -> Vector{T}

Return the connected components of system of vectors ``B`` wrt. to ``G``.

We call connected components of ``B`` wrt. to ``G`` the matrices whose rows
are vectors from ``B`` which belong to the same connected component of the
graph obtained as follows:
- each node is a vector in ``B``
- two nodes are connected if their product wrt. to ``G`` is nonzero.
``G`` is assumed to be bilinear, and no assumption are made on ``B``.

!!!
Warning: the list ``B`` in input will be empty after calling this function.
The content of ``B`` is still in the output list, but gathered as rows
of matrices representing each connected component of the graph
!!!
"""
function _connected_components_graph!(B::Vector{T}, G::T) where T <: MatElem
  components = T[]
  if isempty(B)
    return components
  end
  c = B[1]
  tmp = zero(transpose(c))
  tmp2 = zero(transpose(c))
  tmp3 = zero_matrix(base_ring(c), 1, 1)::T
  D = Int[]
  while length(B) > 0
    basis = T[]
    b = pop!(B)
    push!(basis, b)
    flag = true
    for c in basis
      _c = transpose!(tmp, c)
      Gc = mul!(tmp2, G, _c)
      for (i,a) in enumerate(B)
        if !iszero(mul!(tmp3, a, Gc))
          push!(basis, a)
          push!(D,i)
        end
      end
      deleteat!(B, D)
      empty!(D)
    end
    push!(components, reduce(vcat, basis))
  end
  #@hassert :Lattice 0 sum(rank(i) for i in components; init=0) == nrows(G)
  sort!(components; by=rank)
  return components
end




function _connected_components_graph(B::T, G::T) where T <: MatElem
  return _connected_components_graph!(T[B[i:i, :] for i in 1:nrows(B)], G)
end

################################################################################
#
#  Shortest vectors lattices
#
################################################################################

@doc raw"""
    _shortest_vectors_sublattice_gram_integral(G::ZZMatrix)
                                           -> Bool, ZZRingElem, Vector{ZZMatrix}, ZZMatrix

Given a Gram matrix ``G`` for a positive definite integral lattice ``L``, return
the minimum ``m`` of a vector in ``L``, a system ``B`` of shortest vectors which
span the shortest vectors sublattice of ``L``, and the Hermite normal form ``H``
of such a system. The first output is a boolean which tells whether ``B`` generates
the lattice ``L``.

!!!
Warning: the outputs are independent of a choice of a basis for ``L``, except for
``B`` whose content depends on ``G``. So any other choice of a basis of ``L`` will
change ``G``, and in turns will change ``B``.
!!!
"""
function _shortest_vectors_sublattice_gram_integral(G::ZZMatrix)
  m = minimum(diagonal(G))
  # We create an iterator to avoid creating very large lists for
  # lattices with big kissing number
  V = _short_vectors_gram_nolll_integral(Hecke.LatEnumCtx, G, 0, m, nothing, one(ZZ), ZZRingElem)
  B = ZZMatrix[]
  n = ncols(G)
  H = zero_matrix(ZZ, n+1, n) # One row more for hnf
  w = zero_matrix(ZZ, 1, n)
  flag = false
  for (_v, l) in V
    if l > m
      # m is our current minimum: if l is larger than that,
      # then we do not have a shortest vector so we continue
      continue
    elseif l < m
      # In that case, m was not the minimum so we have to start a new
      # system of vectors from scratch
      empty!(B)
      zero!(H)
      k = Int(0)
      m = ZZ(l)
    end
    w[1:1, :] = _v
    # test whether _v is in the span of B
    reduce_mod_hnf_ur!(w, H)
    iszero(w) && continue
    push!(B, matrix(ZZ, 1, n, _v))
    # We add w in the last row, and we do an hnf
    # H will always have rank at most n
    H[(n+1):(n+1), :] = w
    hnf!(H)
    if all(isone(H[i, i]) for i in 1:n) # We have a basis
      flag = true
      break
    end
  end
  return flag, m, B, H
end

function _row_span!(L::Vector)
  l = length(L)
  d = length(L[1])
  m = min(d,l)
  B = zero_matrix(ZZ, m, d)
  for i in 1:m
    v = L[i]
    for j in 1:d
      B[i,j] = v[j]
    end
  end
  #B = reduce(vcat, L[1:m])
  h = hnf!(B)
  b = zero_matrix(ZZ, 1, d)
  for i in (m+1):l
    _copy_to_row_matrix!(b, L[i])
    reduce_mod_hnf_ur!(b, h)
    if iszero(b)
      continue
    else
      h = vcat(h, b)
      hnf!(h)
    end
  end
  return h[1:rank(h), :]
end

function _copy_to_row_matrix!(b::ZZMatrix, c::Vector)
  @assert ncols(b) == length(c)
  for i in 1:ncols(b)
    @inbounds b[1,i] = c[i]
  end
  return b
end

_copy_to_row_matrix!(b::ZZMatrix, c::ZZMatrix) = copy!(b, c)


_short_vector_generators(L::ZZLat; up_to_sign::Bool=false) = _short_vector_generators_with_sublattice(L; up_to_sign)[2]

function _short_vector_generators_with_sublattice_2(L::ZZLat, elem_type::Type{S}=Int; up_to_sign::Bool=false) where {S}
  if iszero(rank(L))
    return ZZLat[], Vector{Vector{S}}[]
  end
  svL = Vector{S}[]
  svL = shortest_vectors(L, S; check=false)
  B = _row_span!(svL)*basis_matrix(L)
  if !up_to_sign
    append!(svL, [-i for i in svL])
  end
  sv = [svL]
  SL = ZZLat[lattice_in_same_ambient_space(L, B; check=false)]
  nrows(B) == rank(L) && return SL, sv
  M = orthogonal_submodule(L, B)
  SM, svM = _short_vector_generators_with_sublattice_2(M, S; up_to_sign)
  T = ZZ.(coordinates(basis_matrix(M), L))
  if S === Int
    _T = [S(i) for i in transpose(T)]
    append!(sv, [[_T*i for i in j] for j in svM])
  else
    @assert S===ZZRingElem
    append!(sv, [[i*T for i in j] for j in svM])
  end
  append!(SL, SM)
  return SL, sv
end

function _short_vector_generators_with_sublattice(L::ZZLat; up_to_sign::Bool=false)
  SL, sv = _short_vector_generators_with_sublattice_2(L; up_to_sign)
  return SL, reduce(append!, sv; init=Vector{ZZRingElem}[])
end


@doc raw"""
    shortest_vectors_sublattice(L::ZZLat; check::Bool=true)
                                            -> ZZLat, ZZLat Vector{ZZMatrix}

Given a definite lattice ``L``, return the sublattice ``M`` of ``L`` spanned
by the vectors of minimal norm in ``L``.

# Examples
```jldoctest
julia> L = integer_lattice(gram = matrix(QQ, 3, 3, [2,0,0,0,2,1,0,1,6]))
Integer lattice of rank 3 and degree 3
with gram matrix
[2   0   0]
[0   2   1]
[0   1   6]

julia> shortest_vectors_sublattice(L)
Integer lattice of rank 2 and degree 3
with gram matrix
[2   0]
[0   2]
```
"""
function shortest_vectors_sublattice(L::ZZLat; check::Bool=true)
  return first(_shortest_vectors_sublattice(L; check))
end

@doc raw"""
    _shortest_vectors_sublattice(L::ZZLat; check::Bool=true)
                                            -> ZZLat, ZZLat Vector{ZZMatrix}

Given a definite lattice ``L``, return the sublattice ``M`` of ``L`` spanned
by the vectors of minimal norm in ``L``. The second output contains the
said vectors, given in terms of the coordinates of ``L``.
"""
function _shortest_vectors_sublattice(L::ZZLat; check::Bool=true)
  @req !check || is_definite(L) "L must be definite"
  V = ambient_space(L)
  sv = ZZMatrix[matrix(ZZ, 1, rank(L), a) for a in shortest_vectors(L)]
  B = _row_span!(sv)*basis_matrix(L)
  M = lattice(V, B; check=false)
  P = primitive_closure(L, M)
  return M, P, sv
end

@doc raw"""
    _shortest_vectors_decomposition(L::ZZLat; closed::Bool=false, check::Bool=true)
                                               -> Vector{ZZLat}, Vector{QQMatrix}

Given a definite lattice ``L``, we define iteratively:
- the lattice $L_0 = L$ and $M_1$ to be the shortest vectors sublattice of $L_0$,
- the lattice $L_i$ is the orthogonal complement of $M_i$ inside $L_{i-1}$ where
  $M_i$ is the shortest vectors sublattice of $L_{i-1}$.
This procedure terminates whenever we reach an integer $j$ such that
$M_{j+1} = L_j$, i.e. $L_j$ is spanned by its vectors of shortest length.

The function returns the primitive closures of the $M_j$'s' as first output, and
the second output ``sv`` is the union of their respective vectors of shortest
length. The said vectors are given in terms of their ambient coordinates.

If `closed == true`, we add to ``sv`` the vector $-v$ for all $v$ in ``sv``.
"""
function _shortest_vectors_decomposition(L::ZZLat; closed::Bool=false, check::Bool=true)
  @req !check || is_definite(L) "L must be definite"
  sv = ZZMatrix[]
  blocks = ZZLat[]
  _L = L
  while rank(_L) > 0
    M, P, svM = _shortest_vectors_sublattice(_L; check=false)
    push!(blocks, P)
    append!(sv, svM)
    _L = orthogonal_submodule(_L, M)
  end
  if closed
    append!(sv, eltype(sv)[-v for v in sv])
  end
  return blocks, sv
end



################################################################################
#
#  Primitive extensions and glue maps
#
################################################################################

@doc raw"""
    primitive_closure(M::ZZLat, N::ZZLat) -> ZZLat

Given two $\mathbb Z$-lattices `M` and `N` with $N \subseteq \mathbb{Q} M$,
return the primitive closure $M \cap \mathbb{Q} N$ of `N` in `M`.

# Examples

```jldoctest
julia> M = root_lattice(:D, 6);

julia> N = lattice_in_same_ambient_space(M, 3*basis_matrix(M)[1:1,:]);

julia> basis_matrix(N)
[3   0   0   0   0   0]

julia> N2 = primitive_closure(M, N)
Integer lattice of rank 1 and degree 6
with gram matrix
[2]

julia> basis_matrix(N2)
[1   0   0   0   0   0]

julia> M2 = primitive_closure(dual(M), M);

julia> is_integral(M2)
false

```
"""
function primitive_closure(M::ZZLat, N::ZZLat)
  @req ambient_space(M) === ambient_space(N) "Lattices must be in the same ambient space"

  ok, B = can_solve_with_solution(basis_matrix(M), basis_matrix(N); side = :left)

  @req ok "N must be contained in the rational span of M"

  Bz = numerator(FakeFmpqMat(B))
  Bz = saturate(Bz)
  return lattice(ambient_space(M), Bz*basis_matrix(M); check = false)
end

@doc raw"""
    is_primitive(M::ZZLat, N::ZZLat) -> Bool

Given two $\mathbb Z$-lattices $N \subseteq M$, return whether `N` is a
primitive sublattice of `M`.

# Examples

```jldoctest
julia> U = hyperbolic_plane_lattice(3);

julia> bU = basis_matrix(U);

julia> e1, e2 = bU[1:1,:], bU[2:2,:]
([1 0], [0 1])

julia> N = lattice_in_same_ambient_space(U, e1 + e2)
Integer lattice of rank 1 and degree 2
with gram matrix
[6]

julia> is_primitive(U, N)
true

julia> M = root_lattice(:A, 3);

julia> f = matrix(QQ, 3, 3, [0 1 1; -1 -1 -1; 1 1 0]);

julia> N = kernel_lattice(M, f+1)
Integer lattice of rank 1 and degree 3
with gram matrix
[4]

julia> is_primitive(M, N)
true
```
"""
function is_primitive(M::ZZLat, N::ZZLat)
  @req is_sublattice(M, N) "N must be a sublattice of M"

  return primitive_closure(M, N) == N
end

@doc raw"""
    glue_map(L::ZZLat, S::ZZLat, R::ZZLat; check=true)
                           -> Tuple{TorQuadModuleMap, TorQuadModuleMap, TorQuadModuleMap}

Given three integral $\mathbb Z$-lattices `L`, `S` and `R`, with `S` and `R`
primitive sublattices of `L` and such that the sum of the ranks of `S` and `R`
is equal to the rank of `L`, return the glue map $\gamma$ of the primitive
extension $S+R \subseteq L$, as well as the inclusion maps of the domain and
codomain of $\gamma$ into the respective discriminant groups of `S` and `R`.

# Example

```jldoctest
julia> M = root_lattice(:E,8);

julia> f = matrix(QQ, 8, 8, [-1 -1  0  0  0  0  0  0;
                              1  0  0  0  0  0  0  0;
                              0  1  1  0  0  0  0  0;
                              0  0  0  1  0  0  0  0;
                              0  0  0  0  1  0  0  0;
                              0  0  0  0  0  1  1  0;
                             -2 -4 -6 -5 -4 -3 -2 -3;
                              0  0  0  0  0  0  0  1]);

julia> S = kernel_lattice(M ,f-1)
Integer lattice of rank 4 and degree 8
with gram matrix
[12   -3    0   -3]
[-3    2   -1    0]
[ 0   -1    2    0]
[-3    0    0    2]

julia> R = kernel_lattice(M , f^2+f+1)
Integer lattice of rank 4 and degree 8
with gram matrix
[ 2   -1    0    0]
[-1    2   -6    0]
[ 0   -6   30   -3]
[ 0    0   -3    2]

julia> glue, iS, iR = glue_map(M, S, R)
(Map: finite quadratic module -> finite quadratic module, Map: finite quadratic module -> finite quadratic module, Map: finite quadratic module -> finite quadratic module)

julia> is_bijective(glue)
true
```
"""
function glue_map(L::ZZLat, S::ZZLat, R::ZZLat; check=true, _snf=true)
  if check
    @req is_integral(L) "The lattices must be integral"
    @req is_primitive(L, S) && is_primitive(L, R) "S and R must be primitive in L"
    @req iszero(basis_matrix(S)*gram_matrix(ambient_space(L))*transpose(basis_matrix(R))) "S and R must be orthogonal in L"
    @req rank(L) == rank(S) + rank(R) "The sum of the ranks of S and R must be equal to the rank of L"
  end

  SR = S+R
  @assert rank(SR) == rank(L)
  orth = orthogonal_submodule(lattice(ambient_space(L)), SR)
  bSR = vcat(basis_matrix(S), basis_matrix(R), basis_matrix(orth))
  ibSR = inv(bSR)
  I = identity_matrix(QQ, degree(L))
  prS = ibSR * I[:,1:rank(S)] * basis_matrix(S)
  prR = ibSR * I[:,rank(S)+1:rank(R)+rank(S)] * basis_matrix(R)
  bL = basis_matrix(L)
  DS = discriminant_group(S)
  DR = discriminant_group(R)
  gens = TorQuadModuleElem[]
  imgs = TorQuadModuleElem[]
  for i in 1:rank(L)
    d = bL[i:i,:]
    g = DS((d * prS)[1,:])
    if is_zero(g)
      continue
    end
    push!(gens, g)
    push!(imgs, DR((d * prR)[1,:]))
  end
  HS, iS = sub(DS, gens)
  HR, iR = sub(DR, imgs)
  glue_map = hom(HS, HR, TorQuadModuleElem[HR(lift(i)) for i in imgs])
  # massage to get an snf
  if _snf
    HS, is = snf(HS)
    iS = is*iS
    HR, ir = snf(HR)
    iR = ir*iR
    glue_map = is*glue_map*inv(ir)
  end
  @hassert :Lattice 2 is_bijective(glue_map)
  @hassert :Lattice 2 overlattice(glue_map) == L
  return glue_map, iS, iR
end

@doc raw"""
    primitive_extension(glue_map::TorQuadModuleMap)

Given the glue map of a primitive extension of $\mathbb Z$-lattices
$S \oplus R \subseteq L$, return `L` and the inclusions of
$S\otimes \QQ $ and $R \otimes \QQ$ into $L \otimes \QQ$.

This creates $L$ inside the direct sum of $S$ and $R$.
If $S$ and $R$ are in the same ambient space consider using
[`overlattice`](@ref) instead.

# Example

We construct the $E_8$ root lattice as a primitive extension of
the $E_6$ and $A_2$ root lattice.
```jldoctest
julia> R = root_lattice(:A,2);

julia> S = root_lattice(:E,6);

julia> DR = discriminant_group(R);

julia> DS = discriminant_group(S);

julia> b, glue_map = is_anti_isometric_with_anti_isometry(DR,DS)
(true, Map: finite quadratic module -> finite quadratic module)

julia> L, iR, iS = Hecke.primitive_extension(glue_map);

julia> L
Integer lattice of rank 8 and degree 8
with gram matrix
[ 2   -1    0    0    0    0    1    0]
[-1    2    0    0    0    0    0    0]
[ 0    0    2   -1    0    0    1    0]
[ 0    0   -1    2   -1    0    0    0]
[ 0    0    0   -1    2   -1   -1   -1]
[ 0    0    0    0   -1    2    1    0]
[ 1    0    1    0   -1    1    2    0]
[ 0    0    0    0   -1    0    0    2]

julia> det(L)
1

```
"""
function primitive_extension(glue_map::TorQuadModuleMap)
  S = relations(domain(glue_map))
  R = relations(codomain(glue_map))
  SR, (iS, iR) = direct_sum(S, R; cached=false)
  S = iS(S)
  R = iR(R)
  glue = Vector{QQFieldElem}[iS(lift(g)) + iR(lift(glue_map(g))) for g in gens(domain(glue_map))]
  rS = rank(S)
  rR = rank(R)
  rSR = rS+rR
  g = length(glue)
  n = rSR + g
  z = zero_matrix(QQ, 0, degree(SR))
  B = reduce(vcat, QQMatrix[matrix(QQ, 1, degree(S), g) for g in glue]; init=z)
  B = vcat(basis_matrix(S), basis_matrix(R), B)
  B = _hnf!_integral(B)
  return lattice(ambient_space(SR), B[end-rank(S)-rank(R)+1:end,:]; check=false), iS, iR
end

@doc raw"""
    overlattice(glue_map::TorQuadModuleMap) -> ZZLat

Given the glue map of a primitive extension of $\mathbb Z$-lattices
$S+R \subseteq L$, return `L`.

# Example

```jldoctest
julia> M = root_lattice(:E,8);

julia> f = matrix(QQ, 8, 8, [ 1  0  0  0  0  0  0  0;
                              0  1  0  0  0  0  0  0;
                              1  2  4  4  3  2  1  2;
                             -2 -4 -6 -5 -4 -3 -2 -3;
                              2  4  6  4  3  2  1  3;
                             -1 -2 -3 -2 -1  0  0 -2;
                              0  0  0  0  0 -1  0  0;
                             -1 -2 -3 -3 -2 -1  0 -1]);

julia> S = kernel_lattice(M ,f-1)
Integer lattice of rank 4 and degree 8
with gram matrix
[ 2   -1     0     0]
[-1    2    -1     0]
[ 0   -1    12   -15]
[ 0    0   -15    20]

julia> R = kernel_lattice(M , f^4+f^3+f^2+f+1)
Integer lattice of rank 4 and degree 8
with gram matrix
[10   -4    0    1]
[-4    2   -1    0]
[ 0   -1    4   -3]
[ 1    0   -3    4]

julia> glue, iS, iR = glue_map(M, S, R);

julia> overlattice(glue) == M
true
```
"""
function overlattice(glue_map::TorQuadModuleMap)
  S = relations(domain(glue_map))
  R = relations(codomain(glue_map))
  @req ambient_space(S) === ambient_space(R) "Lattices lie in different ambient spaces, try `primitive_extension` instead"
  glue = [lift(g) + lift(glue_map(g)) for g in gens(domain(glue_map))]
  z = zero_matrix(QQ, 0, degree(S))
  B = reduce(vcat, QQMatrix[matrix(QQ, 1, degree(S), g) for g in glue]; init=z)
  B = vcat(basis_matrix(S),basis_matrix(R), B)
  B = _hnf!_integral(B)
  return lattice(ambient_space(S), B[end-rank(S)-rank(R)+1:end,:]; check=false)
end

function overlattice(L::ZZLat, glue::Vector{TorQuadModuleElem}; check=true)
  length(glue) == 0 && return L
  D = discriminant_group(L)
  check && @req all(in(D), glue) "glue must be contained in the discriminant group of L"
  B = matrix(QQ, lift.(glue))
  return lattice(ambient_space(L), B; isbasis=false) + L
end

function overlattice(L::ZZLat, glue_group::TorQuadModule; check::Bool=true)
  C = cover(glue_group)
  check && (is_sublattice(C, L) || error("glue group must be of the form C/L"))
  return C
end

@doc raw"""
    overlattices(L; even::Bool=true) -> Vector{ZZLat}

Return all (even) integral overlattices of ``L``.

# Input
- `indices` -- a list of integers; if given only return overlattices ``M`` with index ``[M:L]`` in `indices`.
"""
function overlattices(L::ZZLat; even::Bool=true, indices=nothing)
  @req is_integral(L) "L must be integral"
  D = discriminant_group(L)
  d = ZZ(det(L))
  sq = divexact(d,squarefree_part(d))
  if indices isa Nothing
    indices = divisors(sq)
  else
    indices = ZZ.(indices)
    indices = [i for i in indices if divides(sq, i)[1]]
  end
  result = ZZLat[]
  for g in indices
    CC = submodules(D; order=g)
    if even
      C = ZZLat[overlattice(L, t[1]; check=false) for t in CC if is_totally_isotropic(t[1])]
    else
      C = ZZLat[overlattice(L, t[1]; check=false) for t in CC if iszero(gram_matrix_bilinear(t[1]))]
    end
    append!(result,C)
  end
  return result
end

################################################################################
#
#  Primary/elementary lattices
#
################################################################################

@doc raw"""
    is_primary_with_prime(L::ZZLat) -> Bool, ZZRingElem

Given a $\mathbb Z$-lattice `L`, return whether `L` is primary, that is whether `L`
is integral and its discriminant group (see [`discriminant_group`](@ref)) is a
`p`-group for some prime number `p`. In case it is, `p` is also returned as
second output.

Note that for unimodular lattices, this function returns `(true, 1)`. If the
lattice is not primary, the second return value is `-1` by default.
"""
function is_primary_with_prime(L::ZZLat)
  @req is_integral(L) "L must be integral"
  d = ZZ(abs(det(L)))
  if d == 1
    return true, d
  end
  pd = prime_divisors(d)
  if length(pd) != 1
    return false, ZZ(-1)
  end
  return true, pd[1]
end

@doc raw"""
    is_primary(L::ZZLat, p::Union{Integer, ZZRingElem}) -> Bool

Given an integral $\mathbb Z$-lattice `L` and a prime number `p`,
return whether `L` is `p`-primary, that is whether its discriminant group
(see [`discriminant_group`](@ref)) is a `p`-group.
"""
function is_primary(L::ZZLat, p::Union{Integer, ZZRingElem})
  bool, q = is_primary_with_prime(L)
  return bool && q == p
end

@doc raw"""
    is_unimodular(L::ZZLat) -> Bool

Given an integral $\mathbb Z$-lattice `L`, return whether `L` is unimodular,
that is whether its discriminant group (see [`discriminant_group`](@ref))
is trivial.
"""
is_unimodular(L::ZZLat) = is_primary(L, 1)

@doc raw"""
    is_elementary_with_prime(L::ZZLat) -> Bool, ZZRingElem

Given a $\mathbb Z$-lattice `L`, return whether `L` is elementary, that is whether
`L` is integral and its discriminant group (see [`discriminant_group`](@ref)) is
an elemenentary `p`-group for some prime number `p`. In case it is, `p` is also
returned as second output.

Note that for unimodular lattices, this function returns `(true, 1)`. If the lattice
is not elementary, the second return value is `-1` by default.
"""
function is_elementary_with_prime(L::ZZLat)
  bool, p = is_primary_with_prime(L)
  bool || return false, ZZ(-1)
  if !is_integer(p*scale(dual(L)))
    return false, ZZ(-1)
  end
  return bool, p
end

@doc raw"""
    is_elementary(L::ZZLat, p::Union{Integer, ZZRingElem}) -> Bool

Given an integral $\mathbb Z$-lattice `L` and a prime number `p`, return whether
`L` is `p`-elementary, that is whether its discriminant group
(see [`discriminant_group`](@ref)) is an elementary `p`-group.
"""
function is_elementary(L::ZZLat, p::Union{Integer, ZZRingElem})
  bool, q = is_elementary_with_prime(L)
  return bool && q == p
end


@attr Bool function is_well_rounded(L::ZZLat)
  S = shortest_vectors_sublattice(L)
  return rank(S) == rank(L)
end

@attr Bool function is_strongly_well_rounded(L::ZZLat)
  S = shortest_vectors_sublattice(L)
  return S == L
end

# brute force
function is_obviously_perfectly_well_rounded_with_data(L::ZZLat; max_tries = 100, lll_perturbed=true)
  L = lll(L)
  S = shortest_vectors_sublattice(L)
  S == L || return false, zero_matrix(QQ, 0, degree(L))
  m = minimum(L)
  # see if we can replace a bad vector by a good one
  flag = true
  while flag
    flag, L = improve_basis(L)
  end
  if m == maximum(abs.(diagonal(gram_matrix(L))))
    return true, basis_matrix(L)
  end
  if minimum(L) == 2
    # root lattices are always perfectly well rounded
    # the fundamental root system is a basis
    B = basis_matrix(root_lattice_recognition_fundamental(L)[1])
    return true, B
  end
  n = rank(L)
  U = hnf_with_transform(matrix(ZZ,n,n, rand(0:1,n^2)))[2]
  Llll = lattice_in_same_ambient_space(L, U*basis_matrix(L))
  if lll_perturbed
    return is_obviously_perfectly_well_rounded_with_data(Llll; max_tries, lll_perturbed=false)
  end
  # brute force try for random combinations
  sv = shortest_vectors(L)
  n = rank(L)
  SV = Set([matrix(ZZ,1, n, i) for i in sv])
  for (i,B) in enumerate(subsets(SV, n))
    i > max_tries && return false, zero_matrix(QQ, 0, degree(L))
    Bmat = reduce(vcat, B)
    rank(Bmat) == n || continue
    all(isone, elementary_divisors(Bmat)) && return true, Bmat
  end
  return false, zero_matrix(ZZ, 0, degree(L))
end

is_obviously_perfectly_well_rounded(L::ZZLat; max_tries=100) = is_obviously_perfectly_well_rounded_with_data(L;max_tries)[1]


@attr Bool function is_lopsided(L::ZZLat)
  S = shortest_vectors_sublattice(L)
  return rank(S) < rank(L)
end

