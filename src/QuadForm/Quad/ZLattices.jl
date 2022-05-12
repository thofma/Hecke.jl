export *,+, basis_matrix, ambient_space, base_ring, base_field, root_lattice,
       kernel_lattice, invariant_lattice, hyperbolic_plane_lattice
# scope & verbose scope: :Lattice

basis_matrix(L::ZLat) = L.basis_matrix

ambient_space(L::ZLat) = L.space

base_ring(L::ZLat) = FlintZZ

base_field(L::ZLat) = base_ring(gram_matrix(ambient_space(L)))

################################################################################
#
#  Creation
#
################################################################################

@doc Markdown.doc"""
    Zlattice([B::MatElem]; gram) -> ZLat

Return the Z-lattice with basis matrix $B$ inside the quadratic space with
Gram matrix `gram`.

If the keyword `gram` is not specified, the Gram matrix is the identity matrix.
If $B$ is not specified, the basis matrix is the identity matrix.

# Examples

```jldoctest
julia> L = Zlattice(matrix(QQ, 2, 2, [1//2, 0, 0, 2]));

julia> gram_matrix(L) == matrix(QQ, 2, 2, [1//4, 0, 0, 4])
true

julia> L = Zlattice(gram = matrix(ZZ, [2 -1; -1 2]));

julia> gram_matrix(L) == matrix(ZZ, [2 -1; -1 2])
true
```
"""
function Zlattice(B::fmpq_mat; gram = identity_matrix(FlintQQ, ncols(B)))
  @req is_symmetric(gram) "Gram matrix must be symmetric"
  V = quadratic_space(FlintQQ, gram)
  return lattice(V, B)
end

function Zlattice(B::fmpz_mat; gram = identity_matrix(FlintQQ, ncols(B)))
  @req is_symmetric(gram) "Gram matrix must be symmetric"
  V = quadratic_space(FlintQQ, gram)
  return lattice(V, B)
end

function Zlattice(;gram)
  @req is_symmetric(gram) "Gram matrix must be symmetric"
  n = nrows(gram)
  return lattice(quadratic_space(FlintQQ, gram), identity_matrix(FlintQQ, n))
end

@doc Markdown.doc"""
    lattice(V::QuadSpace, B::MatElem) -> ZLat

Return the Z-lattice with basis matrix $B$ inside the quadratic space $V$.
"""
function lattice(V::QuadSpace{FlintRationalField, fmpq_mat}, B::MatElem; isbasis::Bool = true, check::Bool = true)
  @req dim(V) == ncols(B) "Ambient space and the matrix B have incompatible dimension"
  local Gc
  try
    Gc = change_base_ring(FlintQQ, B)
  catch e
    throw(error("Cannot convert entries of the matrix to the rationals"))
  end
  if typeof(Gc) !== fmpq_mat
    throw(error("Cannot convert entries of the matrix to the rationals"))
  end

  # We need to produce a basis matrix

  if !isbasis
    BB = fmpq_mat(hnf(FakeFmpqMat(B), :upper_right))
    i = nrows(BB)
    while i > 0 && is_zero_row(BB, i)
      i = i - 1
    end
    return ZLat(V, BB[1:i, :])
  else
    return ZLat(V, Gc)
  end
end

function lattice_in_same_ambient_space(L::ZLat, B::MatElem)
  V = L.space
  return lattice(V,B)
end

function rescale(G::ZLat, r)
  B = basis_matrix(G)
  gram_space = gram_matrix(G.space)
  Vr = quadratic_space(QQ, r*gram_space)
  return lattice(Vr, B)
end

################################################################################
#
#  Gram matrix
#
################################################################################

@doc Markdown.doc"""
    gram_matrix(L::ZLat) -> fmpq_mat

Return the gram matrix of $L$.

# Examples
```jldoctest
julia> L = Zlattice(matrix(ZZ, [2 0; -1 2]));

julia> gram_matrix(L)
[ 4   -2]
[-2    5]
```
"""
function gram_matrix(L::ZLat)
  if isdefined(L, :gram_matrix)
    return L.gram_matrix
  end
  b = basis_matrix(L)
  G = b * gram_matrix(ambient_space(L)) * transpose(b)
  L.gram_matrix = G
  return G
end

gram_matrix_of_rational_span(L::ZLat) = gram_matrix(L)

################################################################################
#
#  Rational span
#
################################################################################

@doc Markdown.doc"""
    rational_span(L::ZLat) -> QuadSpace

Return the rational span of $L$, which is the quadratic space with Gram matrix
equal to `gram_matrix(L)`.

# Examples
```jldoctest
julia> L = Zlattice(matrix(ZZ, [2 0; -1 2]));

julia> rational_span(L)
Quadratic space over
Rational Field
with Gram matrix
[4 -2; -2 5]
```
"""
function rational_span(L::ZLat)
  if isdefined(L, :rational_span)
    return L.rational_span
  else
    G = gram_matrix(L)
    V = quadratic_space(FlintQQ, G)
    L.rational_span = V
    return V
  end
end

################################################################################
#
#  Orthogonal sum
#
################################################################################

@doc Markdown.doc"""
    orthogonal_sum(L1::ZLat, L2::ZLat)

Return the orthogonal direct sum of the lattices `L1` and `L2`.
"""
function orthogonal_sum(L1::ZLat, L2::ZLat)
  V1 = ambient_space(L1)
  V2 = ambient_space(L2)
  B1 = basis_matrix(L1)
  B2 = basis_matrix(L2)
  B = diagonal_matrix(B1, B2)
  V, f1, f2 = orthogonal_sum(V1, V2)
  return lattice(V, B), f1, f2
end

@doc Markdown.doc"""
    orthogonal_submodule(L::ZLat, S::ZLat) -> ZLat

Return the largest submodule of `L` orthogonal to `S`.
"""
function orthogonal_submodule(L::ZLat, S::ZLat)
  @assert ambient_space(L)==ambient_space(S) "L and S must have the same ambient space"
  B = basis_matrix(L)
  C = basis_matrix(S)
  V = ambient_space(L)
  G = gram_matrix(V)
  M = B * G * transpose(C)
  _, K = left_kernel(M)
  K = change_base_ring(ZZ, K*denominator(K))
  Ks = saturate(K)
  return lattice(V, Ks*B)
end
################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, L::ZLat)
  print(io, "Quadratic lattice of rank ", rank(L),
            " and degree ", degree(L), " over the rationals")
end

################################################################################
#
#  Automorphism groups
#
################################################################################

# This is an internal function, which sets
# L.automorphism_group_generators
# L.automorphism_group_order
function assert_has_automorphisms(L::ZLat; redo::Bool = false,
                                           try_small::Bool = true)

  if !redo && isdefined(L, :automorphism_group_generators)
    return nothing
  end

  if rank(L) == 0
    L.automorphism_group_generators = fmpz_mat[identity_matrix(ZZ, 0)]
    L.automorphism_group_order = one(fmpz)
    return nothing
  end

  V = ambient_space(L)
  GL = gram_matrix(L)
  d = denominator(GL)
  res = fmpz_mat[change_base_ring(FlintZZ, d * GL)]
  # So the first one is either positive definite or negative definite
  # Make it positive definite. This does not change the automorphisms.
  if res[1][1, 1] < 0
    res[1] = -res[1]
  end
  Glll, T = lll_gram_with_transform(res[1])
  Ttr = transpose(T)
  res_orig = copy(res)
  res[1] = Glll

  bm = basis_matrix(L)

  # Make the Gram matrix small

  C = ZLatAutoCtx(res)
  if try_small
    fl, Csmall = try_init_small(C)
    if fl
      auto(Csmall)
      _gens, order = _get_generators(Csmall)
      gens = fmpz_mat[matrix(FlintZZ, g) for g in _gens]
    else
      init(C)
      auto(C)
      gens, order = _get_generators(C)
    end
  else
    init(C)
    auto(C)
    gens, order = _get_generators(C)
  end

  # Now translate back
  Tinv = inv(T)
  for i in 1:length(gens)
    gens[i] = Tinv * gens[i] * T
  end

  # Now gens are with respect to the basis of L
  @hassert :Lattice 1 all(change_base_ring(FlintQQ, gens[i]) * GL *
                          transpose(change_base_ring(FlintQQ, gens[i])) == GL
                                                        for i in 1:length(gens))

  L.automorphism_group_generators = gens
  L.automorphism_group_order = order

  return nothing
end

# documented in ../Lattices.jl

function automorphism_group_generators(L::ZLat; ambient_representation::Bool = true)

  @req rank(L) == 0 || is_definite(L) "The lattice must be definite"
  assert_has_automorphisms(L)

  gens = L.automorphism_group_generators
  if !ambient_representation
    return fmpq_mat[ change_base_ring(FlintQQ, g) for g in gens]
  else
    # Now translate to get the automorphisms with respect to basis_matrix(L)
    bm = basis_matrix(L)
    gens = L.automorphism_group_generators
    V = ambient_space(L)
    if rank(L) == rank(V)
      bminv = inv(bm)
      res = fmpq_mat[bminv * change_base_ring(FlintQQ, g) * bm for g in gens]
    else
      # Extend trivially to the orthogonal complement of the rational span
      !is_regular(V) &&
        throw(error(
          """Can compute ambient representation only if ambient space is
             regular"""))
      C = orthogonal_complement(V, basis_matrix(L))
      C = vcat(basis_matrix(L), C)
      Cinv = inv(C)
      D = identity_matrix(FlintQQ, rank(V) - rank(L))
      res = fmpq_mat[Cinv * diagonal_matrix(change_base_ring(FlintQQ, g), D) * C for g in gens]
    end
    @hassert :Lattice 1 all(g * gram_matrix(V) * transpose(g) == gram_matrix(V)
                            for g in res)
    return res
  end
end

# documented in ../Lattices.jl

function automorphism_group_order(L::ZLat)
  assert_has_automorphisms(L)
  return L.automorphism_group_order
end

################################################################################
#
#  Isometry
#
################################################################################

# documented in ../Lattices.jl

function is_isometric(L::ZLat, M::ZLat; ambient_representation::Bool = true)
  @req is_definite(L) && is_definite(M) "The lattices must be definite"

  if rank(L) != rank(M)
    return false, zero_matrix(FlintQQ, 0, 0)
  end

  if rank(L) == 0
    return true, identity_matrix(FlintQQ, 0, 0)
  end

  i = sign(gram_matrix(L)[1,1])
  j = sign(gram_matrix(M)[1,1])
  @req i==j "The lattices must have the same signatures"

  if i < 0
    L = rescale(L,-1)
    M = rescale(M,-1)
  end

  GL = gram_matrix(L)
  dL = denominator(GL)
  GLint = change_base_ring(FlintZZ, dL * GL)
  cL = content(GLint)
  GLint = divexact(GLint, cL)

  GM = gram_matrix(M)
  dM = denominator(GM)
  GMint = change_base_ring(FlintZZ, dM * GM)
  cM = content(GMint)
  GMint = divexact(GMint, cM)

  # GLint, GMint are integral, primitive scalings of GL and GM
  # If they are isometric, then the scalars must be identitcal.
  if dL//cL != dM//cM
    return false, zero_matrix(FlintQQ, 0, 0)
  end

  # Now compute LLL reduces gram matrices

  GLlll, TL = lll_gram_with_transform(GLint)
  @hassert :Lattice 1 TL * change_base_ring(FlintZZ, GL) * transpose(TL) * dL == GLlll *cL
  GMlll, TM = lll_gram_with_transform(GMint)
  @hassert :Lattice 1 TM * change_base_ring(FlintZZ, GM) * transpose(TM) * dM == GMlll *cM

  # Setup for Plesken--Souvignier

  G1 = fmpz_mat[GLlll]
  G2 = fmpz_mat[GMlll]

  fl, CLsmall, CMsmall = _try_iso_setup_small(G1, G2)
  if fl
    b, _T = isometry(CLsmall, CMsmall)
    T = matrix(FlintZZ, _T)
  else
    CL, CM = _iso_setup(fmpz_mat[GLlll], fmpz_mat[GMlll])
    b, T = isometry(CL, CM)
  end

  if b
    T = change_base_ring(FlintQQ, inv(TL)*T*TM)
    if !ambient_representation
      @hassert :Lattice 1 T * gram_matrix(M) * transpose(T) == gram_matrix(L)
      return true, T
    else
      V = ambient_space(L)
      W = ambient_space(M)
      if rank(L) == rank(V)
        T = inv(basis_matrix(L)) * T * basis_matrix(M)
      else
        (!is_regular(V) || !is_regular(W)) &&
          throw(error(
            """Can compute ambient representation only if ambient space is
               regular"""))
          (rank(V) != rank(W)) &&
          throw(error(
            """Can compute ambient representation only if ambient spaces
            have the same dimension."""))

        CV = orthogonal_complement(V, basis_matrix(L))
        CV = vcat(basis_matrix(L), CV)
        CW = orthogonal_complement(W, basis_matrix(M))
        CW = vcat(basis_matrix(M), CW)
        D = identity_matrix(FlintQQ, rank(V) - rank(L))
        T = inv(CV) * diagonal_matrix(T, D) * CW
      end
      @hassert :Lattice 1 T * gram_matrix(ambient_space(M))  * transpose(T) ==
                  gram_matrix(ambient_space(L))
      return true, T
    end
  else
    return false, zero_matrix(FlintQQ, 0, 0)
  end
end

################################################################################
#
#  Is sublattice?
#
################################################################################

function is_sublattice(M::ZLat, N::ZLat)
  if ambient_space(M) != ambient_space(N)
    return false
  end

  hassol, _rels = can_solve_with_solution(basis_matrix(M), basis_matrix(N), side=:left)

  if !hassol || !isone(denominator(_rels))
    return false
  end

  return true
end

@doc Markdown.doc"""
    is_sublattice_with_relations(M::ZLat, N::ZLat) -> Bool, fmpq_mat

Returns whether $N$ is a sublattice of $M$. In this case, the second return
value is a matrix $B$ such that $B B_M = B_N$, where $B_M$ and $B_N$ are the
basis matrices of $M$ and $N$ respectively.
"""
function is_sublattice_with_relations(M::ZLat, N::ZLat)
   if ambient_space(M) != ambient_space(N)
     return false, basis_matrix(M)
   end

   hassol, _rels = can_solve_with_solution(basis_matrix(M), basis_matrix(N), side=:left)

   if !hassol || !isone(denominator(_rels))
     return false, basis_matrix(M)
   end

   return true, _rels
 end

################################################################################
#
#  Root lattice
#
################################################################################

@doc Markdown.doc"""
    root_lattice(R::Symbol, n::Int)

Return the root lattice of type `R` given by ``:A``, ``:D`` or ``:E`` with parameter `n`.
"""
function root_lattice(R::Symbol, n::Int)
  if R === :A
    return Zlattice(gram = _root_lattice_A(n))
  elseif R === :E
    return Zlattice(gram = _root_lattice_E(n))
  elseif R === :D
    return Zlattice(gram = _root_lattice_D(n))
  else
    error("Type (:$R) must be :A, :D or :E")
  end
end

function _root_lattice_A(n::Int)
  n < 0 && error("Parameter ($n) for root lattice of type :A must be positive")
  z = zero_matrix(FlintQQ, n, n)
  for i in 1:n
    z[i, i] = 2
    if i > 1
      z[i, i - 1] = -1
    end
    if i < n
      z[i, i + 1] = -1
    end
  end
  return z
end

function _root_lattice_D(n::Int)
  n < 2 && error("Parameter ($n) for root lattices of type :D must be greater or equal to 2")
  if n == 2
    G = matrix(ZZ, [2 0 ;0 2])
  elseif n == 3
    return _root_lattice_A(n)
  else
    G = zero_matrix(ZZ, n, n)
    G[1,3] = G[3,1] = -1
    for i in 1:n
      G[i,i] = 2
      if 2 <= i <= n-1
        G[i,i+1] = G[i+1,i] = -1
      end
    end
  end
  return G
end

function _root_lattice_E(n::Int)
  n in [6,7,8] || error("Parameter ($n) for lattice of type :E must be 6, 7 or 8")
  if n == 6
    G = [2 -1 0 0 0 0;
        -1 2 -1 0 0 0;
        0 -1 2 -1 0 -1;
        0 0 -1 2 -1 0;
        0 0 0 -1 2 0;
        0 0 -1 0 0 2]
  elseif n == 7
    G = [2 -1 0 0 0 0 0;
        -1 2 -1 0 0 0 0;
        0 -1 2 -1 0 0 -1;
        0 0 -1 2 -1 0 0;
        0 0 0 -1 2 -1 0;
        0 0 0 0 -1 2 0;
        0 0 -1 0 0 0 2]
  else
    G = [2 -1 0 0 0 0 0 0;
        -1 2 -1 0 0 0 0 0;
        0 -1 2 -1 0 0 0 -1;
        0 0 -1 2 -1 0 0 0;
        0 0 0 -1 2 -1 0 0;
        0 0 0 0 -1 2 -1 0;
        0 0 0 0 0 -1 2 0;
        0 0 -1 0 0 0 0 2]
  end
  return matrix(ZZ, G)
end

################################################################################
#
#  Hyperbolic plane
#
################################################################################

@doc Markdown.doc"""
    Zlattice(S::Symbol, n::Union{Int64, fmpz} = 1) -> Zlat

Given `S = :H` or `S = :U`, return a $\mathbb Z$-lattice admitting $n*J_2$ as
Gram matrix in some basis, where $J_2$ is the 2-by-2 matrix with 0's on the
main diagonal and 1's elsewhere.
"""
function Zlattice(S::Symbol, n::Union{Int64, fmpz} = 1)
  @req S === :H || S === :U "Only available for the hyperbolic plane"
  gram = n*identity_matrix(ZZ, 2)
  gram = reverse_cols!(gram)
  return Zlattice(gram = gram)
end

@doc Markdown.doc"""
    hyperbolic_plane_lattice(n::Union{Int64, fmpz} = 1)

Return the hyperbolic plane with intersection form of scale `n`, that is,
the unique (up to isometry) even unimodular hyperbolic $\mathbb Z$-lattice
of rank 2, rescaled by `n`.

# Examples

```jldoctest
julia> L = hyperbolic_plane_lattice(6);

julia> gram_matrix(L)
[0   6]
[6   0]

julia> L = hyperbolic_plane_lattice(ZZ(-13));

julia> gram_matrix(L)
[  0   -13]
[-13     0]
```
"""
hyperbolic_plane_lattice(n::Union{Int64, fmpz} = 1) = Zlattice(:H, n)

################################################################################
#
#  Dual lattice
#
################################################################################

# documented in ../Lattices.jl

function dual(L::ZLat)
  G = gram_matrix(L)
  new_bmat = inv(G)*basis_matrix(L)
  return lattice(ambient_space(L), new_bmat)
end

################################################################################
#
#  Scale
#
################################################################################

function scale(L::ZLat)
  if isdefined(L, :scale)
    return L.scale
  end
  G = gram_matrix(L)
  s = zero(fmpq)
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

function norm(L::ZLat)
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

################################################################################
#
#  Eveness
#
################################################################################

iseven(L::ZLat) = is_integral(L) && iseven(numerator(norm(L)))

################################################################################
#
#  Discriminant
#
################################################################################

function discriminant(L::ZLat)
  d = det(gram_matrix(L))
  return d
end

################################################################################
#
#  Determinant
#
################################################################################

function det(L::ZLat)
  return det(gram_matrix(L))
end

################################################################################
#
#  Rank
#
################################################################################

function rank(L::ZLat)
  return nrows(basis_matrix(L))
end

################################################################################
#
#  Local basis matrix
#
################################################################################

# so that abstract lattice functions also work with Z-lattices

local_basis_matrix(L::ZLat, p) = basis_matrix(L)

################################################################################
#
#  Intersection
#
################################################################################

function intersect(M::ZLat, N::ZLat)
  @req ambient_space(M) === ambient_space(N) "Lattices must have same ambient space"
  BM = basis_matrix(M)
  BN = basis_matrix(N)
  dM = denominator(BM)
  dN = denominator(BN)
  d = lcm(dM, dN)
  BMint = change_base_ring(FlintZZ, d * BM)
  BNint = change_base_ring(FlintZZ, d * BN)
  H = vcat(BMint, BNint)
  k, K = left_kernel(H)
  BI = divexact(change_base_ring(FlintQQ, hnf(view(K, 1:k, 1:nrows(BM)) * BMint)), d)
  return lattice(ambient_space(M), BI)
end

################################################################################
#
#  Sum
#
################################################################################

function +(M::ZLat, N::ZLat)
  @req ambient_space(M) === ambient_space(N) "Lattices must have same ambient space"
  BM = basis_matrix(M)
  BN = basis_matrix(N)
  B = fmpq_mat(hnf(FakeFmpqMat(vcat(BM, BN))))
  i = 1
  while is_zero_row(B, i)
    i += 1
  end
  return lattice(ambient_space(M), B[i:end, 1:ncols(B)])
end

################################################################################
#
#  Local isometry
#
################################################################################

# TODO: This is slow. We need a dedicated implementation

function is_locally_isometric(L::ZLat, M::ZLat, p::Int)
  return is_locally_isometric(L, M, fmpz(p))
end

function is_locally_isometric(L::ZLat, M::ZLat, p::fmpz)
  LL = _to_number_field_lattice(L)
  K = base_field(LL)
  MM = _to_number_field_lattice(L, K = K)
  OK = maximal_order(K)
  P = prime_decomposition(OK, p)[1][1]
  return is_locally_isometric(LL, MM, P)
end

################################################################################
#
#  Conversion between ZLat and QuadLat
#
################################################################################

function _to_number_field_lattice(L::ZLat, K, V)
  LL = lattice(V, change_base_ring(K, basis_matrix(L)))
  return LL
end

function _to_number_field_lattice(L::ZLat;
                                  K::AnticNumberField = rationals_as_number_field()[1],
                                  V::QuadSpace = quadratic_space(K, gram_matrix(ambient_space(L))))
  return _to_number_field_lattice(L, K, V)
end


function _to_ZLat(L::QuadLat, K, V)
  pm = pseudo_matrix(L)
  cm = coefficient_ideals(pm)
  pmm = matrix(pm)
  bm = zero_matrix(FlintQQ, rank(L), dim(V))
  for i in 1:nrows(pm)
    a = norm(cm[i])
    for j in 1:ncols(pm)
      bm[i, j] = a * FlintQQ(pmm[i, j])
    end
  end
  return lattice(V, bm)
end

function _to_ZLat(L::QuadLat;
                  K::FlintRationalField = FlintQQ,
                  V::QuadSpace = quadratic_space(K, map_entries(FlintQQ, gram_matrix(ambient_space(L)))))
  return _to_ZLat(L, K, V)
end

################################################################################
#
#  Mass
#
################################################################################

mass(L::ZLat) = mass(_to_number_field_lattice(L))

################################################################################
#
#  Genus representatives
#
################################################################################

function genus_representatives(L::ZLat)
  LL = _to_number_field_lattice(L)
  K = base_field(L)
  G = genus_representatives(LL)
  res = ZLat[]
  for N in G
    push!(res, _to_ZLat(N, K = K))
  end
  return res
end

################################################################################
#
#  Maximal integral lattice
#
################################################################################

function maximal_integral_lattice(L::ZLat)
  LL = _to_number_field_lattice(L)
  M = maximal_integral_lattice(LL)
  return _to_ZLat(M, V = ambient_space(L))
end

################################################################################
#
#  Scalar multiplication
#
################################################################################

@doc Markdown.doc"""
    *(a, L::ZLat) -> ZLat

Returns the lattice $aM$ inside the ambient space of $M$.
"""
function Base.:(*)(a, L::ZLat)
  @assert has_ambient_space(L)
  B = a*L.basis_matrix
  return lattice_in_same_ambient_space(L, B)
end

function Base.:(*)(L::ZLat, a)
  return a * L
end


################################################################################
#
#  Equality
#
################################################################################

@doc Markdown.doc"""
Return ``true`` if both lattices have the same ambient quadratic space
and the same underlying module.
"""
function Base.:(==)(L1::ZLat, L2::ZLat)
  V1 = ambient_space(L1)
  V2 = ambient_space(L2)
  if V1 != V2
    return false
  end
  B1 = basis_matrix(L1)
  B2 = basis_matrix(L2)
  return hnf(FakeFmpqMat(B1)) == hnf(FakeFmpqMat(B2))
end

@doc Markdown.doc"""
    local_modification(M::ZLat, L::ZLat, p)

Return a local modification of `M` that matches `L` at `p`.

INPUT:

- ``M`` -- a `\ZZ_p`-maximal lattice
- ``L`` -- the a lattice
            isomorphic to `M` over `\QQ_p`
- ``p`` -- a prime number

OUTPUT:

an integral lattice `M'` in the ambient space of `M` such that `M` and `M'` are locally equal at all
completions except at `p` where `M'` is locally isometric to the lattice `L`.
"""
function local_modification(M::ZLat, L::ZLat, p)
  # notation
  d = denominator(inv(gram_matrix(L)))
  level = valuation(d,p)
  d = p^(level+1) # +1 since scale(M) <= 1/2 ZZ

  @req is_isometric(L.space, M.space, p) "quadratic spaces must be locally isometric at m"
  L_max = maximal_integral_lattice(L)

  # invert the gerstein operations
  GLm, U = padic_normal_form(gram_matrix(L_max), p, prec=level+3)
  B1 = inv(U*basis_matrix(L_max))

  GM, UM = padic_normal_form(gram_matrix(M), p, prec=level+3)
  # assert GLm == GM at least modulo p^prec
  B2 = B1 * UM * basis_matrix(M)
  Lp = lattice(M.space, B2)

  # the local modification
  S = intersect(Lp, M) + d * M
  # confirm result
  @hassert :Lattice 2 genus(S, p)==genus(L, p)
  return S
end

################################################################################
#
#  Kernel lattice
#
################################################################################

@doc Markdown.doc"""
    kernel_lattice(L::ZLat, f::MatElem;
                   ambient_representation::Bool = true) -> ZLat

Given a $\mathbf{Z}$-lattice $L$ and a matrix $f$ inducing an endomorphism of
$L$, return $\ker(f)$ is a sublattice of $L$.

If `ambient_representation` is `true` (the default), the endomorphism is
represented with respect to the ambient space of $L$. Otherwise, the
endomorphism is represented with respect to the basis of $L$.
"""
function kernel_lattice(L::ZLat, f::MatElem; ambient_representation::Bool = true)
  bL = basis_matrix(L)
  if ambient_representation
    if !is_square(bL)
      fl, finL = can_solve_with_solution(bL, bL * f, side = :left)
      @req fl "f must preserve the lattice L"
    else
      finL = bL * f * inv(bL)
    end
  else
    finL = f
  end
  k, K = left_kernel(change_base_ring(ZZ, finL))
  return lattice(ambient_space(L), K * basis_matrix(L))
end

################################################################################
#
#  Invariant lattice
#
################################################################################

@doc Markdown.doc"""
    invariant_lattice(L::ZLat, G::Vector{MatElem};
                      ambient_representation::Bool = true) -> ZLat

Given a $\mathbf{Z}$-lattice $L$ and a list of matrices $G$ inducing
endomorphisms of $L$, return the lattice $L^G$, consisting of elements fixed by
$G$.

If `ambient_representation` is `true` (the default), the endomorphism is
represented with respect to the ambient space of $L$. Otherwise, the
endomorphism is represented with respect to the basis of $L$.
"""
function invariant_lattice(L::ZLat, G::Vector{<:MatElem};
                           ambient_representation::Bool = true)
  if length(G) == 0
    return L
  end

  M = kernel_lattice(L, G[1] - 1,
                     ambient_representation = ambient_representation)
  for i in 2:length(G)
    N = kernel_lattice(L, G[i] - 1,
                       ambient_representation = ambient_representation)
    M = intersect(M, N)
  end
  return M
end

function invariant_lattice(L::ZLat, G::MatElem;
                           ambient_representation::Bool = true)
  return kernel_lattice(L, G - 1, ambient_representation = ambient_representation)
end

################################################################################
#
#  Membership check
#
################################################################################

@doc Markdown.doc"""
    Base.in(v::Vector, L::ZLat) -> Bool

  Check if the vector `v` lies in the lattice `L` or not.
"""
function Base.in(v::Vector, L::ZLat)
  @assert length(v) == degree(L) "The vector should have the same length as the degree of the lattice."
  V = matrix(QQ, 1, length(v), v)
  return V in L
end

@doc Markdown.doc"""
    Base.in(v::fmpq_mat, L::ZLat) -> Bool

  Check if the row span of `v` lies in the lattice `L` or not.
"""
function Base.in(v::fmpq_mat, L::ZLat)
  @assert ncols(v)==degree(L) "The vector should have the same length as the degree of the lattice."
  B = basis_matrix(L)
  fl, w = can_solve_with_solution(B, v, side=:left)
  return fl && isone(denominator(w))
end

