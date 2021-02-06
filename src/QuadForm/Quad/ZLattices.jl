# scope & verbose scope: :Lattice

basis_matrix(L::ZLat) = L.basis_matrix

ambient_space(L::ZLat) = L.space

base_ring(L::ZLat) = FlintZZ

################################################################################
#
#  Creation
#
################################################################################

@doc Markdown.doc"""
    Zlattice([B::MatElem]; gram) -> ZLat

Return the Z-lattice with basis matrix $B$ inside the quadratic space with
Gram matrix `gram`.

If `gram` is not specified, the Gram matrix is the identity matrix. If $B$
is not specified, the basis matrix is the identity matrix.
"""
function Zlattice(B::fmpq_mat; gram = identity_matrix(FlintQQ, ncols(B)))
  V = quadratic_space(FlintQQ, gram)
  return lattice(V, B)
end

function Zlattice(B::fmpz_mat; gram = identity_matrix(FlintQQ, ncols(B)))
  V = quadratic_space(FlintQQ, gram)
  return lattice(V, B)
end

function Zlattice(;gram)
  n = nrows(gram)
  return lattice(quadratic_space(FlintQQ, gram), identity_matrix(FlintQQ, n))
end

@doc Markdown.doc"""
    lattice(V::QuadSpace, B::MatElem) -> ZLat

Return the Z-lattice with basis matrix $B$ inside the quadratic space $V$.
"""
function lattice(V::QuadSpace{FlintRationalField, fmpq_mat}, B::MatElem; isbasis::Bool = true)
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
    while iszero_row(BB, i)
      i = i - 1
    end
    return ZLat(V, BB[1:i, :])
  else
    return ZLat(V, Gc)
  end
end

################################################################################
#
#  Gram matrix
#
################################################################################

@doc Markdown.doc"""
    gram_matrix(L::ZLat) -> fmpq_mat

Return the gram matrix of $L$.
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

Return the orthogonal direct sum of the lattice L1 and L2.
"""
function orthogonal_sum(L1::ZLat, L2::ZLat)
  V1 = ambient_space(L1)
  V2 = ambient_space(L2)
  B1 = basis_matrix(L1)
  B2 = basis_matrix(L2)
  B = diagonal_matrix(B1, B2)
  V = orthogonal_sum(V1, V2)
  return lattice(V, B)
end

@doc Markdown.doc"""
    orthogonal_submodule(L::ZLat, S::ZLat) -> ZLat

Return the orthogonal submodule lattice of the subset S of lattice L.
"""
function orthogonal_submodule(L::ZLat, S::ZLat)
  @assert issublattice(L, S) "S is not a sublattice of L"
  B = basis_matrix(L)
  C = basis_matrix(S)
  V = ambient_space(L)
  G = gram_matrix(V)
  M = B * G * transpose(C)
  K = left_kernel(M)
  return lattice(V, K[2]*B) #this will be the orthogonal submodule of S
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

  @req isdefinite(L) "The lattice must be definite"
  assert_has_automorphisms(L)

  gens = L.automorphism_group_generators
  if !ambient_representation
    return fmpq_mat[ change_base_ring(FlintQQ, g) for g in gens]
  else
    # Now translate to get the automorphisms with respect to basis_matrix(L)
    bm = basis_matrix(L)
    bminv = inv(bm)
    gens = L.automorphism_group_generators
    V = ambient_space(L)
    if rank(L) == rank(V)
      res = fmpq_mat[bminv * change_base_ring(FlintQQ, g) * bm for g in gens]
    else
      # Extend trivially to the orthogonal complement of the rational span
      !isregular(V) &&
        throw(error(
          """Can compute ambient representation only if ambient space is
             regular"""))
      C = orthogonal_complement(V, basis_matrix(L))
      C = vcat(basis_matrix(L), C)
      Cinv = inv(C)
      D = identity_matrix(FlintQQ, rank(V) - rank(L))
      res = fmpq_mat[Cinv * diagonal_matrix(change_base_ring(FlintQQ, g), D) * C for g in gens]
    end
    @hassert :Lattice 1 all(g * gram_matrix(V) * g' == gram_matrix(V)
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

function isisometric(L::ZLat, M::ZLat; ambient_representation::Bool = true)
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
  @hassert :Lattice 1 TL * change_base_ring(FlintZZ, GL) * TL' * dL == GLlll *cL
  GMlll, TM = lll_gram_with_transform(GMint)
  @hassert :Lattice 1 TM * change_base_ring(FlintZZ, GM) * TM' * dM == GMlll *cM

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
      @hassert :Lattice 1 T * gram_matrix(M) * T' == gram_matrix(L)
      return true, T
    else
      V = ambient_space(L)
      W = ambient_space(L)
      if rank(L) == rank(V)
        T = inv(basis_matrix(L)) * T * basis_matrix(M)
      else
        (!isregular(V) || !isregular(W)) &&
          throw(error(
            """Can compute ambient representation only if ambient space is
               regular"""))
          (rank(V) != rank(W)) &&
          throw(error(
            """Can compute ambient representation only if ambient spaces
            have the same dimension."""))

        CV = orthogonal_complement(V, basis_matrix(L))
        CV = vcat(basis_matrix(L), CV)
        CW = orthogonal_complement(V, basis_matrix(M))
        CW = vcat(basis_matrix(M), CW)
        D = identity_matrix(FlintQQ, rank(V) - rank(L))
        T = inv(CV) * diagonal_matrix(T, D) * CW
      end
        @hassert :Lattice 1 T * gram_matrix(ambient_space(M))  * T' ==
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

function issublattice(M::ZLat, N::ZLat)
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
    issublattice_with_relations(M::ZLat, N::ZLat) -> Bool, fmpq_mat

Returns whether $N$ is a sublattice of $N$. In this case, the second return
value is a matrix $B$ such that $B B_M = B_N$, where $B_M$ and $B_N$ are the
basis matrices of $M$ and $N$ respectively.
"""
function issublattice_with_relations(M::ZLat, N::ZLat)
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

Return the root lattice of type `R` with parameter `n`. At the moment only
type `:A` is supported.
"""
function root_lattice(R::Symbol, n::Int)
  if R === :A
    return Zlattice(gram = _root_lattice_A(n))
  else
    error("Type (:$R) must be :A")
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

################################################################################
#
#  Dual lattice
#
################################################################################

# documented in ../Lattices.jl

function dual(L::ZLat)
  G = gram_matrix(ambient_space(L))
  Gi = inv(G)
  new_bmat = transpose(inv(basis_matrix(L)) * Gi)
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
#  Discriminant
#
################################################################################

function discriminant(L::ZLat)
  d = det(gram_matrix(L))
  return d
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
