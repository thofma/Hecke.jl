basis_matrix(L::ZLat) = L.basis_matrix

ambient_space(L::ZLat) = L.space

base_ring(L::ZLat) = FlintZZ

################################################################################
#
#  Creation
#
################################################################################

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

function lattice(V::QuadSpace{FlintRationalField, fmpq_mat}, B::MatElem)
  Gc = change_base_ring(FlintQQ, B)
  if typeof(Gc) !== fmpq_mat
    throw(error("Cannot convert entries of the matrix to the rationals"))
  end
  return ZLat(V, Gc)
end

function gram_matrix(L::ZLat)
  b = basis_matrix(L)
  return b * gram_matrix(ambient_space(L)) * transpose(b)
end

gram_matrix_of_rational_span(L::ZLat) = gram_matrix(L)

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
#  String I/O
#
################################################################################

# if ambient_representation = true, they are given with respect to the ambient space
function Base.show(io::IO, L::ZLat)
  print(io, "Quadratic lattice of rank ", rank(L),
            " and degree ", degree(L), " over the rationals")
end

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
      gens = fmpz_mat[matrix(ZZ, g) for g in _gens]
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
  @hassert all(gens[i] * GL * transpose(gens[i]) == GL for i in 1:length(gens))

  L.automorphism_group_generators = gens
  L.automorphism_group_order = order

  return nothing
end

# natural action = action on ambient_space

@doc Markdown.doc"""
    automorphism_group_generators(L::ZLat; ambient_representation::Bool = true)

Returns generators of the automorphism group of $L$. By default, the
automorphisms are acting on the coordinate vectors of lattice elements.
If `ambient_representation = true`, the automorphisms act on elements in the
ambient space of `L`.
"""
function automorphism_group_generators(L::ZLat; check::Bool = true,
                                                ambient_representation::Bool = true)

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
    if check
      for g in res
        @assert g * gram_matrix(V) * g' == gram_matrix(V)
      end
    end
    return res
  end
end

function automorphism_group_order(L::ZLat)
  assert_has_automorphisms(L)
  return L.automorphism_group_order
end

@doc Markdown.doc"""
    isisometric(L::ZLat, M::ZLat; ambient_representation::Bool = true
                                  check::Bool = true)
        -> (Bool, MatElem)

Tests if $L$ and $M$ are isometric. If this is the case, the second return value
is an isometry $T$ from $L$ to $M$.

By default, that isometry is represented with respect to the bases of the
ambient spaces, that is, $T V_M T^t = V_L$ where $V_L$ and $V_M$ are the gram
matrices of the ambient spaces of $L$ and $M$ respectively. If
`ambient_representation = true`, then the isometry is represented with respect
to the bases of $L$ and $M$, that is, $T G_M T^t = G_L$ where $G_M$ and $G_L$ are
the gram matrices of $L$ and $M$ respectively.
"""
function isisometric(L::ZLat, M::ZLat; ambient_representation::Bool = true,
                                       check::Bool = true)
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
  @assert TL * change_base_ring(FlintZZ, GL) * TL' * dL == GLlll * cL
  GMlll, TM = lll_gram_with_transform(GMint)
  @assert TM * change_base_ring(FlintZZ, GM) * TM' * dM == GMlll * cM

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
      if check
        @assert T * gram_matrix(M) * T' == gram_matrix(L)
      end
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
      if check
        @assert T * gram_matrix(ambient_space(M))  * T' ==
                  gram_matrix(ambient_space(L))
      end
      return true, T
    end
  else
    return false, zero_matrix(FlintQQ, 0, 0)
  end
end

################################################################################
#
#  Root lattice
#
################################################################################

@doc Markdown.doc"""
    root_lattice(R::Symbol, n::Int)

Determine the root lattice of type `R` with parameter `n`. At the moment only
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


