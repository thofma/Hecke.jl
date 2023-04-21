export maximal_integral_lattice, is_maximal_integral

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, L::HermLat)
  println(io, "Hermitian lattice of rank $(rank(L)) and degree $(degree(L))")
  println(io, "over")
  print(IOContext(io, :compact => true), base_ring(L))
end

################################################################################
#
#  Construction
#
################################################################################

function lattice(V::HermSpace, B::PMat; check::Bool = true)
  E = base_ring(V)
  if check
    @req rank(matrix(B)) == min(nrows(B), ncols(B)) "B must be of full rank"
  end
  @req nf(base_ring(B)) == E "Incompatible arguments: B must be defined over E"
  @req ncols(B) == dim(V) "Incompatible arguments: the number of columns of B must be equal to the dimension of V"
  L = HermLat{typeof(E), typeof(base_field(E)), typeof(gram_matrix(V)), typeof(B), morphism_type(typeof(E))}()
  L.pmat = B
  L.base_algebra = E
  L.involution = involution(V)
  L.space = V
  return L
end

@doc raw"""
    hermitian_lattice(E::NumField, B::PMat; gram = nothing,
				             check::Bool = true) -> HermLat

Given a pseudo-matrix `B` with entries in a number field `E` of degree 2,
return the hermitian lattice spanned by the pseudo-matrix `B` inside the hermitian
space over `E` with Gram matrix `gram`.

If `gram` is not supplied, the Gram matrix of the ambient space will be the
identity matrix over `E` of size the number of columns of `B`.

By default, `B` is checked to be of full rank. This test can be disabled by setting
`check` to false.
"""
function hermitian_lattice(E::NumField, B::PMat; gram = nothing, check::Bool = true)
  @req nf(base_ring(B)) == E "Incompatible arguments: B must be defined over E"
  @req degree(E) == 2 "E must be a quadratic extension"
  if gram === nothing
    V = hermitian_space(E, ncols(B))
  else
    @assert gram isa MatElem
    @req is_square(gram) "gram must be a square matrix"
    @req ncols(B) == nrows(gram) "Incompatible arguments: the number of columns of B must correspond to the size of gram"
    gram = map_entries(E, gram)
    V = hermitian_space(E, gram)
  end
  return lattice(V, B, check = check)
end

@doc raw"""
    hermitian_lattice(E::NumField, basis::MatElem; gram = nothing,
				                    check::Bool = true) -> HermLat

Given a matrix `basis` and a number field `E` of degree 2, return the hermitian lattice
spanned by the rows of `basis` inside the hermitian space over `E` with Gram matrix `gram`.

If `gram` is not supplied, the Gram matrix of the ambient space will be the identity
matrix over `E` of size the number of columns of `basis`.

By default, `basis` is checked to be of full rank. This test can be disabled by setting
`check` to false.
"""
hermitian_lattice(E::NumField, basis::MatElem; gram = nothing, check::Bool = true) = hermitian_lattice(E, pseudo_matrix(basis), gram = gram, check = check)

@doc raw"""
    hermitian_lattice(E::NumField, gens::Vector ; gram = nothing) -> HermLat

Given a list of vectors `gens` and a number field `E` of degree 2, return the hermitian
lattice spanned by the elements of `gens` inside the hermitian space over `E` with
Gram matrix `gram`.

If `gram` is not supplied, the Gram matrix of the ambient space will be the identity
matrix over `E` of size the length of the elements of `gens`.

If `gens` is empty, `gram` must be supplied and the function returns the zero lattice
in the hermitan space over `E` with Gram matrix `gram`.
"""
function hermitian_lattice(E::NumField, gens::Vector; gram = nothing)
  if length(gens) == 0
    @assert gram !== nothing
    pm = pseudo_matrix(matrix(E, 0, nrows(gram), []))
    L = hermitian_lattice(E, pm, gram = gram, check = false)
    return L
  end
  @assert length(gens[1]) > 0
  @req all(v -> length(v) == length(gens[1]), gens) "All vectors in gens must be of the same length"

  if gram === nothing
    V = hermitian_space(E, length(gens[1]))
  else
    @assert gram isa MatElem
    @req is_square(gram) "gram must be a square matrix"
    @req length(gens[1]) == nrows(gram) "Incompatible arguments: the length of the elements of gens must correspond to the size of gram"
    gram = map_entries(E, gram)
    V = hermitian_space(E, gram)
  end
  return lattice(V, gens)
end

@doc raw"""
    hermitian_lattice(E::NumField; gram::MatElem) -> HermLat

Given a matrix `gram` and a number field `E` of degree 2, return the free hermitian
lattice inside the hermitian space over `E` with Gram matrix `gram`.
"""
function hermitian_lattice(E::NumField; gram::MatElem)
  @req is_square(gram) "gram must be a square matrix"
  gram = map_entries(E, gram)
  B = pseudo_matrix(identity_matrix(E, ncols(gram)))
  return hermitian_lattice(E, B, gram = gram, check = false)
end

################################################################################
#
#  Absolute pseudo matrix
#
################################################################################

# Given a lattice for the quadratic extension E/K, return the pseudo matrix
# over Eabs, where Eabs/Q is an absolute field isomorphic to E
function absolute_pseudo_matrix(E::HermLat{S, T, U, V, W}) where {S, T, U, V, W}
  c = get_attribute(E, :absolute_pseudo_matrix)
  if c === nothing
    f = absolute_simple_field(ambient_space(E))[2]
    pm = _translate_pseudo_hnf(pseudo_matrix(E), pseudo_inv(f))
    set_attribute!(E, :absolute_pseudo_matrix => pm)
    return pm::PMat{elem_type(T), fractional_ideal_type(order_type(T))}
  else
    return c::PMat{elem_type(T), fractional_ideal_type(order_type(T))}
  end
end

################################################################################
#
#  Rational span
#
################################################################################

function rational_span(L::HermLat)
  if isdefined(L, :rational_span)
    return L.rational_span
  else
    G = gram_matrix_of_rational_span(L)
    V = hermitian_space(base_field(L), G)
    L.rational_span = V
    return V
  end
end

################################################################################
#
#  Involution
#
################################################################################

involution(L::HermLat) = L.involution

################################################################################
#
#  Hasse invariant
#
################################################################################

function hasse_invariant(L::HermLat, p)
  error("The lattice must be quadratic")
end

################################################################################
#
#  Witt invariant
#
################################################################################

function witt_invariant(L::HermLat, p)
  error("The lattice must be quadratic")
end

################################################################################
#
#  New lattice in same ambient space
#
################################################################################

# Used internally to return a lattice in the same ambient space of L with
# parameter m (that could be a basis matrix, a pseudo matrix, a list of gens
function lattice_in_same_ambient_space(L::HermLat, m::T) where T
  return lattice(ambient_space(L), m)
end

################################################################################
#
#  Norm
#
################################################################################

# TODO: Be careful with the +, ideal_trace gives QQFieldElem and then this must be gcd
function norm(L::HermLat)
  if isdefined(L, :norm)
    return L.norm::fractional_ideal_type(base_ring(base_ring(L)))
  end
  G = gram_matrix_of_rational_span(L)
  v = involution(L)
  K = base_ring(G)
  R = base_ring(L)
  C = coefficient_ideals(L)
  to_sum = sum(G[i, i] * C[i] * v(C[i]) for i in 1:length(C))
  to_sum = to_sum + R * reduce(+, [tr(C[i] * G[i, j] * v(C[j])) for j in 1:length(C) for i in 1:(j-1)], init = ZZ(0)*inv(1*base_ring(R)))
  n = minimum(numerator(to_sum))//denominator(to_sum)
  L.norm = n
  return n
end

################################################################################
#
#  Scale
#
################################################################################

function scale(L::HermLat)
  if isdefined(L, :scale)
    return L.scale::fractional_ideal_type(base_ring(L))
  end
  G = gram_matrix_of_rational_span(L)
  C = coefficient_ideals(L)
  to_sum = [ G[i, j] * C[i] * involution(L)(C[j]) for j in 1:length(C) for i in 1:j ]
  d = length(to_sum)
  for i in 1:d
    push!(to_sum, involution(L)(to_sum[i]))
  end
  s = sum(to_sum)
  L.scale = s
  return s
end

################################################################################
#
#  Rescale
#
################################################################################

function rescale(L::HermLat, a::Union{FieldElem, RationalUnion})
  @req typeof(a) <: RationalUnion || parent(a) === fixed_field(L) "a must be in the fixed field of L"
  if isone(a)
    return L
  end
  K = fixed_field(L)
  b = base_field(L)(K(a))
  gramamb = gram_matrix(ambient_space(L))
  return hermitian_lattice(base_field(L), pseudo_matrix(L),
                           gram = b * gramamb)
end

################################################################################
#
#  Bad primes
#
################################################################################

@doc raw"""
    bad_primes(L::HermLat; discriminant::Bool = false, dyadic::Bool = false)
                                                             -> Vector{NfOrdIdl}

Given a hermitian lattice `L` over $E/K$, return the prime ideals of $\mathcal O_K$
dividing the scale or the volume of `L`.

If `discriminant == true`, the prime ideals dividing the discriminant of
$\mathcal O_E$ are returned.
If `dyadic == true`, the prime ideals dividing $2*\mathcal O_K$ are returned.
"""
function bad_primes(L::HermLat; discriminant::Bool = false, dyadic::Bool = false)
  bp = support(norm(scale(L)))
  union!(bp, support(norm(volume(L))))
  discriminant && union!(bp, support(Hecke.discriminant(base_ring(L))))
  dyadic && union!(bp, support(2*fixed_ring(L)))
  return bp
end

################################################################################
#
#  Dual lattice
#
################################################################################

function dual(L::HermLat)
  G = gram_matrix_of_rational_span(L)
  @req rank(G) == nrows(G) "Lattice must be non-degenerate"
  B = matrix(pseudo_matrix(L))
  C = coefficient_ideals(L)
  Gi = inv(G)
  new_bmat = Gi * B
  new_coeff =  eltype(C)[inv(involution(L)(c)) for c in C]
  pm = pseudo_matrix(new_bmat, new_coeff)
  return lattice(ambient_space(L), pm)
end

################################################################################
#
#  Jordan decomposition
#
################################################################################

function jordan_decomposition(L::HermLat, p)
  R = base_ring(L)
  E = nf(R)
  aut = involution(L)
  even = is_dyadic(p)

  S = local_basis_matrix(L, p)

  D = prime_decomposition(R, p)
  split = length(D) == 2
  ram = D[1][2] == 2
  n = rank(L)

  P = D[1][1]

  if split
    # I need a p-uniformizer
    pi = elem_in_nf(p_uniformizer(P))
    @assert valuation(pi, D[2][1]) == 0
  elseif ram
    pi = elem_in_nf(uniformizer(P))
  else
    pi = base_field(L)(elem_in_nf(uniformizer(p)))
    su = even ? _special_unit(P, p) : one(nf(order(P)))
  end

  oldval = inf
  blocks = Int[]
  exponents = Int[]

  F = gram_matrix(ambient_space(L))

  k = 1
  while k <= n
    G = S * F * transpose(_map(S, aut))
    X = Union{Int, PosInf}[ iszero(G[i, i]) ? inf : valuation(G[i, i], P) for i in k:n]
    m, ii = findmin(X)
    ii = ii + (k - 1)
    pair = (ii, ii)
    for i in k:n
      for j in k:n
        tmp = iszero(G[i, j]) ? inf : valuation(G[i, j], P)
        if tmp < m
          m = tmp
          pair = (i, j)
        end
      end
    end
    if m != oldval
      push!(blocks, k)
      oldval = m
      push!(exponents, m)
    end
    i, j = pair[1], pair[2]
    if (i != j) && !(ram && (even || isodd(m)))
      a = G[i, j]
      if split
        lambda = valuation(pi * a, P) == m ? pi : aut(pi)
      elseif ram
        @assert iseven(m)
        lambda = E(norm(pi)^(div(m ,2)))//a
      else
        lambda = pi^m//a * su
      end
      for l in 1:ncols(S)
        S[i, l] = S[i, l] + aut(lambda) * S[j, l]
      end
      G = S * F * transpose(_map(S, aut))
      @assert valuation(G[i, i], P) == m
      j = i
    end

    if i != j
      @assert i < j
      swap_rows!(S, i, k)
      swap_rows!(S, j, k + 1)
      SF = S * F
      X1 = SF * transpose(_map(view(S, k:k, 1:ncols(S)), aut))
      X2 = SF * transpose(_map(view(S, (k + 1):(k + 1), 1:ncols(S)), aut))
      for l in k+2:n
        den = norm(X2[k, 1]) - X1[k, 1] * X2[k + 1, 1]
        t1 = (X2[l, 1] * X1[k + 1, 1] - X1[l, 1] * X2[k + 1, 1])//den
        t2 = (X1[l, 1] * X2[k, 1] - X2[l, 1] * X1[k, 1])//den

        for o in 1:ncols(S)
          S[l, o] = S[l, o] - (t1 * S[k, o] + t2 * S[k + 1, o])
        end
      end
      k = k + 2
    else
      swap_rows!(S, i, k)
      X1 = S * F * transpose(_map(view(S, k:k, 1:ncols(S)), aut))
      for l in (k + 1):n
        for o in 1:ncols(S)
          S[l, o] = S[l, o] - X1[l, 1]//X1[k, 1] * S[k, o]
        end
      end
      k = k + 1
    end
  end

  if !ram
    G = S * F * transpose(_map(S, aut))
    @assert is_diagonal(G)
  end

  push!(blocks, n + 1)

  matrices = typeof(F)[ sub(S, blocks[i]:(blocks[i+1] - 1), 1:ncols(S)) for i in 1:(length(blocks) - 1)]
  return matrices, typeof(F)[ m * F * transpose(_map(m, aut)) for m in matrices], exponents
end

################################################################################
#
#  Local isometry
#
################################################################################

# base case for order(p) == base_ring(base_ring(L1))
function is_locally_isometric(L1::HermLat, L2::HermLat, p)
  # Test first rational equivalence
  return genus(L1, p) == genus(L2, p)
end

################################################################################
#
#  Maximal integral lattices
#
################################################################################

# Checks whether L is p-maximal integral. If not, a minimal integral
# over-lattice at p is returned
function _ismaximal_integral(L::HermLat, p)
  R = base_ring(L)
  E = nf(R)
  D = prime_decomposition(R, p)
  Q = D[1][1]
  e = valuation(discriminant(R), p)
  if e == 0
    s = one(E)
  else
    s = elem_in_nf(p_uniformizer(D[1][1]))^e
  end
  @assert valuation(s, D[1][1]) == valuation(discriminant(R), p)

  absolute_map = absolute_simple_field(ambient_space(L))[2]

  M = local_basis_matrix(L, p, type = :submodule)
  G = gram_matrix(ambient_space(L), M)
  F, h = residue_field(R, D[1][1])
  hext = extend(h, E)
  sGmodp = map_entries(hext, s * G)
  Vnullity, V = kernel(sGmodp, side = :left)
  if Vnullity == 0
    return true, zero_matrix(E, 0, 0)
  end

  hprim = u -> elem_in_nf((h\u))

  @vprint :GenRep 1 """Enumerating projective points over $F
                       of length $(nrows(V))\n"""

  for x in enumerate_lines(F, nrows(V))
    v = map_entries(hprim, matrix(F, 1, nrows(V), x) * V)::dense_matrix_type(E)
    res = v * M
    resvec = elem_type(E)[res[1, i] for i in 1:ncols(res)]
    t = inner_product(ambient_space(L), resvec, resvec)
    valv = iszero(t) ? inf : valuation(t, Q)
    if valv >= 2
      # I don't want to compute the generators
      genL = generators(L)
      X = Vector{Union{Int, PosInf}}(undef, length(genL))
      for i in 1:length(genL)
        g = genL[i]
        ip = inner_product(ambient_space(L), resvec, g)
        if iszero(ip)
          X[i] = inf
        else
          X[i] = valuation(ip, Q)
        end
      end
      @assert minimum(X) >= 1 - e
      return false, v * M
    end
  end
  return true, zero_matrix(E, 0, 0)
end

# Check if L is maximal integral at p. If not, return either:
# - a minimal integral overlattice at p (minimal = true)
# - a maximal integral overlattice at p (minimal = false).
function _maximal_integral_lattice(L::HermLat, p, minimal = true)
  R = base_ring(L)
  # already maximal?
  if valuation(norm(volume(L)), p) == 0 && !is_ramified(R, p)
    return true, L
  end

  absolute_map = absolute_simple_field(ambient_space(L))[2]

  B, G, S = jordan_decomposition(L, p)
  D = prime_decomposition(R, p)
  P = D[1][1]
  is_max = true
  lS = length(S)

  invP = inv(P)

  if length(D) == 2 # split
    @assert S[end] != 0
    if minimal
      max = 1
      M = pseudo_matrix(B[lS][1, :], fractional_ideal_type(R)[invP])
    else
      max = S[end]
      coeff_ideals = fractional_ideal_type(R)[]
      _matrix = zero_matrix(nf(R), 0, ncols(B[1]))
      for i in 1:length(B)
        if S[i] == 0
          continue
        end
        _matrix = vcat(_matrix, B[i])
        for k in 1:nrows(B[i])
          push!(coeff_ideals, invP^(S[i]))
        end
      end
      M = pseudo_matrix(_matrix, coeff_ideals)
    end
    _new_pmat = _sum_modules_with_map(pseudo_matrix(L), M, absolute_map)
    LLL = invP^(max) * pseudo_matrix(L)
    _new_pmat = _intersect_modules_with_map(_new_pmat, LLL, absolute_map)
    return false, lattice(ambient_space(L), _new_pmat)
  elseif D[1][2] == 1 # The inert case
    if S[end] >= 2
      if minimal
        max = 1
        M = pseudo_matrix(B[lS][1, :], [invP^(div(S[end], 2))])
      else
        max = S[end]
        coeff_ideals = fractional_ideal_type(R)[]
        _matrix = zero_matrix(nf(R), 0, ncols(B[1]))
        for i in 1:length(B)
          if !(S[i] >= 2)
            continue
          end
          _matrix = vcat(_matrix, B[i])
          for k in 1:nrows(B[i])
            push!(coeff_ideals, invP^(div(S[i], 2)))
          end
        end
        M = pseudo_matrix(_matrix, coeff_ideals)
      end
      _new_pmat = _sum_modules_with_map(pseudo_matrix(L), M, absolute_map)
      LLL = invP^(max) * pseudo_matrix(L)
      _new_pmat = _intersect_modules_with_map(_new_pmat, LLL, absolute_map)
      L = lattice(ambient_space(L), _new_pmat)
      if minimal
        return false, L
      end
      B, G, S = jordan_decomposition(L, p)
      is_max = false
    end
    # new we look for zeros of ax^2 + by^2
    kk, h = residue_field(R, P)
    while sum(Int[S[i] * nrows(B[i]) for i in 1:length(B)]) > 1
      k = 0
      for i in 1:(length(S) + 1)
        if S[i] == 1
          k = i
          break
        end
      end
      @assert nrows(B[k]) >= 2
      r = h\rand(kk)
      # The following might throw ...
      while valuation(G[k][1, 1] + G[k][2, 2] * elem_in_nf(norm(r)), P) < 2
        r = h\rand(kk)
      end
      M = pseudo_matrix(B[k][1, :] + elem_in_nf(r) * B[k][2, :], [invP])
      _new_pmat = _sum_modules_with_map(pseudo_matrix(L), M, absolute_map)
      LLL = invP * pseudo_matrix(L)
      _new_pmat = _intersect_modules_with_map(_new_pmat, LLL, absolute_map)
      L = lattice(ambient_space(L), _new_pmat)
      if minimal
        return false, L
      end
      is_max = false
      B, G, S = jordan_decomposition(L, p)
      @assert S[1] >= 0
    end
    return is_max, L
  else # ramified case
    if S[end] >= 2
      if minimal
        max = 1
        M = pseudo_matrix(B[lS][1, :], [invP^(div(S[end], 2))])
      else
        max = S[end]
        coeff_ideals = fractional_ideal_type(R)[]
        _matrix = zero_matrix(nf(R), 0, ncols(B[1]))
        for i in 1:length(B)
          if !(S[i] >= 2)
            continue
          end
          _matrix = vcat(_matrix, B[i])
          for k in 1:nrows(B[i])
            push!(coeff_ideals, invP^(div(S[i], 2)))
          end
        end
        M = pseudo_matrix(_matrix, coeff_ideals)
      end
      _new_pmat = _sum_modules_with_map(pseudo_matrix(L), M, absolute_map)
      LLL = invP^(max) * pseudo_matrix(L)
      _new_pmat = _intersect_modules_with_map(_new_pmat, LLL, absolute_map)
      L = lattice(ambient_space(L), _new_pmat)
      if minimal
        return false, L
      end
      B, G, S = jordan_decomposition(L, p)
    end
    v = valuation(volume(L), P)
    ok, x = _ismaximal_integral(L, p)
    while !ok
      LL = L
      LLL = pseudo_matrix(x, fractional_ideal_type(R)[invP])
      LpLLL = _sum_modules_with_map(pseudo_matrix(L), LLL, absolute_map)
      L = lattice(ambient_space(L), LpLLL)
      v = v - 2
      @assert v == valuation(volume(L), P)
      @assert valuation(norm(L), p) >= 0
      if minimal
        return false, L
      end
      is_max = false
      ok, x = _ismaximal_integral(L, p)
    end
    @assert iseven(v)
    v = div(v, 2)
    m = rank(L)
    e = valuation(discriminant(R), p)
    if isodd(m)
      valmax = - div(m - 1, 2) * e
    else
      valmax = -div(m, 2) * e
      disc = discriminant(ambient_space(L))
      if !is_local_norm(nf(R), disc, p)
        valmax += 1
      end
    end
    @assert v == valmax
    return is_max, L
  end
end

function is_maximal_integral(L::HermLat, p)
  valuation(norm(L), p) < 0 && return false, L
  return _maximal_integral_lattice(L, p, true)
end

function is_maximal_integral(L::HermLat)
  !is_integral(norm(L)) && error("The lattice is not integral")
  S = base_ring(L)
  f = factor(discriminant(S))
  ff = factor(norm(volume(L)))
  for (p, e) in ff
    f[p] = 0
  end
  bad = collect(keys(f))
  for p in bad
    ok, LL = _maximal_integral_lattice(L, p, true)
    if !ok
      return false, LL
    end
  end
  return true, L
end

function is_maximal(L::HermLat, p)
  #iszero(L) && error("The lattice must be non-zero")
  v = valuation(norm(L), p)
  x = elem_in_nf(p_uniformizer(p))^(-v)
  b, LL = is_maximal_integral(rescale(L, x), p)
  if b
    return b, L
  else
    return false, lattice(ambient_space(L), pseudo_matrix(LL))
  end
end

function maximal_integral_lattice(L::HermLat)
  !is_integral(norm(L)) && error("The lattice is not integral")
  S = base_ring(L)
  f = factor(discriminant(S))
  ff = factor(norm(volume(L)))
  for (p, e) in ff
    f[p] = 0
  end
  bad = collect(keys(f))
  for p in bad
    _, L = _maximal_integral_lattice(L, p, false)
  end
  return L
end

function maximal_integral_lattice(L::HermLat, p)
  valuation(norm(L), p) < 0 && error("Lattice is not locally integral")
  _, L = _maximal_integral_lattice(L, p, false)
  return L
end

function maximal_integral_lattice(V::HermSpace)
  L = lattice(V, identity_matrix(base_ring(V), rank(V)))
  fac = collect(factor(scale(L)))
  S = base_ring(L)
  s = one(nf(S)) * S
  while length(fac) > 0
    nrm = norm(fac[1][1])
    i = findfirst(i -> norm(fac[i][1]) == nrm, 2:length(fac))
    if i !== nothing
      i = i + 1 # findfirst gives the index and not the element
      @assert fac[i][2] == fac[1][2]
      s = s * fractional_ideal(S, fac[1][1])^fac[1][2]
      deleteat!(fac, i)
    else
      s = s * inv(fac[1][1])^(div(fac[1][2], 2))
    end
    deleteat!(fac, 1)
  end
  if !isone(s)
    L = s * L
  end
  return maximal_integral_lattice(L)
end

