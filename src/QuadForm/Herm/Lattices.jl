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

@doc Markdown.doc"""
    hermitian_lattice(K::NumField, B::PMat; gram_ambient_space = F) -> HermLat

Given a number field $K$ and a pseudo-matrix $B$, returns the hermitian lattice
spanned by the pseudo-matrix $B$ inside the hermitian space over $K$ with gram
matrix $F$.

If $F$ is not supplied, the gram matrix of the ambient space will be the
identity matrix.
"""
hermitian_lattice(::NumField, ::PMat; gram_ambient_space = nothing)

function hermitian_lattice(K::NumField, B::PMat; gram_ambient_space = nothing, gram = nothing)
  if gram_ambient_space === nothing && gram === nothing
    return HermLat(K, identity_matrix(K, nrows(B)), B)
  end
  if gram_ambient_space !== nothing && gram === nothing
    return HermLat(K, gram_ambient_space, B)
  end
  if gram_ambient_space === nothing && gram !== nothing
    @assert degree(K) == 2
    A = automorphisms(K)
    a = gen(K)
    if A[1](a) == a
      involution = A[2]
    else
      involution = A[1]
    end

    z = HermLat{typeof(K), typeof(base_field(K)), typeof(gram), typeof(B), morphism_type(typeof(K))}()
    z.pmat = P
    z.gram = gram
    z.involution = involution
    z.base_algebra = K
    return z
  end
end

@doc Markdown.doc"""
    hermitian_lattice(K::NumField, B::MatElem; gram_ambient_space = F) -> HermLat

Given a number field $K$ and a matrix $B$, returns the hermitian lattice
spanned by the rows of $B$ inside the hermitian space over $K$ with gram matrix
$F$.

If $F$ is not supplied, the gram matrix of the ambient space will be the
identity matrix.
"""
hermitian_lattice(::NumField, ::MatElem; gram_ambient_space = nothing)

function hermitian_lattice(K::NumField, B::MatElem; gram_ambient_space = nothing, gram = nothing)
  if gram_ambient_space === nothing && gram === nothing
    return HermLat(K, identity_matrix(K, nrows(B)), pseudo_matrix(B))
  end
  if gram_ambient_space !== nothing && gram === nothing
    return HermLat(K, gram_ambient_space, pseudo_matrix(B))
  end
  if gram_ambient_space === nothing && gram !== nothing
    @assert degree(K) == 2
    A = automorphisms(K)
    a = gen(K)
    if A[1](a) == a
      involution = A[2]
    else
      involution = A[1]
    end

    P = pseudo_matrix(B)
    z = HermLat{typeof(K), typeof(base_field(K)), typeof(B), typeof(P), morphism_type(typeof(K))}()
    z.pmat = P
    z.gram = gram
    z.involution = involution
    z.base_algebra = K
    return z
  end
end

function hermitian_lattice(E::NumField; generators::Vector = Vector{elem_type(E)}[], gram_ambient_space)
  if length(generators) == 0
    pm = pseudo_matrix(identity_matrix(E, nrows(gram_ambient_space)))
  else
    z = zero_matrix(E, length(generators), ncols(gram_ambient_space))
    for i in 1:length(generators)
      for j in 1:ncols(gram_ambient_space)
        z[i, j] = generators[i][j]
      end
    end
    pm = pseudo_hnf(pseudo_matrix(z), :lowerleft)
    i = 1
    while iszero_row(pm.matrix, i)
      i += 1
    end
    pm = sub(pm, i:nrows(pm), 1:ncols(pm))
  end
  L = hermitian_lattice(E, pm, gram_ambient_space = gram_ambient_space)
  L.generators = Vector{elem_type(E)}[map(E, v) for v in generators]
  return L
end

@doc Markdown.doc"""
    lattice(V::HermSpace, B::PMat) -> HermLat

Given a hermitian space $V$ and a pseudo-matrix $B$, returns the hermitian lattice
spanned by the pseudo-matrix $B$ inside $V$.
"""
function lattice(V::HermSpace, B::PMat)
  K = base_ring(V)
  gram = gram_matrix(V, matrix(B))
  z = HermLat{typeof(K), typeof(base_field(K)), typeof(gram), typeof(B), morphism_type(typeof(K))}()
  z.pmat = B
  z.gram = gram
  z.base_algebra = base_ring(V)
  z.involution = involution(V)
  z.space = V
  return z
end

@doc Markdown.doc"""
    lattice(V::HermSpace, B::MatElem) -> HermLat

Given a Hermitian space $V$ and a matrix $B$, returns the Hermitian lattice
spanned by the rows of $B$ inside $V$.
"""
function lattice(V::HermSpace, B::MatElem)
  K = base_ring(V)
  gram = gram_matrix(V, B)
  pmat = pseudo_matrix(B)
  z = HermLat{typeof(K), typeof(base_field(K)), typeof(gram), typeof(pmat), morphism_type(typeof(K))}()
  z.pmat = pmat
  z.gram = gram
  z.base_algebra = base_ring(V)
  z.involution = involution(V)
  z.space = V
  return z
end

@doc Markdown.doc"""
    lattice(V::HermSpace) -> HermLat

Given a Hermitian space $V$, returns the Hermitian lattice with trivial basis
matrix.
"""
lattice(V::HermSpace) = lattice(V, identity_matrix(base_ring(V), rank(V)))

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

# docstring in ../Lattices.jl

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

function lattice_in_same_ambient_space(L::HermLat, m::T) where T
  return hermitian_lattice(base_field(L), m,
                           gram_ambient_space = gram_matrix(ambient_space(L)))
end

################################################################################
#
#  Norm
#
################################################################################

# TODO: Be careful with the +, ideal_trace gives fmpq and then this must be gcd
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
  to_sum = to_sum + R * reduce(+, [tr(C[i] * G[i, j] * v(C[j])) for j in 1:length(C) for i in 1:(j-1)])
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

function rescale(L::HermLat, a)
  if isone(a)
    return L
  end
  K = fixed_field(L)
  b = base_field(L)(K(a))
  gramamb = gram_matrix(ambient_space(L))
  return hermitian_lattice(base_field(L), pseudo_matrix(L),
                           gram_ambient_space = b * gramamb)
end

################################################################################
#
#  Bad primes
#
################################################################################

@doc Markdown.doc"""
    bad_primes(L::HermLat; discriminant = false) -> Vector{NfOrdIdl}

Returns the prime ideals dividing the scale and volume of $L$. If
`discriminant == true`, also the prime ideals dividing the discriminant of the
base ring of $L$ are included.
"""
function bad_primes(L::HermLat; discriminant::Bool = false)
  s = scale(L)
  f = factor(norm(scale(L)))
  ff = factor(norm(volume(L)))
  for (p, e) in ff
    f[p] = 0
  end
  if discriminant
    for (p, ) in factor(Hecke.discriminant(base_ring(L)))
      f[p] = 0
    end
  end
  return collect(keys(f))
end

################################################################################
#
#  Dual lattice
#
################################################################################

function dual(L::HermLat)
  G, B = _gram_schmidt(gram_matrix_of_rational_span(L), involution(L))
  C = coefficient_ideals(L)
  Gi = inv(G)
  new_bmat = Gi * B
  new_coeff =  eltype(C)[inv(induce_image(c, involution(L))) for c in C]
  pm = pseudo_matrix(new_bmat, new_coeff)
  return hermitian_lattice(base_field(L), pm,
                           gram_ambient_space = gram_matrix(ambient_space(L)))
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
  even = isdyadic(p)

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
    @assert isdiagonal(G)
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
function islocally_isometric(L1::HermLat, L2::HermLat, p)
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
  F, h = ResidueField(R, D[1][1])
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
  if valuation(norm(volume(L)), p) == 0 && !isramified(R, p)
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
        M = pseudo_matrix(B[lS][1, :], invP^(div(S[end], 2)))
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
    kk, h = ResidueField(R, P)
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
      if !islocal_norm(nf(R), disc, p)
        valmax += 1
      end
    end
    @assert v == valmax
    return is_max, L
  end
end

@doc Markdown.doc"""
    ismaximal_integral(L::HermLat, p) -> Bool, HermLat

Checks whether $L$ is maximal integral at $p$. In case it is not, the second
return value is a minimal integral overlattice at $p$.
"""
function ismaximal_integral(L::HermLat, p)
  @req valuation(norm(L), p) >= 0 "The lattice must be integral at the prime"
  return _maximal_integral_lattice(L, p, true)
end

@doc Markdown.doc"""
    ismaximal_integral(L::HermLat) -> Bool, HermLat

Checks whether $L$ is maximal integral. In case it is not, the second return
value is a maximal integral overlattice.
"""
function ismaximal_integral(L::HermLat)
  !isintegral(norm(L)) && throw(error("The lattice is not integral"))
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

@doc Markdown.doc"""
    ismaximal(L::HermLat, p) -> Bool, HermLat

Decide if the norm of $L_p$ is integral and if the lattice is maximal. If the
first condition holds but the second does not, then a proper overlattice with
integral norm is also returned.
"""
function ismaximal(L::HermLat, p)
  #iszero(L) && error("The lattice must be non-zero")
  v = valuation(norm(L), p)
  x = elem_in_nf(p_uniformizer(p))^(-v)
  b, LL = ismaximal_integral(rescale(L, x), p)
  if b
    return b, L
  else
    return false, lattice(ambient_space(L), pseudo_matrix(LL))
  end
end

@doc Markdown.doc"""
    maximal_integral_lattice(L::HermLat) -> HermLat

Returns a maximal integral lattice containing $L$.
"""
function maximal_integral_lattice(L::HermLat)
  !isintegral(norm(L)) && throw(error("The lattice is not integral"))
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

@doc Markdown.doc"""
    maximal_integral_lattice(L::HermLat, p) -> HermLat

Returns a lattice $M$ with $M$ maximal integral at $p$ and which agrees with L
at all places different from $p$.
"""
function maximal_integral_lattice(L::HermLat, p)
  valuation(norm(L), p) < 0 && throw(error("Lattice is not locally integral"))
  _, L = _maximal_integral_lattice(L, p, false)
  return L
end

@doc Markdown.doc"""
    maximal_integral_lattice(V::HermSpace) -> HermLat

Returns a lattice $L$ of $V$ such that the norm of $L$ is integral and $L$ is
maximal with respect to this property.
"""
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
