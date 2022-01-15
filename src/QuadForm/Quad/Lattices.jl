################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, L::QuadLat)
  println(io, "Quadratic lattice of rank $(rank(L)) and degree $(degree(L))")
  println(io, "over")
  print(IOContext(io, :compact => true), base_ring(L))
end

################################################################################
#
#  Construction
#
################################################################################

@doc Markdown.doc"""
    quadratic_lattice(K::NumField, B::PMat; gram_ambient_space = F) -> QuadLat

Given a number field $K$ and a pseudo-matrix $B$, returns the quadratic lattice
spanned by the pseudo-matrix $B$ inside the quadratic space over $K$ with gram
matrix $F$.

If $F$ is not supplied, the gram matrix of the ambient space will be the
identity matrix.
"""
quadratic_lattice(::NumField, ::PMat; gram_ambient_space = nothing)

# TODO: At the moment I assume that B is a pseudo-hnf (probably)
function quadratic_lattice(K::NumField, B::PMat; gram_ambient_space = nothing, gram = nothing)
  if gram_ambient_space === nothing && gram === nothing
    return QuadLat(K, identity_matrix(K, nrows(B)), B)
  end
  if gram_ambient_space !== nothing && gram === nothing
    return QuadLat(K, gram_ambient_space, B)
  end
  if gram_ambient_space === nothing && gram !== nothing
    z = QuadLat{typeof(K), typeof(gram), typeof(B)}()
    z.pmat = B
    z.gram = gram
    z.base_algebra = K
    return z
  end
end

@doc Markdown.doc"""
    quadratic_lattice(K::NumField, B::MatElem; gram_ambient_space = F) -> QuadLat

Given a number field $K$ and a matrix $B$, returns the quadratic lattice
spanned by the rows of $B$ inside the quadratic space over $K$ with gram matrix
$F$.

If $F$ is not supplied, the gram matrix of the ambient space will be the
identity matrix.
"""
quadratic_lattice(::NumField, ::MatElem; gram_ambient_space = nothing)

function quadratic_lattice(K::NumField, B::MatElem; gram_ambient_space = nothing, gram = nothing)
  if gram_ambient_space === nothing && gram === nothing
    return QuadLat(K, identity_matrix(K, nrows(B)), pseudo_matrix(B))
  end
  if gram_ambient_space !== nothing && gram === nothing
    return QuadLat(K, gram_ambient_space, pseudo_matrix(B))
  end
  if gram_ambient_space === nothing && gram !== nothing
    P = pseudo_matrix(B)
    z = QuadLat{typeof(K), typeof(B), typeof(P)}()
    z.pmat = P
    z.gram = gram
    z.base_algebra = K
    return z
  end
end

function quadratic_lattice(K::NumField; generators::Vector = Vector{elem_type(K)}[], gram_ambient_space)
  if length(generators) == 0
    pm = pseudo_matrix(identity_matrix(K, nrows(gram_ambient_space)))
  else
    z = zero_matrix(K, length(generators), ncols(gram_ambient_space))
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
  L = quadratic_lattice(K, pm, gram_ambient_space = gram_ambient_space)
  L.generators = Vector{elem_type(K)}[map(K, v) for v in generators]
  return L
end


@doc Markdown.doc"""
    lattice(V::QuadSpace, B::PMat) -> QuadLat

Given a quadratic space $V$ and a pseudo-matrix $B$, returns the quadratic lattice
spanned by the pseudo-matrix $B$ inside $V$.
"""
function lattice(V::QuadSpace, B::PMat)
  K = base_ring(V)
  z = QuadLat{typeof(K), typeof(gram_matrix(V)), typeof(B)}()
  z.pmat = B
  z.gram = gram_matrix(V, matrix(B))
  z.base_algebra = K
  z.space = V
  return z
end

@doc Markdown.doc"""
    lattice(V::QuadSpace, B::MatElem) -> QuadLat

Given a quadratic space $V$ and a matrix $B$, returns the quadratic lattice
spanned by the rows of $B$ inside $V$.
"""
function lattice(V::QuadSpace, B::MatElem)
  K = base_ring(V)
  pmat = pseudo_matrix(B)
  z = QuadLat{typeof(K), typeof(gram_matrix(V)), typeof(pmat)}()
  z.pmat = pmat
  z.gram = gram_matrix(V, B)
  z.base_algebra = K
  z.space = V
  return z
end

@doc Markdown.doc"""
    lattice(V::QuadSpace) -> QuadLat

Given a quadratic space $V$, returns the quadratic lattice with trivial basis
matrix.
"""
lattice(V::QuadSpace) = lattice(V, identity_matrix(base_ring(V), rank(V)))

################################################################################
#
#  Rational span
#
################################################################################

# docstring in ../Lattices.jl

function rational_span(L::QuadLat)
  if isdefined(L, :rational_span)
    return L.rational_span
  else
    G = gram_matrix_of_rational_span(L)
    V = quadratic_space(base_field(L), G)
    L.rational_span = V
    return V
  end
end

################################################################################
#
#  Involution
#
################################################################################

# docstring in ../Lattices.jl

involution(L::QuadLat) = identity

################################################################################
#
#  Hasse invariant
#
################################################################################

function hasse_invariant(L::QuadLat, p)
  return hasse_invariant(rational_span(L), p)
end

################################################################################
#
#  Witt invariant
#
################################################################################

function witt_invariant(L::QuadLat, p::Union{NfAbsOrdIdl, InfPlc})
  return witt_invariant(rational_span(L), p)
end

################################################################################
#
#  New lattice in same ambient space
#
################################################################################

function lattice_in_same_ambient_space(L::QuadLat, m::PMat)
  return lattice(ambient_space(L),m)
end

################################################################################
#
#  Norm
#
################################################################################

function norm(L::QuadLat)
  if isdefined(L, :norm)
    return L.norm::fractional_ideal_type(base_ring(L))
  end
  G = gram_matrix_of_rational_span(L)
  C = coefficient_ideals(L)
  K = nf(order(C[1]))
  n = sum(G[i, i] * C[i]^2 for i in 1:length(C)) + K(2) * scale(L)
  L.norm = n
  return n
end

################################################################################
#
#  Scale
#
################################################################################

function scale(L::QuadLat)
  if isdefined(L, :scale)
    return L.scale::fractional_ideal_type(base_ring(L))
  end
  G = gram_matrix_of_rational_span(L)
  C = coefficient_ideals(L)
  to_sum = [ G[i, j] * C[i] * involution(L)(C[j]) for j in 1:length(C) for i in 1:j]
  s = sum(to_sum)
  L.scale = s
  return s
end

################################################################################
#
#  Rescale
#
################################################################################

@doc Markdown.doc"""
    rescale(L::QuadLat, a) -> QuadLat

Rescale the quadratic form `q` of the ambient space to `a \cdot q`
"""
function rescale(L::QuadLat, a)
  if isone(a)
    return L
  end
  K = fixed_field(L)
  b = K(a)
  gramamb = gram_matrix(ambient_space(L))
  return quadratic_lattice(base_field(L), pseudo_matrix(L),
                           gram_ambient_space = b * gramamb)
end

################################################################################
#
#  Bad primes
#
################################################################################

@doc Markdown.doc"""
    bad_primes(L::AbsLat; even = false) -> Vector{NfOrdIdl}

Return the prime ideals dividing the scale and volume of $L$. If `even == true`
also the prime ideals dividing $2$ are included.
"""
function bad_primes(L::QuadLat; even::Bool = false)
  f = factor(scale(L))
  ff = factor(volume(L))
  for (p, e) in ff
    f[p] = 0
  end
  if even
    for p in prime_decomposition(base_ring(L), 2)
      f[p[1]] = 0
    end
  end
  return collect(keys(f))
end

################################################################################
#
#  Dual lattice
#
################################################################################

function dual(L::QuadLat)
  G, B = _gram_schmidt(gram_matrix_of_rational_span(L), involution(L))
  C = coefficient_ideals(L)
  Gi = inv(G)
  new_bmat = Gi * B
  new_coeff = eltype(C)[inv(c) for c in C]
  pm = pseudo_matrix(new_bmat, new_coeff)
  return lattice(ambient_space(L), pm)
end

################################################################################
#
#  Jordan decomposition
#
################################################################################

function jordan_decomposition(L::Union{ZLat, QuadLat}, p)
  F = gram_matrix(ambient_space(L))
  even = isdyadic(p)
  if even
    pi = elem_in_nf(uniformizer(p))
  else
    pi = zero(nf(order(p)))
  end

  oldval = PosInf()
  blocks = Int[]
  exponents = Int[]
  S = local_basis_matrix(L, p)
  n = nrows(S)
  k = 1
  while k <= n
    G = S * F * transpose(S)
    X = Union{Int, PosInf}[ iszero(G[i, i]) ? inf : valuation(G[i, i], p) for i in k:n]
    m, ii = findmin(X)
    ii = ii + (k - 1)
    pair = (ii, ii)

    for i in k:n
      for j in (i + 1):n
        tmp = iszero(G[i, j]) ? inf : valuation(G[i, j], p)
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

    if even && pair[1] != pair[2]
      swap_rows!(S, pair[1], k)
      swap_rows!(S, pair[2], k +1)

      T12 = (sub(S, k:k, 1:ncols(S)) * F * transpose(sub(S, k+1:k+1, 1:ncols(S))))[1, 1]
      for l in 1:ncols(S)
        S[k, l] = S[k, l] * pi^valuation(T12, p)//T12
      end

      T = (i, j) -> (sub(S, i:i, 1:ncols(S)) * F * transpose(sub(S, j:j, 1:ncols(S))))[1, 1]
      T11 = T(k, k)
      T22 = T(k + 1, k + 1)
      T12 = T(k, k + 1)
      d = T11*T22 - T12^2
      for l in (k + 2):n
        tl = T12 * T(k + 1, l) - T22 * T(k, l)
        ul = T12 * T(k, l) - T11 * T(k + 1, l)
        for u in 1:ncols(S)
          S[l, u] = S[l, u] + (tl//d) * S[k, u] + (ul//d) * S[k + 1, u]
        end
      end
      k = k + 2
    else
      if pair[1] == pair[2]
        swap_rows!(S, pair[1], k)
      else
        for u in 1:ncols(S)
          S[pair[1], u] = S[pair[1], u] + S[pair[2], u]
        end
        swap_rows!(S, pair[1], k)
      end
      nrm = (sub(S, k:k, 1:ncols(S)) * F * transpose(sub(S, k:k, 1:ncols(S))))[1, 1]
      XX = sub(S, k:k, 1:ncols(S)) * F * transpose(S)
      for l in k+1:n
        for u in 1:ncols(S)
          S[l, u] = S[l, u] - XX[1,l]//nrm * S[k, u]
        end
      end
      k = k + 1
    end
  end

  push!(blocks, n+1)
  matrices = typeof(F)[ sub(S, blocks[i]:(blocks[i+1] - 1), 1:ncols(S)) for i in 1:(length(blocks) - 1)]
  return matrices, typeof(F)[ m * F * transpose(m) for m in matrices], exponents
end

################################################################################
#
#  Maximal integral lattices
#
################################################################################

function guess_max_det(L::QuadLat, p)
  m = rank(L)
  R = base_ring(L)
  n = div(m, 2)
  d = det(gram_matrix_of_rational_span(L))
  e = 2 * valuation(base_ring(L)(2), p)
  if isodd(m)
    v = mod(valuation(d, p), 2)
    v = witt_invariant(L, p) == 1 ? v - e * n : 2 - v - e * n
  else
    if isodd(div(m * (m - 1), 2))
      d = -d
    end
    qd = quadratic_defect(d, p)
    if qd isa PosInf
      v = witt_invariant(L, p) == 1 ? -e * n : 2 - e * n
    else
      vd = valuation(d, p)
      # I cannot use div(qd, 2), because qd might be negative and I need to round
      # toward 0, e.g., I need div(-3, 2) to be -2 and not -1.
      v = vd - 2 * Int(fdiv(fmpz(qd), 2)) + e * (1 - n)
      if iseven(vd) && qd == vd + e && witt_invariant(L, p) == -1
        v = -e*n + 2
      end
    end
  end
  return v
end

@doc Markdown.doc"""
    ismaximal_integral(L::QuadLat, p) -> Bool, QuadLat

Checks whether L is maximal integral at $p$. If not, the second return value is
a minimal integral overlattice at p.
"""
function ismaximal_integral(L::QuadLat, p)
  @req order(p) == base_ring(L) "blabla do not match"
  #if iszero(L)
  #  return true, L
  #end

  if valuation(norm(L), p) < 0
    # this is a weird case? Magma does not return a second argument
    return false, L
  end

  # don't know what this does
  if guess_max_det(L, p) == valuation(volume(L), p)
    return true, L
  end

  R = base_ring(L)
  K = nf(R)

  k, h = ResidueField(R, p)
  hext = extend(h, K)

  BM = local_basis_matrix(L, p, type = :submodule)

  G = 2 * gram_matrix(ambient_space(L), BM)

  Gmodp = map(hext, G)

  r, V = left_kernel(Gmodp)
  @assert r > 0
  local v::dense_matrix_type(K)
  if !isdyadic(p)
    T = map(y -> hext\y, V)
    H = inv(elem_in_nf(uniformizer(p))) * T * G * transpose(T)
    Hmod = map_entries(hext, H)
    ok, __v = _isisotropic_with_vector_finite(Hmod)
    @assert ok
    _v = matrix(k, 1, length(__v), __v)
    e = map_entries(x -> hext\x, _v * V)
    sp = (e * G * transpose(e))[1, 1]
    valv = iszero(sp) ? inf : valuation(sp, p)
    @assert valv >= 2
    v = e
  else
    val2 = valuation(R(2), p)
    PP = enumerate_lines(k, nrows(V))
    for x in PP
      @assert !iszero(x)
      xV = matrix(k, 1, length(x), x) * V
      e = elem_type(K)[ hext\(xV[1, i]) for i in 1:ncols(xV) ]
      v = matrix(K, 1, length(e), e)
      _z = (v * G * transpose(v))[1, 1]
      # Test if valv >= val2 + 2
      if iszero(_z)
        break
      else
        valv = valuation(_z, p)
        @assert valv >= 1
        if valv >= val2 + 2
          break
        end
      end
    end
  end
  pia = anti_uniformizer(p)
  _LL = _sum_modules(pseudo_matrix(L), pseudo_matrix(pia * v * BM))
  LL = lattice(ambient_space(L), _LL)
  @assert volume(L) ==  volume(LL) * p^2 && valuation(norm(LL), p) >= 0
  return false, LL
end

@doc Markdown.doc"""
    ismaximal_integral(L::QuadLat) -> Bool, QuadLat

Checks whether $L$ is maximal integral. If not, the second return valiue is a
minimal integral overlattice.
"""
function ismaximal_integral(L::QuadLat)
  #if iszero(L)
  #  return true, L
  #end

  if !isintegral(norm(L))
    # is L a minimal integral over-lattice? I don't think so
    return false, L
  end

  for p in bad_primes(L, even = true)
    ok, LL = ismaximal_integral(L, p)
    if !ok
      return false, LL
    end
  end
  return true, L
end

function maximal_integral_lattice(L::QuadLat, p)
  @req base_ring(L) == order(p) "Second argument must be an ideal of the base ring of L"
  @req valuation(norm(L), p) >= 0 "The normal of the lattice must be locally integral"

  ok, LL = ismaximal_integral(L, p)
  while !ok
    L = LL
    ok, LL = ismaximal_integral(L, p)
  end
  return L
end

@doc Markdown.doc"""
    ismaximal_integral(L::QuadLat, p) -> Bool, QuadLat

Checks whether $L$ is maximal at $p$, that is, whether no overlattice has the
same norm. If not, the second return value is a proper overlattice with the
same norm.
"""
function ismaximal(L::QuadLat, p)
  @req order(p) == base_ring(L) "Asdsads"
  #if iszero(L)
  #  return true, L
  #end
  v = valuation(norm(L), p)
  x = elem_in_nf(uniformizer(p))^(-v)
  ok, LL = ismaximal_integral(rescale(L, x), p)
  if ok
    return true, L
  else
    return false, rescale(LL, inv(elem_in_nf(x)))
  end
end

@doc Markdown.doc"""
    maximal_integral_lattice(V::QuadSpace) -> QuadLat

Return a lattice $L$ of $V$ such that the norm of $L$ is integral and $L$ is
maximal with respect to this property.
"""
function maximal_integral_lattice(V::QuadSpace)
  K = base_ring(V)
  L = lattice(V, identity_matrix(K, rank(V)))
  n = norm(L)
  R = order(n)
  if !isone(norm(n))
    fa = factor(n)
    d = prod(typeof(n)[fractional_ideal(R, p)^(fld(e, 2)) for (p, e) in fa])
    # fld = fdiv = floored division
    L = lattice(V, _module_scale_ideal(inv(d), pseudo_matrix(L)))
    n = norm(L)
    @assert isintegral(n)
  end

  return maximal_integral_lattice(L)
end

@doc Markdown.doc"""
    maximal_integral_lattice(L::QuadLat) -> QuadLat

Return a maximal integral lattice containing $L$.
"""
function maximal_integral_lattice(L::QuadLat)
  @req isintegral(norm(L)) "Lattice must be integral"
  for p in bad_primes(L, even = true)
    L = maximal_integral_lattice(L, p)
  end
  return L
end
