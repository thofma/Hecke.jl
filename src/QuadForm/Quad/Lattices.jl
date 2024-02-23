################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, ::MIME"text/plain", L::QuadLat)
  io = pretty(io)
  println(io, "Quadratic lattice of rank $(rank(L)) and degree $(degree(L))")
  print(io, Indent(), "over ", Lowercase())
  Base.show(io, MIME"text/plain"(), base_ring(L))
  print(io, Dedent())
end

function Base.show(io::IO, L::QuadLat)
  if get(io, :supercompact, false)
    print(io, "Quadratic lattice")
  else
    print(io, "Quadratic lattice of rank $(rank(L)) and degree $(degree(L))")
  end
end

################################################################################
#
#  Construction
#
################################################################################

function lattice(V::QuadSpace, B::PMat; check::Bool = true)
  K = base_ring(V)
  if check
    @req rank(matrix(B)) == min(nrows(B), ncols(B)) "B must be of full rank"
  end
  @req nf(base_ring(B)) == K "Incompatible arguments: B must be defined over K"
  @req ncols(B) == dim(V) "Incompatible arguments: the number of columns of B must be equal to the dimension of V"
  L = QuadLat{typeof(K), typeof(gram_matrix(V)), typeof(B)}()
  L.pmat = B
  L.base_algebra = K
  L.space = V
  return L
end

# TODO: At the moment I assume that B is a pseudo-hnf (probably)
@doc raw"""
    quadratic_lattice(K::Field, B::PMat ; gram = nothing,
                                          check:::Bool = true) -> QuadLat

Given a pseudo-matrix `B` with entries in a field `K` return the quadratic
lattice spanned by the pseudo-matrix `B` inside the quadratic space over `K` with
Gram matrix `gram`.

If `gram` is not supplied, the Gram matrix of the ambient space will be the identity
matrix over `K` of size the number of columns of `B`.

By default, `B` is checked to be of full rank. This test can be disabled by setting
`check` to false.
"""
function quadratic_lattice(K::Field, B::PMat ; gram = nothing, check::Bool = true)
  @req nf(base_ring(B)) == K "Incompatible arguments: B must be defined over K"
  @req (K isa NumField || K isa QQField) "K must be a number field"
  if gram === nothing
    V = quadratic_space(K, ncols(B))
  else
    @assert gram isa MatElem
    @req is_square(gram) "gram must be a square matrix"
    @req ncols(B) == nrows(gram) "Incompatible arguments: the number of columns of B must correspond to the size of gram"
    gram = map_entries(K, gram)
    V = quadratic_space(K, gram; check)
  end
  return lattice(V, B; check)
end

@doc raw"""
    quadratic_lattice(K::Field, basis::MatElem ; gram = nothing,
                                                 check::Bool = true)
                                                          -> Union{ZZLat, QuadLat}

Given a matrix `basis` and a field `K`, return the quadratic lattice spanned
by the rows of `basis` inside the quadratic space over `K` with Gram matrix `gram`.

If `gram` is not supplied, the Gram matrix of the ambient space will be the identity
matrix over `K` of size the number of columns of `basis`.

By default, `basis` is checked to be of full rank. This test can be disabled by setting
`check` to false.

If $K = \mathbb{Q}$, then the output lattice is of type `ZZLat`, seen as a lattice
over the ring $\mathbb{Z}$.
"""
quadratic_lattice(K::Field, basis::MatElem ; gram = nothing, check::Bool = true) = quadratic_lattice(K, pseudo_matrix(basis); gram, check)

@doc raw"""
    quadratic_lattice(K::Field, gens::Vector ; gram = nothing) -> Union{ZZLat, QuadLat}

Given a list of vectors `gens` and a field `K`, return the quadratic lattice
spanned by the elements of `gens` inside the quadratic space over `K` with
Gram matrix `gram`.

If `gram` is not supplied, the Gram matrix of the ambient space will be the identity
matrix over `K` of size the length of the elements of `gens`.

If `gens` is empty, `gram` must be supplied and the function returns the zero lattice
in the quadratic space over `K` with gram matrix `gram`.

If $K = \mathbb{Q}$, then the output lattice is of type `ZZLat`, seen as a lattice
over the ring $\mathbb{Z}$.
"""
function quadratic_lattice(K::Field, gens::Vector; gram = nothing, check::Bool = true)
  if length(gens) == 0
    @assert gram !== nothing
    pm = pseudo_matrix(matrix(K, 0, nrows(gram), []))
    L = quadratic_lattice(K, pm; gram)
    return L
  end
  @assert length(gens[1]) > 0
  @req all(v -> length(v) == length(gens[1]), gens) "All vectors in gens must be of the same length"

  if gram === nothing
    V = quadratic_space(K, length(gens[1]))
  else
    @assert gram isa MatElem
    @req is_square(gram) "gram must be a square matrix"
    @req length(gens[1]) == nrows(gram) "Incompatible arguments: the length of the elements of gens must correspond to the size of gram"
    gram = map_entries(K, gram)
    V = quadratic_space(K, gram; check)
  end
  return lattice(V, gens)
end

@doc raw"""
    quadratic_lattice(K::Field ; gram::MatElem) -> Union{ZZLat, QuadLat}

Given a matrix `gram` and a field `K`, return the free quadratic
lattice inside the quadratic space over `K` with Gram matrix `gram`.

If $K = \mathbb{Q}$, then the output lattice is of type `ZZLat`, seen as a lattice
over the ring $\mathbb{Z}$.
"""
function quadratic_lattice(K::Field ; gram::MatElem, check::Bool = true)
  @req is_square(gram) "gram must be a square matrix"
  gram = map_entries(K, gram)
  B = pseudo_matrix(identity_matrix(K, ncols(gram)))
  return quadratic_lattice(K, B; gram, check)
end

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

function witt_invariant(L::QuadLat, p::Union{AbsNumFieldOrderIdeal, InfPlc})
  return witt_invariant(rational_span(L), p)
end

################################################################################
#
#  New lattice in same ambient space
#
################################################################################

function lattice_in_same_ambient_space(L::QuadLat, m::PMat)
  return lattice(ambient_space(L), m)
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
  n = sum(G[i, i] * C[i]^2 for i in 1:length(C); init = fractional_ideal(base_ring(L), zero(base_field(L)))) + K(2) * scale(L)
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
  s = sum(G[i, j] * C[i] * involution(L)(C[j]) for j in 1:length(C) for i in 1:j;
          init = fractional_ideal(base_ring(L), zero(base_field(L))))
  L.scale = s
  return s
end

################################################################################
#
#  Rescale
#
################################################################################

@doc raw"""
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
  return quadratic_lattice(base_field(L), pseudo_matrix(L); gram = b * gramamb)
end

################################################################################
#
#  Bad primes
#
################################################################################

@doc raw"""
    bad_primes(L::QuadLat; even = false) -> Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}

Return the prime ideals dividing the scale and volume of $L$. If `even == true`
also the prime ideals dividing $2$ are included.
"""
function bad_primes(L::QuadLat; even::Bool = false)
  bp = get_attribute!(L, :bad_primes) do
    Dict{Bool, Vector{ideal_type(base_ring(L))}}()
  end::Dict{Bool, Vector{ideal_type(base_ring(L))}}

  get!(bp, even) do
    return _bad_primes(L; even)
  end::Vector{ideal_type(base_ring(L))}
end

function _bad_primes(L::QuadLat; even::Bool = false)
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
  G = gram_matrix_of_rational_span(L)
  B = matrix(pseudo_matrix(L))
  @req rank(G) == nrows(G) "Lattice must be non-degenerate"
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

function jordan_decomposition(L::Union{ZZLat, QuadLat}, p)
  F = gram_matrix(ambient_space(L))
  even = is_dyadic(p)
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
      v = vd - 2 * Int(fdiv(ZZRingElem(qd), 2)) + e * (1 - n)
      if iseven(vd) && qd == vd + e && witt_invariant(L, p) == -1
        v = -e*n + 2
      end
    end
  end
  return v
end

function is_maximal_integral(L::QuadLat, p)
  @req order(p) == base_ring(L) "The ideal does not belong to the base ring of the lattice"
  #if iszero(L)
  #  return true, L
  #end

  if valuation(norm(L), p) < 0
    # this is a weird case? Magma does not return a second argument
    # not integral
    return false, L
  end

  # o-maximal lattices are classified
  # see Kirschmer Lemma 3.5.3
  if guess_max_det(L, p) == valuation(volume(L), p)
    return true, L
  end

  R = base_ring(L)
  K = nf(R)

  k, h = residue_field(R, p)
  hext = extend(h, K)

  BM = local_basis_matrix(L, p; type = :submodule)

  G = 2 * gram_matrix(ambient_space(L), BM)

  Gmodp = map(hext, G)

  V = kernel(Gmodp, side = :left)
  @assert nrows(V) > 0
  local v::dense_matrix_type(K)
  if !is_dyadic(p)
    T = map(y -> hext\y, V)
    H = inv(elem_in_nf(uniformizer(p))) * T * G * transpose(T)
    Hmod = map_entries(hext, H)
    ok, __v = _isisotropic_with_vector_finite(Hmod)
    @assert ok
    _v = matrix(k, 1, length(__v), __v)
    e = map_entries(x -> hext\x, _v * V)
    sp = only(e * G * transpose(e))
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
      _z = only(v * G * transpose(v))
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

function is_maximal_integral(L::QuadLat)
  #if iszero(L)
  #  return true, L
  #end

  if !is_integral(norm(L))
    # is L a minimal integral over-lattice? I don't think so
    return false, L
  end

  for p in bad_primes(L; even = true)
    ok, LL = is_maximal_integral(L, p)
    if !ok
      return false, LL
    end
  end
  return true, L
end

function maximal_integral_lattice(L::QuadLat, p)
  @req base_ring(L) == order(p) "The ideal does not belong to the base ring of the lattice"
  @req valuation(norm(L), p) >= 0 "The norm of the lattice is not locally integral"

  ok, LL = is_maximal_integral(L, p)
  while !ok
    L = LL
    ok, LL = is_maximal_integral(L, p)
  end
  return L
end

function is_maximal(L::QuadLat, p)
  @req order(p) == base_ring(L) "The ideal does not belong to the base ring of the lattice"
  @req valuation(norm(L), p) >= 0 "The norm of the lattice is not locally integral"
  #if iszero(L)
  #  return true, L
  #end
  v = valuation(norm(L), p)
  x = elem_in_nf(uniformizer(p))^(-v)
  ok, LL = is_maximal_integral(rescale(L, x), p)
  if ok
    return true, L
  else
    return false, rescale(LL, inv(elem_in_nf(x)))
  end
end

function maximal_integral_lattice(V::QuadSpace)
  K = base_ring(V)
  L = lattice(V, identity_matrix(K, rank(V)))
  n = norm(L)
  R = order(n)
  if !isone(norm(n))
    fa = factor(n)
    d = prod(fractional_ideal(R, p)^(fld(e, 2)) for (p, e) in fa)
    # fld = fdiv = floored division
    L = lattice(V, _module_scale_ideal(inv(d), pseudo_matrix(L)))
    n = norm(L)
    @assert is_integral(n)
  end

  return maximal_integral_lattice(L)
end

function maximal_integral_lattice(L::QuadLat)
  @req is_integral(norm(L)) "The norm of the lattice is not integral"
  for p in bad_primes(L; even = true)
    L = maximal_integral_lattice(L, p)
  end
  return L
end

