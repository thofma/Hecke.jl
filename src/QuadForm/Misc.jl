################################################################################
#
#  Restrict and extend scalars from L^n to Q^(d * n)
#
################################################################################

### Printing functions

function Base.show(io::IO, ::MIME"text/plain", f::VecSpaceRes)
  n = f.domain_dim
  m = f.codomain_dim
  io = pretty(io)
  println(io, "Map of change of scalars")
  println(io, Indent(), "from vector space of dimension ", n, " over ", Lowercase(), QQ)
  print(io, "to vector space of dimension ", m, " over ", Lowercase())
  print(io, f.field)
  print(io, Dedent())
end

function Base.show(io::IO, f::VecSpaceRes)
  if get(io, :supercompact, false)
    print(io, "Map of change of scalars")
  else
    print(io, "Map of change of scalars between vector spaces")
  end
end

function Base.show(io::IO, ::MIME"text/plain", f::AbstractSpaceRes)
  io = pretty(io)
  println(io, "Map of change of scalars")
  println(io, Indent(), "from ", Lowercase(), domain(f))
  print(io, "to ", Lowercase(), codomain(f))
  print(io, Dedent())
end

function Base.show(io::IO, f::AbstractSpaceRes)
 if get(io, :supercompact, false)
    print(io, "Map of change of scalars")
  else
    print(io, "Map of change of scalars between hermitian spaces")
  end
end

### Image functions

(f::VecSpaceRes)(a) = image(f, a)

(f::AbstractSpaceRes)(a) = image(f, a)

function image(f::VecSpaceRes{S, T}, v::Vector) where {S, T}
  if v isa Vector{QQFieldElem}
    vv = v
  else
    vv = map(QQFieldElem, v)::Vector{QQFieldElem}
  end
  return _image(f, vv)
end

function _image(f::VecSpaceRes{S, T}, v::Vector{QQFieldElem}) where {S, T}
  n = f.codomain_dim
  d = f.absolute_degree
  m = f.domain_dim
  B = f.absolute_basis
  @req length(v) == m "Vector must have length $m ($(length(v)))"
  z = Vector{T}(undef, n)
  l = 1
  for i in 1:n
    z[i] = zero(f.field)
    for k in 1:d
      z[i] = z[i] + v[l] * B[k]
      l = l + 1
    end
  end
  return z
end

# f makes f.btop correspond with f.bdown. So for a vector v in
# the domain of f, we get its coordinates in the basis f.btop
# using f.ibtop, we do the exntension of scalars. This gives
# the coordinates in the basis f.bdown of the codomain of f
# which we therefore multiply to f.bdown to get coordinates
# in the standard basis
function image(f::AbstractSpaceRes{S, T}, v::Union{Vector, MatrixElem}) where {S, T}
  E = base_ring(codomain(f))
  ibtop = f.ibtop
  bdown = f.bdown
  n = rank(codomain(f))
  d = absolute_degree(E)
  m = rank(domain(f))
  B = absolute_basis(E)
  if v isa MatElem
    @req size(v) == (1, m) || size(v) == (m, 1) "Matrix should be a column or row vector of length $m ($(size(v)))"
    if ncols(v) == 1
      v = transpose(v)
    end
  else
    @req length(v) == m "Vector must have length $m ($(length(v)))"
  end
  v *= ibtop
  z = Vector{elem_type(E)}(undef, n)
  l = 1
  for i in 1:n
    z[i] = zero(E)
    for k in 1:d
      z[i] = z[i] + v[l] * B[k]
      l = l + 1
    end
  end
  return (z*bdown)::Vector{elem_type(E)}
end

### Preimage functions

Base.:(\)(f::VecSpaceRes, a) = preimage(f, a)

Base.:(\)(f::AbstractSpaceRes, a) = preimage(f, a)

function preimage(f::VecSpaceRes{S, T}, v::Vector) where {S, T}
  if v isa Vector{T}
    vv = v
  else
    vv = map(f.field, v)::Vector{T}
  end
  return _preimage(f, vv)
end

function _preimage(f::VecSpaceRes{S, T}, w::Vector{T}) where {S, T}
  n = f.codomain_dim
  d = f.absolute_degree
  @req length(w) == n "Vector must have length $n ($(length(w)))"
  z = Vector{QQFieldElem}(undef, f.domain_dim)
  k = 1
  for i in 1:n
    y = w[i]
    @assert parent(y) === f.field
    co = absolute_coordinates(y)
    for j in 1:d
      z[k] = co[j]
      k = k + 1
    end
  end
  return z
end

function preimage(f::AbstractSpaceRes{S, T}, v::Vector) where {S, T}
  if v isa Vector{elem_type(base_ring(codomain(f)))}
    vv = v
  else
    vv = map(base_ring(codomain(f)), v)
  end
  return _preimage(f, vv)
end

# f makes f.btop correspond with f.bdown. So for a vector v in
# the codomain of f, we get its coordinates in the basis f.bdown
# using f.ibdown, we do the restrictionn of scalars. This gives
# the coordinates in the basis f.btop of the domain of f
# which we therefore multiply to f.btop to get coordinates
# in the standard basis.
function _preimage(f::AbstractSpaceRes{S, T}, w::Vector) where {S, T}
  K = base_ring(domain(f))
  btop = f.btop
  ibdown = f.ibdown
  n = rank(codomain(f))
  d = absolute_degree(base_ring(codomain(f)))
  @req length(w) == n "Vector must have length $n ($(length(w)))"
  wl = vec(collect(transpose(matrix(w))*ibdown))
  z = Vector{elem_type(K)}(undef, rank(domain(f)))
  k = 1
  for i in 1:n
    y = wl[i]
    @assert parent(y) === base_ring(codomain(f))
    co = absolute_coordinates(y)
    for j in 1:d
      z[k] = co[j]
      k = k + 1
    end
  end
  return vec(collect(matrix(QQ, 1, length(z), z)*btop))::Vector{elem_type(K)}
end

################################################################################
#
#  Kummer generators for local quadratic unramified extensions
#
################################################################################


# Return an element Delta, such that K_p(\sqrt{Delta}) is the unique quadratic unramified extension.

@doc raw"""
    kummer_generator_of_local_unramified_quadratic_extension(p::Idl) -> NumFieldElem

Given a dyadic prime ideal $\mathfrak p$ of a number field $K$, return a local
unit $\Delta$, such that $K(\sqrt(\Delta))$ is unramified at $\mathfrak p$.
"""
function kummer_generator_of_local_unramified_quadratic_extension(p)
  @assert is_dyadic(p)
  K = nf(order(p))
  k, h = residue_field(order(p), p)
  kt, t = polynomial_ring(k, "t", cached = false)
  a = rand(k)
  f = t^2 - t + a
  while !is_irreducible(f)
    a = rand(k)
    f = t^2 - t + a
  end
  Kt, t = polynomial_ring(K, "t", cached = false)
  g = t^2 - t + elem_in_nf(h\a)
  aa = elem_in_nf(h\a)
  gg = evaluate(g, inv(K(2)) * (t + 1))
  @assert iszero(coeff(gg, 1))
  D = -coeff(gg, 0) * 4
  @assert quadratic_defect(D, p) == valuation(4, p)
  DD = -4 * aa + 1
  @assert D == DD
  @assert quadratic_defect(DD, p) == valuation(4, p)
  return DD
end

# {Given a unit at the prime p, find a local unit v in the same square class such that v-1 generates the quadratic defect of u}

function _find_special_class(u, p)
  R = order(p)
  K = nf(R)
  @assert valuation(u, p) == 0
  k, _h = residue_field(R, p)
  h = extend(_h, K)
  fl, s = is_square_with_sqrt(h(u))
  @assert fl
  u = divexact(u, (h\s)^2)
  @assert isone(h(u))
  e = valuation(2, p)
  pi = elem_in_nf(uniformizer(p))
  val = isone(u) ? inf : valuation(u - 1, p)
  while val < 2 * e
    if isodd(val)
      return u
    end
    fl, s = is_square_with_sqrt(h((u - 1)//pi^val))
    @assert fl
    # TODO:FIXME the div is wrong for negative valuations I think
    @assert val >= 0
    u = divexact(u, (1 + (h\s) * pi^(div(val, 2)))^2)
    val = valuation(u - 1, p)
  end
  kt, t = polynomial_ring(k, "t", cached = false)
  return val == 2 * e && is_irreducible(kt([h(divexact(u - 1, 4)), one(k), one(k)])) ? u : one(K)
end

################################################################################
#
#  Should go somewhere else
#
################################################################################

# This can be done more efficiently
function image(f::NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}}, I::AbsNumFieldOrderIdeal, OK)
  return reduce(+, (OK(f(elem_in_nf(b))) * OK for b in basis(I)), init = 0 * OK)
end

function image(f::NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}}, I::AbsNumFieldOrderIdeal)
  OK = maximal_order(codomain(f))
  return image(f, I, OK)
end

function image(f::NumFieldHom{RelSimpleNumField{AbsSimpleNumFieldElem}, RelSimpleNumField{AbsSimpleNumFieldElem}}, I::RelNumFieldOrderIdeal)
  OK = order(I)
  return reduce(+, (OK(f(b)) * OK for b in absolute_basis(I)), init = 0 * OK)
end

function preimage(f::NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}}, I::RelNumFieldOrderIdeal, OK)
  return reduce(+, (OK(f\(b)) * OK for b in absolute_basis(I)), init = 0 * OK)
end

function preimage(f::NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}}, I::RelNumFieldOrderIdeal)
  OK = maximal_order(domain(f))
  return preimage(f, I, OK)
end

function image(S::T, A::AbsSimpleNumFieldOrderFractionalIdeal) where {T <: Hecke.NumFieldHom}
  return S(numerator(A))//denominator(A)
end

function preimage(f::NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}}, I::RelNumFieldOrderFractionalIdeal, OK)
  E = codomain(f)
  den = (f\E(denominator(I)))*OK
  return reduce(+, (OK(f\(b)) * OK for b in absolute_basis(numerator(I))), init = 0 * OK)//den
end

function preimage(f::NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}}, I::RelNumFieldOrderFractionalIdeal)
  OK = maximal_order(domain(f))
  return preimage(f, I, OK)
end


################################################################################
#
#  "Strong" approximation
#
################################################################################

# Cohen 1.3.11
function _strong_approximation(S, ep, xp)
  OK = order(S[1])
  if length(S) > 1
    @assert sum(S) == 1 * OK
  end
  if all(x -> x >= 0, ep) && all(is_integral, xp)
    return _strong_approximation_easy(S, ep, xp)
  else
    d = reduce(lcm, (denominator(x) for x in xp), init = one(ZZRingElem))
    for i in 1:length(S)
      l = valuation(d, S[i]) - ep[i]
      if l < 0
        d = d * absolute_minimum(S[i])^(l)
      end
      @assert valuation(d, S[i]) + ep[i] >= 0
    end
  end
  _ep = ZZRingElem[]
  _xp = AbsSimpleNumFieldElem[]
  _S = support(d * OK)
  _SS = ideal_type(OK)[]
  for i in 1:length(S)
    push!(_ep, ep[i] + valuation(d, S[i]))
    push!(_xp, d * xp[i])
    push!(_SS, S[i])
  end
  for p in _S
    if !(p in _SS)
      push!(_ep, valuation(d, p))
      push!(_xp, zero(nf(OK)))
      push!(_SS, p)
    end
  end

  y = _strong_approximation_easy(_SS, _ep, _xp)
  z = y//d

  for i in 1:length(ep)
    @assert valuation(xp[i] - z, S[i]) == ep[i]
  end
  return z
end

function _strong_approximation_easy(S, ep, xp)
  if length(S) == 1
    p = S[1]
    ap = uniformizer(p)
    z = xp[1] - ap^(ep[1])
    @assert valuation(xp[1] - z, S[1]) == ep[1]
    @assert z == 0 || all(p -> (valuation(z, p) >= 0 || p in S), support(z * order(S[1])))
    return z
  end
  OK = order(S[1])
  # assume ep non-negative and xp in R
  I = reduce(*, (S[i]^(ep[i] + 1) for i in 1:length(S)), init = 1 * OK)
  aps = ideal_type(OK)[]
  bps = elem_type(nf(OK))[]
  for i in 1:length(S)
    bp = elem_in_nf(uniformizer(S[i]))^(ep[i])
    push!(bps, bp)
    ap = divexact(I, S[i]^(ep[i] + 1))
    @assert ap * S[i]^(ep[i] + 1) == I
    push!(aps, ap)
  end
  as = _idempotents(aps)
  for i in 1:length(as)
    @assert as[i] in aps[i]
  end
  @assert sum(as) == one(OK)
  @assert length(as) == length(aps)
  z = elem_in_nf(reduce(+, (as[i]* (xp[i] + bps[i]) for i in 1:length(as)), init = zero(OK)))
  for i in 1:length(ep)
    @assert valuation(z - xp[i], S[i]) == ep[i]
  end
  return z
end

function _idempotents(x::Vector)
  @assert length(x) >= 2

  k = length(x)
  O = order(x[1])
  @assert sum(x) == 1 * O
  d = degree(O)
  # form the matrix
  #
  # ( 1 |  1  | 0 )
  # ( 0 | M_x | I )
  # ( 0 | M_y | 0 )

  V = zero_matrix(FlintZZ, d * k + 1, d * k + 1)

  u = coordinates(one(O))

  V[1, 1] = 1

  for i in 1:d
    V[1, i + 1] = u[i]
  end

  for i in 1:k
    VV = view(V, (2 + (i - 1)*d):(2 + i*d - 1), 2:(2 + d))
    B = basis_matrix(x[i], copy = false)
    for m in 1:d
      for n in 1:d
        VV[m, n] = B[m, n]
      end
    end
  end

  #println("V:\n", sprint(show, "text/plain", V))

  for i in 1:(k - 1)
    VV = view(V, (2 + (i-1)*d):(2 + i*d - 1), (i*d + 2):((i + 1)*d + 1))
    for m in 1:d
      VV[m, m] = 1
    end
    #println("V:\n", sprint(show, "text/plain", V))
  end

  #println("V:\n", sprint(show, "text/plain", V))

  m = lcm(ZZRingElem[minimum(x[i], copy = false) for i in 1:length(x)])

  H = hnf_modular_eldiv!(V, m) # upper right

  for i in 2:(1 + d)
    if H[1, i] != 0
      error("Ideals are not coprime")
    end
  end

  els = elem_type(O)[]

  #println("H:\n", sprint(show, "text/plain", H))

  for i in 1:(k - 1)
    B = basis(x[i], copy = false)
    z = zero(O)
    for j in 1:d
      z += H[1, 1 + j + (i)*d] * B[j]
    end
    push!(els, z)
  end

  @assert one(O) + sum(els[i] for i in 1:length(els)) in x[end]

  push!(els, (one(O) + sum(els[i] for i in 1:k - 1)))
  for i in 1:length(els) - 1
    els[i] = -els[i]
  end
  @assert sum(els) == one(O)
  return els
end

################################################################################
#
#  Some helper functions
#
################################################################################

function _weak_approximation_coprime(IP, S, M)
  R = order(M)
  A, _exp, _log = sign_map(R, _embedding.(IP), M)

  t = (1 + _exp(A([ S[j] == 1 ? 0 : -1 for j in 1:length(IP)])))
  @assert all(i -> sign(t, IP[i]) == S[i], 1:length(IP))
  return t
end

################################################################################
#
#  Helper functions (sort them later)
#
################################################################################

function image(f::NumFieldHom, I::RelNumFieldOrderIdeal{T, S}) where {T, S}
  #f has to be an automorphism!!!!
  O = order(I)
  @assert is_maximal(O) # Otherwise the order might change
  K = nf(O)

  B = absolute_basis(I)

  if I.is_prime == 1
    lp = prime_decomposition(O, minimum(I))
    for (Q, e) in lp
      if I.splitting_type[2] == e
        if all(b -> f(b) in Q, B)
          return Q
        end
      end
    end
  end

  pb = pseudo_basis(I)
  pm = basis_pmatrix(I)

  m = zero(matrix(pm))

  c = coefficient_ideals(pm)

  for i in 1:length(pb)
    cc = coordinates(O(f(pb[i][1])))
    for j in 1:length(cc)
      m[i, j] = cc[j]
    end
  end

  J = ideal(O, pseudo_matrix(m, c))

  if isdefined(I, :minimum)
    J.minimum = I.minimum
  end

  J.has_norm = I.has_norm

  if isdefined(I, :norm)
    J.norm = I.norm
  end

  if isdefined(I, :is_prime)
    J.is_prime = I.is_prime
  end

  if isdefined(I, :splitting_type)
    J.splitting_type = I.splitting_type
  end

  return J
end

function image(f::NumFieldHom, I::RelNumFieldOrderFractionalIdeal{T, S}; order = order(I)) where {T, S}
  #S has to be an automorphism!!!!
  O = order
  @assert is_maximal(O) # Otherwise the order might change
  K = nf(O)
  @assert K === codomain(f)

  pb = pseudo_basis(I)

  z = sum(b * (f(a) * O) for (a, b) in pb; init = zero(K) * O)
  return z
end

# An element is locally a square if and only if the quadratic defect is 0, that is
# the valuation is inf.
# (see O'Meara, Introduction to quadratic forms, 3rd edition, p. 160)
function is_local_square(a, p)
  return quadratic_defect(a, p) isa PosInf
end

function _map(a::AbstractAlgebra.MatrixElem, f)
  z = similar(a)
  for i in 1:nrows(a)
    for j in 1:ncols(a)
      z[i, j] = f(a[i, j])
    end
  end
  return z
end

# I think I need a can_change_base_ring version

function element_with_signs(K, D::Dict{<:NumFieldEmb, Int})
  return _element_with_signs(K, D)
end

function _element_with_signs(K, D)
  OK = maximal_order(K)
  G, mG = sign_map(OK, real_embeddings(K), 1*OK)
  r = real_embeddings(K)
  z = id(G)
  for (v, s) in D
    for i in 1:length(r)
      if s == 1
        ss = 0
      else
        ss = 1
      end

      if v == r[i]
        z = z + ss * G[i]
      end
    end
  end
  zz = elem_in_nf(mG(z))::elem_type(K)
  @assert all(u -> sign(zz, u[1]) == u[2], D)
  return zz
end

function element_with_signs(K, P::Vector{<:NumFieldEmb}, S::Vector{Int})
  return _element_with_signs(K, zip(P, S))
end

function element_with_signs(K, A::Vector{Tuple{T, Int}}) where {T <: NumFieldEmb}
  return _element_with_signs(K, A)
end

################################################################################
#
#  Local norms in quadratic extensions
#
################################################################################

@doc raw"""
    is_local_norm(L::NumField, a::NumFieldElem, P)

Given a number field $L/K$, an element $a \in K$ and a prime ideal $P$ of $K$,
returns whether $a$ is a local norm at $P$.

The number field $L/K$ must be a simple extension of degree 2.
"""
is_local_norm(::NumField, ::NumFieldElem, ::Any)

function is_local_norm(K::AbsSimpleNumField, a::QQFieldElem, p::ZZRingElem)
  degree(K) != 2 && error("Degree of number field must be 2")
  x = gen(K)
  b = (2 * x - tr(x))^2
  @assert degree(minpoly(b)) == 1
  bQ = coeff(b, 0)
  return hilbert_symbol(a, bQ, p) == 1
end

function is_local_norm(K::AbsSimpleNumField, a::QQFieldElem, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  p = minimum(P)
  return is_local_norm(K, a, p)
end

function is_local_norm(K::AbsSimpleNumField, a::RingElement, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  return is_local_norm(K, FlintQQ(a), P)
end

function is_local_norm(K::AbsSimpleNumField, a::RingElement, p::ZZRingElem)
  return is_local_norm(K, FlintQQ(a), p)
end

function is_local_norm(K::AbsSimpleNumField, a::RingElement, p::Integer)
  return is_local_norm(K, FlintQQ(a), ZZRingElem(p))
end

function is_local_norm(K::RelSimpleNumField{T}, a::T, P) where {T} # ideal of parent(a)
  nf(order(P)) != parent(a) && error("Prime ideal must have the same base field as the second argument")
  degree(K) != 2 && error("Degree of number field must be 2")
  x = gen(K)
  b = (2 * x - tr(x))^2
  @assert degree(minpoly(b)) == 1
  bQ = coeff(b, 0)
  return hilbert_symbol(a, bQ, P) == 1
end

################################################################################
#
#  Special local units
#
################################################################################

# Return a local unit u (that is, valuation(u, P) = 0) with trace one.
# P must be even and inert (P is lying over p)
function _special_unit(P, p::ZZRingElem)
  R = order(P)
  E = nf(R)
  @assert degree(E) == 2
  x = gen(E)
  x = x - trace(x)//2
  a = coeff(x^2, 0)
  K = base_field(E)
  pi = elem_in_nf(uniformizer(p))
  v = valuation(a, p)
  if v != 0
    @assert iseven(v)
    a = a//pi^v
    x = x//pi^(div(v, 2))
  end
  k = GF(p, cached = false)
  hex(x) = k(numerator(x)) * inv(k(denominator(x)))
  hexinv(x) = FlintQQ(lift(x))
  t = hexinv(sqrt(hex(a)))
  a = a//t^2
  x = x//t
  w = valuation(a - 1, p)
  e = valuation(order(p)(2), p)
  while w < 2*e
    @assert iseven(w)
    s = sqrt(hex((a - 1)//pi^w))
    t = 1 + (hexinv(s)) * pi^(div(w, 2))
    a = a//t^2
    x = x//t
    w = valuation(a - 1, p)
  end
  @assert w == 2 * e
  u = (1 + x)//2
  @assert trace(u) == 1
  @assert valuation(u, P) == 0
  return u
end

function _special_unit(P, p)
  @assert ramification_index(P) == 1
  @assert is_dyadic(p)
  R = order(P)
  E = nf(R)
  @assert degree(E) == 2
  x = gen(E)
  x = x - trace(x)//2
  a = coeff(x^2, 0)
  K = base_field(E)
  pi = elem_in_nf(uniformizer(p))
  v = valuation(a, p)
  if v != 0
    @assert iseven(v)
    a = a//pi^v
    x = x//pi^(div(v, 2))
  end
  k, h = residue_field(order(p), p)
  hex = extend(h, K)
  t = hex \ sqrt(hex(a))
  a = a//t^2
  x = x//t
  w = valuation(a - 1, p)
  e = valuation(order(p)(2), p)
  while w < 2*e
    @assert iseven(w)
    s = sqrt(hex((a - 1)//pi^w))
    t = 1 + (hex \ s) * pi^(div(w, 2))
    a = a//t^2
    x = x//t
    w = valuation(a - 1, p)
  end
  @assert w == 2 * e
  u = (1 + x)//2
  @assert trace(u) == 1
  @assert valuation(u, P) == 0
  return u
end

################################################################################
#
#  Valuation of trace ideal generated by elements
#
################################################################################

# L is a list of (integral) number field elements
# and p a prime ideal of the maximal.
# Return v(tr(<L>), P).
function trace_ideal_valuation(L, p)
  R = order(p)
  v = valuation(different(R), p)
  V = unique!(valuation(l, p) for l in L if !iszero(l))
  X = Int[ 2 *div(l + v, 2) for l in V]
  if length(X) == 0
    return inf
  else
    minimum(X)
  end
end

function _get_norm_valuation_from_gram_matrix(G, P)
  n = ncols(G)
  R = order(P)
  L = nf(R)
  K = base_field(L)
  trrr = R * (tr(fractional_ideal(order(P), [G[i, j] for i in 1:n for j in i+1:n])))
  if iszero(trrr)
    T = inf
  else
    T = valuation(trrr, P)
  end
  #T = trace_ideal_valuation((G[i, j] for i in 1:n for j in i+1:n), P)
  diag = minimum(iszero(G[i, i]) ? inf : valuation(G[i, i], P) for i in 1:n)
  if T isa PosInf
    return diag
  else
    return min(T, diag)
  end
end

################################################################################
#
#  Treat FlintQQ as a number field
#
################################################################################

uniformizer(p::ZZRingElem) = p

is_dyadic(p::ZZRingElem) = p == 2

################################################################################
#
#  Normic defect
#
################################################################################

function normic_defect(E, a, p)
  R = maximal_order(E)
  if iszero(a) || is_local_norm(E, a, p)
    return inf
  end
  return valuation(a, p) + valuation(discriminant(R), p) - 1
end

################################################################################
#
#  Find quaternion algebras
#
################################################################################

# Given an element b in a number field K and sets of finite and infinite
# places P and I of K, return an element a in K such that
# { v: (a,b)_v = -1 } = P \cup I
# Note that the function computes the unit and class groups of K!
# TODO: use factored elements
function _find_quaternion_algebra(b, P, I)
  @assert iseven(length(I) + length(P))
  @assert all(p -> !is_local_square(b, p), P)
  @assert all(p -> is_negative(b, p), I)

  K = parent(b)
  if length(P) > 0
    R = order(P[1])
  else
    R = maximal_order(K)
  end

  n = length(P)
  m = length(I)

  _J = b * R
  #_P = Dict{}()
  __P = copy(P)
  #for p in P
  #  _P[p] = true
  #end
  for p in support(_J)
    if !(p in __P)
      push!(__P, p)
    end
      #_P[p] = true
  end
  for p in prime_decomposition(R, 2)
    if !(p[1] in __P)
      push!(__P, p[1])
    end
  end
  for p in real_places(K)
    if !(p in I) && is_negative(b, p)
      push!(I, p)
    end
  end

  F = Nemo.Native.GF(2)

  target = matrix(F, 1, length(__P) + length(I), vcat(fill(1, n), fill(0, length(__P) - n), fill(1, m), fill(0, length(I) - m)))
  if iszero(target)
    return one(K)
  end

  #__P = convert(Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, collect(keys(_P)))

  found = false
  U, h = unit_group(R)
  sign_vector = g -> begin
    return matrix(F, 1, length(__P) + length(I),
                  vcat([div(1 - hilbert_symbol(K(g), b, p), 2) for p in __P ], [ div(1 - sign(g, p), 2) for p in I]))
  end


  L, f = sunit_group(identity.(__P))
  M = zero_matrix(F, 0, length(__P) + length(I))
  elts = AbsSimpleNumFieldElem[]

  for i in 1:ngens(L)
    v = sign_vector(f(L[i]))
    if rank(M) == rank(vcat(M, v))
      continue
    end
    M = vcat(M, v)
    push!(elts, f(L[i])) # cache
    fl, w = can_solve_with_solution(M, target, side = :left)
    if fl
      found = true
      break
    end
  end

  if !found
    Cl, mCl = class_group(R)
    A = abelian_group(fill(0, length(__P)))
    hh = hom(A, Cl, [mCl\(p) for p in __P])
    S, mS = image(hh, false)
    Q, mQ = quo(Cl, [mS(S[i]) for i in 1:ngens(S)])

    p = 2
    while !found
      p = next_prime(p)
      for (q, e) in prime_decomposition(R, p)
        if q in __P
          continue
        end
        o = order(mQ(mCl\(q)))
        c = -(hh\(o * (mCl\(q))))
        fl, x = is_principal_with_data(q * prod(__P[i]^Int(c.coeff[i]) for i in 1:length(__P)))
        @assert fl
        v = sign_vector(elem_in_nf(x))
        if rank(M) == rank(vcat(M, v + target))
          found = true
          M = vcat(M, v)
          push!(elts, elem_in_nf(x))
          break
        end
      end
    end
  end
  fl, v = can_solve_with_solution(M, target, side = :left)
  @assert fl
  z = evaluate(FacElem(Dict(elts[i] => Int(lift(v[1, i])) for i in 1:ncols(v))))
  @assert sign_vector(z) == target
  return z
end

function _find_quaternion_algebra(b::QQFieldElem, P, I)
  K, a = rationals_as_number_field()
  bK = K(b)
  OK = maximal_order(K)
  PK = ideal_type(OK)[]
  for p in P
    push!(PK, prime_decomposition(OK, p)[1][1])
  end
  if length(I) == 0
    IK = InfPlc[]
  else
    @assert length(I) == 1
    IK = infinite_places(K)
  end
  c = _find_quaternion_algebra(bK, PK, IK)::AbsSimpleNumFieldElem
  return coeff(c, 0)
end

################################################################################
#
#  Weak approximation
#
################################################################################

function _weak_approximation(I::Vector{<: InfPlc}, val::Vector{<: Int})
  K = number_field(first(I))
  if degree(K) == 2
    return _weak_approximation_quadratic(I, val)
  else
    return _weak_approximation_generic(I, val)
  end
end

function _weak_approximation_generic(I::Vector{<: InfPlc}, val::Vector{Int})
  K = number_field(first(I))
  OK = maximal_order(K)
  local A::FinGenAbGroup
  A, exp, log = sign_map(OK, _embedding.(I), 1 * OK)
  uni = infinite_uniformizers(K)
  target_signs = zeros(Int, ngens(A))

  if all(isequal(1), val)
    return one(K)
  elseif all(isequal(-1), val)
    return -one(K)
  end

  for P in I
    v = log(uni[embedding(P)])::FinGenAbGroupElem
    for i in 1:ngens(A)
      if v.coeff[i] == 1
        target_signs[i] = val[i] == -1 ? 1 : 0
        break
      end
    end
  end
  c = K(exp(A(target_signs))::elem_type(OK))
  for i in 1:length(I)
    @assert sign(c, I[i]) == val[i]
  end
  return c
end

function _weak_approximation_quadratic(I::Vector{<: InfPlc}, val::Vector{Int})
  K = number_field(first(I))
  if length(I) == 1
    return K(val[1])
  else
    if val[1] == val[2]
      return K(val[1])
    else
      x = gen(K)
      s1 = sign(x, I[1])
      s2 = sign(x, I[2])
      if s1 == val[1] && s2 == val[2]
        return x
      elseif s1 == -val[1] && s2 == -val[2]
        return -x
      else
        return _weak_approximation_generic(I, val)
      end
    end
  end
end

################################################################################
#
#  Decreasing non-negative inter sequences
#
################################################################################

# Compute all decreasing non-negative integer sequences of length len with sum
# equal to sum.
# This is not optimized.
function _integer_lists(sum::Int, len::Int)
  if len <= 0
    return Vector{Int}[]
  end
  if sum == 0
    return Vector{Int}[fill(0, len)]
  end
  if len == 1
    return Vector{Int}[Int[sum]]
  end
  res = Vector{Vector{Int}}()
  for i in 0:sum
    rec = _integer_lists(sum - i, len - 1)::Vector{Vector{Int}}
    if isempty(rec)
      push!(res, append!(Int[i], fill(0, len - 1)))
    else
      for v in rec
        push!(res, append!(Int[i], v))
      end
    end
  end
  return res
end

function _integer_lists(sum::Int, minval::Int, maxval::Int)
  len = maxval-minval+1
  return _integer_lists(sum, len)
end

is_dyadic(p) = is_dyadic(minimum(p))

################################################################################
#
#  Local non-norms
#
################################################################################

# find an element of K, which is not a local norm at p
# p must be ramified
# See [Kir16, Corollary 3.3.17]
function _non_norm_rep(E, K, p)
  K = base_field(E)
  if is_ramified(maximal_order(E), p)
    if !is_dyadic(p)
      U, mU = unit_group(maximal_order(K))
      for i in 1:ngens(U)
        u = mU(U[i])
        if !is_local_norm(E, elem_in_nf(u), p)
          return elem_in_nf(u)
        end
      end
      B = elem_in_nf.(basis(p))
      k = 0
      while true
        if k > 10000
          error("Something wrong in non_norm_rep")
        end
        y = rand(K, -5:5)
        if iszero(y)
          continue
        end
        if !is_local_norm(E, y, p) && iszero(valuation(y, p))
          return y
        end
        k += 1
      end
    else
      lP = prime_decomposition(maximal_order(E), p)
      @assert length(lP) == 1 && lP[1][2] == 2
      Q = lP[1][1]
      e = valuation(different(maximal_order(E)), Q)
      U, mU = unit_group(maximal_order(K))
      for i in 1:ngens(U)
        u = mU(U[i])
        if !is_local_norm(E, elem_in_nf(u), p) && (valuation(u - 1, p) == e - 1)
          return elem_in_nf(u)
        end
      end
      # We look for a local unit u such that v_p(u - 1) = e - 1 and
      # u not a local norm
      tu = elem_in_nf(mU(U[1]))
      tuo = order(U[1])
      B = elem_in_nf.(basis(p^(e - 1)))
      k = 0
      while true
        if k > 10000
          error("Something wrong in non_norm_rep")
        end
        y = (1 + rand(B, -1:1)) * tu^(rand(1:tuo))
        @assert valuation(y, p) == 0
        if !is_local_norm(E, y, p) && valuation(y - 1, p) == e - 1
          return y
        end
        k += 1
      end
    end
    error("This should not happen ...")
  else
    lP = prime_decomposition(maximal_order(E), p)
    if length(lP) == 2
      error("This dosses not make any sense!")
    else
      return elem_in_nf(p_uniformizer(p))
     end
  end
end

# P must be inert and odd
# Find an element which is a locally a norm, but not a square
function _non_square_norm(P)
  @assert !is_dyadic(P)
  #@assert is_inert(P)
  R = order(P)
  p = minimum(P)
  k, h = residue_field(order(P), P)
  kp, hp = residue_field(order(p), p)
  local u
  while true
    r = rand(k)
    u = h\r
    if !iszero(r) && !is_square(hp(norm(u)))[1]
      break
    end
  end
  return u
end

################################################################################
#
#  Matrices as Vector
#
################################################################################

_eltseq(M::MatElem) = [M[i, j] for i in 1:nrows(M) for j in 1:ncols(M)]

################################################################################
#
#  Maximal subspaces
#
################################################################################

function maximal_subspaces(k::Field, n::Int)
  I = identity_matrix(k, n)
  L = typeof(I)[]
  for i in 1:n
    II = remove_row(I, i)
    if i == 1
      push!(L, II)
      continue
    end
    #V = Iterators.product([k for j in 1:(i - 1)]...)
    VV = [collect(k) for j in 1:(i - 1)]
    V = cartesian_product_iterator(VV, inplace = false)
    for v in V
      III = deepcopy(II)
      for l in 1:(i - 1)
        III[l, i] = v[l]
      end
      push!(L, III)
    end
  end
  return L
end

