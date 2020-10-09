################################################################################
#
#  Abstract Jordan decomposition
#
################################################################################

# This holds invariants of a local Jordan decomposition
#
# L = L_1 \perp ... \perp L_r
#
# In the non-dyadic case we store
# - ranks
# - scales
# - determinant (classes)
# of the L_i
#
# In the dyadic case we store
# - norm generators of L_i
# - (valuation of ) weights
# - determinant (classes)
# - Witt invariants 

mutable struct JorDec{S, T, U}
  K::S
  p::T
  isdyadic::Bool
  ranks::Vector{Int}
  scales::Vector{Int}

  # dyadic things
  normgens::Vector{U}
  weights::Vector{Int}
  dets::Vector{U}
  witt::Vector{Int}

  JorDec{S, T, U}() where {S, T, U} = new{S, T, U}()
end

function JorDec(p, scales::Vector{Int}, ranks::Vector{Int}, dets::Vector{nf_elem})
  K = nf(order(p))
  _weight = Vector{Int}()
  _normgen = Vector{elem_type(K)}()
  _f = Int[]
  witt = Int[]
  z = JorDec{typeof(K), typeof(p), elem_type(K)}()
  z.isdyadic = isdyadic(p)
  z.K = K
  z.p = p
  z.ranks = ranks
  z.scales = scales
  z.normgens = _normgen
  z.weights = _weight
  z.witt = witt
  z.dets = dets
  return z
end

function Base.show(io::IO, J::JorDec)
  p = J.p
  if !isdyadic(p)
    for i in 1:length(J)
      print(io, "(", J.scales[i], ", ", J.ranks[i], ", ", J.dets[i], ")")
    end
  else
    for i in 1:length(J)
      print(io, "(", J.scales[i], ", ", J.ranks[i], ", ", J.normgens[i], ", ", J.weights[i], ", ", J.dets[i], ", ", J.witt[i], ")")
    end
  end
end

function Base.show(io::IO, ::MIME"text/plain", J::JorDec)
  p = J.p
  if !get(io, :compact, false)
    print(IOContext(io, :compact => true), "Abstract Jordan decomposition at ", p)
    if !isdyadic(p)
      print(io, "\n(scale, rank, determinant class)")
    else
      print(io, "\n(scale, rank, norm generator, weight, det, Witt)")
    end
  end
  print(io, "\n")
  if !isdyadic(p)
    for i in 1:length(J)
      print(io, "(", J.ranks[i], ", ", J.scales[i], ", ", J.dets[i], ")")
    end
  else
    for i in 1:length(J)
      print(io, "(", J.scales[i], ", ", J.ranks[i], ", ", J.normgens[i], ", ", J.weights[i], ", ", J.dets[i], ", ", J.witt[i], ")")
    end
  end
end

length(J::JorDec) = length(J.ranks)

function JorDec(p, sc::Vector{Int}, rks::Vector{Int}, normgens::Vector{nf_elem}, weights::Vector{Int}, dets::Vector{nf_elem}, witts::Vector{Int}) 
  K = nf(order(p))
  z = JorDec{typeof(K), typeof(p), elem_type(K)}()
  z.isdyadic = isdyadic(p)
  z.K = K
  z.p = p
  z.ranks = rks
  z.scales = sc
  z.normgens = normgens
  z.weights = weights
  z.witt = witts
  z.dets = dets
  return z
end

# Construction of abstract Jordan decomposition from a concrete Jordan decomposition
function JorDec(J, G, E, p)
  O = order(p)
  K = nf(O)
  t = length(G)
  _, _h = ResidueField(O, p)
  h = extend(_h, K)
  if !isdyadic(p)
    dets = elem_type(K)[det(G[i]) for i in 1:t]
    _weight = Vector{Int}()
    _normgen = Vector{elem_type(K)}()
    _f = Int[]
    witt = Int[]
    #Gs = [ h(prod(diagonal(G[i]))//unif^(E[i] * nrows(J[i]))) for i in 1:length(J)]
    #@assert !(0 in Gs)
    #x  = [ (nrows(J[i]), E[i], issquare(Gs[i])[1] ? 1 : -1) for i in 1:length(J)]
    #return LocalGenusSymbol{QuadLat}(p, x, unif, false, base_field(L), nothing, nothing)
  else
    sL = Int[ minimum(Union{PosInf, Int}[iszero(g[i, j]) ? inf : valuation(g[i, j], p) for j in 1:ncols(g) for i in 1:j]) for g in G]
    @assert sL == E
    _sym = Vector{Tuple{Int, Int, Int}}(undef, t)
    e = ramification_index(p)
    aL = elem_type(K)[]
    uL = Int[]
    wL = Int[]
    witt = Int[]
    dets = elem_type(K)[]
    unif = elem_in_nf(uniformizer(p))
    for i in 1:t
      _sym[i] = (nrows(J[i]), sL[i], 0)
      push!(dets, det(G[i]))
      push!(witt, witt_invariant(quadratic_space(K, G[i]), p))
      #GG = diagonal_matrix(eltype(G)[ j < i ? unif^(2*(sL[i] - sL[j])) * G[j] : G[j] for j in 1:t])
      D = diagonal(G[i])
      m, pos = findmin(Union{PosInf, Int}[iszero(d) ? inf : valuation(d, p) for d in D])
      if e + sL[i] <= m
        push!(aL, unif^(e + sL[i]))
      else
        push!(aL, D[pos])
      end
      push!(uL, valuation(aL[i], p))
      push!(wL, min(e + sL[i], minimum(Union{PosInf, Int}[uL[i] + quadratic_defect(d//aL[i], p) for d in D])))
    end
    _normgen = aL
    _weight = wL
  end

  z = JorDec{typeof(K), typeof(p), elem_type(K)}()
  z.isdyadic = isdyadic(p)
  z.K = K
  z.p = p
  z.ranks = Int[nrows(J[i]) for i in 1:length(J)]
  z.scales = E
  z.normgens = _normgen
  z.weights = _weight
  z.witt = witt
  z.dets = dets
  return z
end

function JorDec(L::QuadLat, p)
  O = base_ring(L)
  K = nf(O)
  J, G, E = jordan_decomposition(L, p)
  return JorDec(J, G, E, p)
end

@doc Markdown.doc"""
    gram_matrix(J::JorDec, i::Int) -> MatElem

Given an abstract Jordan decomposition $J$ and $i$, return the Gram matrix of
of the $i$-th block of $J$.
"""
function gram_matrix(J::JorDec, i::Int)
  @req 1 <= i <= length(J) "Index ($i) must be in range 1:$(length(J))"
  p = J.p
  if J.isdyadic
    r, s, w = J.ranks[i], J.scales[i], J.weights[i]
    d, a, wi = J.dets[i], J.normgens[i], J.witt[i]
    # Not that these are the invariants of G(L_i)
    # We now write G(L_i) = pi^s * G(L_i') with L_i' = L_i^(pi^-s) and L_i' is
    # unimodular. We first have to translate the invariants of L_i to L_i'
    # and then use the classification of unimodular lattices.
    pi = elem_in_nf(uniformizer(J.p))
    _w = w - s
    _d = pi^(-s * r) * d
    @assert valuation(_d, p) == 0
    _a = a//pi^s
    # Adjust the Witt invariant
    ha = _witt_hasse(wi, r, d, p)
    # this is the hasse invariant
    # this is the hasse invariant of the scaled lattice
    hanew = ha * hilbert_symbol((-1)^(div(r*(r-1), 2)) * d^(r - 1), inv(pi)^s, p)
    winew = _witt_hasse(hanew, r, _d, p)
    # this is the new witt invariant
    z = _quadratic_unimodular_lattice_dyadic(p, r, _w, _d, _a, winew)
    @assert begin L = quadratic_lattice(nf(order(p)), gram_ambient_space = z); witt_invariant(L, p) == winew end

    @assert valuation(det(z), p) == 0
    zz = pi^s * z
    if wi < 2
      @assert begin L = quadratic_lattice(nf(order(p)), gram_ambient_space = zz); witt_invariant(L, p) == wi end
    end
    return zz
  else
    r = J.ranks[i]
    s = J.scales[i]
    z = identity_matrix(J.K, r)
    pi = elem_in_nf(uniformizer(p))
    q = J.dets[i]//pi^(r * s)
    @assert valuation(q, p) == 0
    if islocal_square(pi^(r * s) * J.dets[i], p)
      z[r, r] = one(parent(pi))
    else
      z[r, r] = _non_square(J.K, p)
    end
    return pi^s * z
  end
end

@doc Markdown.doc"""
    gram_matrix(J::JorDec) -> MatElem

Given an abstract Jordan decomposition, return the Gram matrix of a lattice
admitting this Jordan decompositon.
"""
function gram_matrix(J::JorDec)
  K = J.K
  D = diagonal_matrix(dense_matrix_type(K)[gram_matrix(J, i) for i in 1:length(J)])
  return D
end

@doc Markdown.doc"""
    gram_matrix(J::JorDec) -> MatElem

Given an abstract Jordan decomposition, return a lattice admitting this Jordan
decompositon.
"""
function lattice(J::JorDec)
  return quadratic_lattice(J.K, gram_ambient_space = gram_matrix(J))
end

@doc Markdown.doc"""
    genus(J::JorDec) -> LocalGenusQuad

Given an abstract Jordan decomposition, return the local genus to which the
corresponding matrix belongs.
"""
function genus(J::JorDec)
  r = length(J.ranks)
  sca = J.scales
  p = J.p
  pi = elem_in_nf(uniformizer(p))
  if !isdyadic(p)
    detclass = Int[]
    for i in 1:length(J.ranks)
      push!(detclass, islocal_square(J.dets[i]//pi^(J.ranks[i] * J.scales[i]), p) ? 1 : -1)
    end
    z = genus(QuadLat, p, pi, J.ranks, J.scales, detclass)
    z.dets = J.dets
    z.jordec = J
    return z
  end
  K = nf(order(p))
  normgens = J.normgens
  new_normgens = Vector{eltype(normgens)}(undef, r)
  new_weights = Vector{Int}(undef, r)
  e = ramification_index(p)
  for i in 1:r
    # find the minimal norm
    # L^(s_i) = \sum p^(max(0, s_i - s_j)) L_j
    new_normgen = zero(K)
    new_norm = inf # valuation(normgens[i], p)
    for j in 1:r
      poss_normgen = pi^max(0, 2*(sca[i] - sca[j])) * normgens[j]
      poss_n = max(0, 2*(sca[i] - sca[j])) + valuation(normgens[j], p)
      if poss_n < new_norm
        new_norm = poss_n
        new_normgen = poss_normgen
      end
    end

    # Now determine w(L^(s_i)) using this norm generator
    # We first determine the diagonal of a gram matrix of L^(s_i)
    D = elem_type(K)[]
    for j in 1:r
      # TODO: We could determine just the diagonal, that would be easier.
      # Also, there is some redundancy here, the z is acutally independent of i
      z = gram_matrix(J, j)
      for l in 1:nrows(z)
        push!(D, pi^(max(0, 2 * (sca[i] - sca[j]))) * z[l, l])
      end
    end

    # Lemma 3.3.9
    
    #@show new_normgen
    #@show new_norm
    #@show D

    # Now the scale of L^(s_i) is si
    weight = minimum(Union{PosInf, Int}[new_norm + quadratic_defect(divexact(d, new_normgen), p) for d in D])
    #@show weight
    weight = min(weight, e + sca[i])
    #@show weight
    new_weights[i] = weight
    new_normgens[i] = new_normgen
  end
  g =  genus(QuadLat, p, J.ranks, J.scales, new_weights, J.dets, new_normgens, J.witt)
  g.norms = Int[]
  g.jordec = J
  return g
end

################################################################################
#
#  Construct unimodular lattices with given invariants
#
################################################################################

# p = prime ideal
# r = rank
# w = weight (valuation)
# d = determinant (class)
# alpha = norm generator
# wi = Witt invariants
#
# This is [Kirschmer2016, Proposition 3.3.11]
function _quadratic_unimodular_lattice_dyadic(p, r, w, d, alpha, wi)
  m = r
  K = nf(order(p))
  e = ramification_index(p)
  pi = elem_in_nf(uniformizer(p))
  if m == 1
    return matrix(K, 1, 1, elem_type(K)[d])
  end
  
  D = kummer_generator_of_local_unramified_quadratic_extension(p)
  rho = divexact(1 - D, 4)
  @assert valuation(rho, p) == 0
  @assert quadratic_defect(D, p) == valuation(4, p) 

  if isodd(m)
    r = div(m - 1, 2)
    @assert (w == e) || (w < e && isodd(w))
    mats = dense_matrix_type(K)[]
    if wi == 1
      push!(mats, _Amatrix(K, pi^w, 0))
      push!(mats, matrix(K, 1, 1, [(-1)^r * d]))
      for i in 1:(r - 1)
        push!(mats, _Amatrix(K, 0, 0))
      end
    else
      @assert wi == -1
      push!(mats, _Amatrix(K, pi^w, 4 * rho * pi^(-w)))
      push!(mats, matrix(K, 1, 1, [inv(D) * (-1)^r * d]))
      for i in 1:(r - 1)
        push!(mats, _Amatrix(K, 0, 0))
      end
    end
    return diagonal_matrix(mats)
  else
    r = div(m, 2)
    @assert valuation(d, p) == 0
    mmod4 = mod(m, 4)
    if mmod4 == 0 || mmod4 == 1
      gamma = _find_special_class(d, p) - 1
      @assert islocal_square(d//(1 + gamma), p)
      @assert valuation(d, p) == valuation(1 + gamma, p)
    else
      gamma = _find_special_class(-d, p) - 1
      @assert islocal_square(-d//(1 + gamma), p)
      @assert valuation(-d, p) == valuation(1 + gamma, p)
    end
    @assert quadratic_defect(1 + gamma, p) == (iszero(gamma) ? inf : valuation(gamma, p))
    if iseven(valuation(alpha, p) + w)
      @assert w == e
      mats = dense_matrix_type(K)[]
      @assert iszero(gamma) || valuation(gamma, p) >= w + valuation(alpha, p)
      push!(mats, _Amatrix(K, alpha, -gamma * inv(alpha)))
      @assert valuation(det(mats[end]), p) == 0
      for i in 1:(r - 1)
        push!(mats, _Amatrix(K, 0, 0))
      end
      return diagonal_matrix(mats)
    elseif r == 1
      @assert isodd(valuation(alpha, p) + w)
      @assert w == e || (e > w && w == valuation(gamma, p) - valuation(alpha, p))
      return _Amatrix(K, alpha, -gamma * inv(alpha))
    elseif r >= 2 && isodd(valuation(alpha, p) + w)
      mats = dense_matrix_type(K)[]
      # Kirschmer Remark 3.3.12
      if wi == hilbert_symbol(alpha, 1 + gamma, p)
        push!(mats, _Amatrix(K, alpha, -gamma * inv(alpha)))
        push!(mats, _Amatrix(K, pi^w, 0))
        for i in 1:(r - 2)
          push!(mats, _Amatrix(K, 0, 0))
        end
      else
        push!(mats, _Amatrix(K, alpha, -(gamma - 4 * rho) * inv(alpha)))
        push!(mats, _Amatrix(K, pi^w, 4 * rho * pi^(-w)))
        for i in 1:(r - 2)
          push!(mats, _Amatrix(K, 0, 0))
        end
      end
      z = diagonal_matrix(mats)
      @assert valuation(det(z), p) == 0
      return z
    else
      throw(error("This should not happen"))
    end
  end
end

################################################################################
#
#  Local genus symbol
#
################################################################################

# This holds invariants of a local Genus symbol
#
# L = L_1 \perp ... \perp L_r
#
# In the non-dyadic case we store
# - ranks
# - scales
# - determinant (classes)
# of the L_i = L^(s_i)
#
# In the dyadic case we store
# - norm generators of L^(s_i)
# - (valuation of ) weights of L^(s_i)
# - determinant (classes) of L^(s_i)
# - Witt invariants of L_i

mutable struct LocalGenusQuad{S, T, U}
  K::S
  p::T
  isdyadic::Bool
  witt_inv::Int
  hass_inv::Int
  det::U
  rank::Int
  
  uniformizer::U

  ranks::Vector{Int}
  scales::Vector{Int}
  detclasses::Vector{Int}

  # dyadic things
  normgens::Vector{U}
  weights::Vector{Int}
  f::Vector{Int}
  dets::Vector{U}
  witt::Vector{Int}
  norms::Vector{Int}

  # Sometimes a know a jordan decomposition
  jordec::JorDec{S, T, U}

  function LocalGenusQuad{S, T, U}() where {S, T, U}
    z = new{S, T, U}()
    z.rank = 0
    z.witt_inv = 0
    z.hass_inv = 0
    return z
  end
end

function in(L::QuadLat, G::LocalGenusQuad)
  return genus(L, prime(G)) == G
end

function local_quadratic_genus_type(K)
  return LocalGenusQuad{typeof(K), 
                        ideal_type(order_type(K)),
                        elem_type(K)}
end

# Access
prime(G::LocalGenusQuad) = G.p

length(G::LocalGenusQuad) = length(G.ranks)

scales(G::LocalGenusQuad) = G.scales

ranks(G::LocalGenusQuad) = G.ranks

dets(G::LocalGenusQuad) = G.detclasses

weights(G::LocalGenusQuad) = G.weights

function witt_invariant(G::LocalGenusQuad)
  if G.witt_inv != 0
    return G.witt_inv
  end

  p = prime(G)

  @assert isdyadic(p)

  w, d, n = G.witt[1], G.dets[1], G.ranks[1]

  for i in 2:length(G)
    d, w, n = _witt_of_orthgonal_sum(d, w, n, G.dets[i], G.witt[i], G.ranks[i], p)
  end

  G.witt_inv = w

  return w
end

function rank(G::LocalGenusQuad)
  if G.rank != 0
    return G.rank
  end

  rk = sum(G.ranks)

  G.rank = rk
  return rk
end

function det(G::LocalGenusQuad)
  if isdefined(G, :det)
    return G.det
  end

  #if isdyadic(G)
    d = prod(G.dets)
    G.det = d
  #else
  #  pi = uniformizer(G)
  #  d = prod(nf_elem[pi^(G.ranks[i] * G.scales[i]) * G.detclasses[i] for i in 1:length(G)])
  #  G.det = d
  #  #@show d
  #  #@show valuation(d, prime(G))
  #  #@show det(gram_matrix_of_basis(representative(G)))
  #  @assert islocal_square(d * det(gram_matrix_of_basis(representative(G))), prime(G))
  #end
  return d
end

function det(G::LocalGenusQuad, i::Int)
  #if isdyadic(G)
    return G.dets[i]
  #else
  #  pi = uniformizer(G)
  #  return pi^(G.ranks[i] * G.scales[i]) * G.detclasses[i]
  #end
end

function hasse_invariant(G::LocalGenusQuad)
  if isdyadic(G)
    w = witt_invariant(G)
    return _witt_hasse(w, rank(G), det(G), prime(G))
  else
    p = prime(G)
    l = length(G)
    pi = uniformizer(G)
    h = hilbert_symbol((-1)^divexact(G.ranks[1] * (G.ranks[1] - 1), 2) * det(G, 1)^(G.ranks[1] - 1), pi^G.scales[1], p)
    d = det(G, 1)
    for i in 2:l
      h = h * hilbert_symbol(d, det(G, i), p)
      h = h * hilbert_symbol((-1)^divexact(G.ranks[i] * (G.ranks[i] - 1), 2) * det(G, i)^(G.ranks[i] - 1), pi^G.scales[i], p)
      d = d * det(G, i)
    end
    @assert hasse_invariant(representative(G), p) == h
    return h
  end
end 


function uniformizer(G::LocalGenusQuad)
  @req !isdyadic(G) "Genus symbol must not be dyadic"
  return G.uniformizer
end

isdyadic(G::LocalGenusQuad) = G.isdyadic

function norm_generators(G::LocalGenusQuad)
  @req isdyadic(G) "Genus symbol must be dyadic"
  return G.normgens
end

function norms(G::LocalGenusQuad)
  @req isdyadic(G) "Genus symbol must be dyadic"
  if length(G.norms) == 0
    p = prime(G)
    G.norms = Int[valuation(a, p) for a in norm_generators(G)]
    return G.norms
  else
    return G.norms
  end
end
    
function Base.show(io::IO, G::LocalGenusQuad{S, T, U}) where {S, T, U}
  if !isdyadic(G)
    for i in 1:length(G)
      print(io, "(", G.scales[i], ", ", G.ranks[i], ", ", G.detclasses[i], ")")
    end
  else
    for i in 1:length(G)
      print(io, "(", G.scales[i], ", ", G.ranks[i], ", ", G.normgens[i], ", ", G.weights[i], ", ", G.dets[i], ", ", G.witt[i], ")")
    end
  end
end

function Base.show(io::IO, ::MIME"text/plain", G::LocalGenusQuad{S, T, U}) where {S, T, U}
  p = prime(G)
  if !get(io, :compact, false)
    print(io, "Local quadratic genus for prime ")
    print(IOContext(io, :compact => true), p)

    if !isdyadic(p)
      print(io, " with respect to uniformizer ", uniformizer(G))
      print(io, "\n(scale, rank, determinant class)\n")
    else
      print(io, "\n(scale, rank, norm generator, weight, det, Witt)\n")
    end
  end
  if !isdyadic(G)
    for i in 1:length(G)
      print(io, "(", G.scales[i], ", ", G.ranks[i], ", ", G.detclasses[i], ")")
    end
  else
    for i in 1:length(G)
      print(io, "(", G.scales[i], ", ", G.ranks[i], ", ", G.normgens[i], ", ", G.weights[i], ", ", G.dets[i], ", ", G.witt[i], ")")
    end
  end
end

# Creation of non-dyadic genus symbol

function genus(::Type{QuadLat}, p, pi::nf_elem, ranks::Vector{Int},
                                                scales::Vector{Int},
                                                normclass::Vector{Int})
  @req !isdyadic(p) "Prime ideal must not be dyadic"
  K = nf(order(p))
  z = LocalGenusQuad{typeof(K), typeof(p), elem_type(K)}()
  z.p = p
  z.uniformizer = pi
  z.isdyadic = false
  z.ranks = ranks
  z.scales = scales
  z.detclasses = normclass
  return z
end

# Creation of dyadic genus symbols, with the f already computed

function genus(::Type{QuadLat}, p, ranks::Vector{Int}, scales::Vector{Int},
                                   weights::Vector{Int}, normgens::Vector{T},
                                   dets::Vector{T}, witt::Vector{Int},
                                   f::Vector{Int}) where {T}
  @req isdyadic(p) "Prime ideal must be dyadic"
  K = nf(order(p))
  z = LocalGenusQuad{typeof(K), typeof(p), elem_type(K)}()
  z.isdyadic = true
  z.p = p
  z.ranks = ranks
  z.scales = scales
  z.weights = weights
  z.normgens = normgens
  z.dets = dets
  z.witt = witt
  z.f = f
  return z
end

# Creation of dyadic genus symbols, without the f already computed
function genus(::Type{QuadLat}, p, ranks::Vector{Int}, scales::Vector{Int},
                                   weights::Vector{Int}, dets::Vector{T},
                                   normgens::Vector{T},
                                   witt::Vector{Int}) where {T}
  @req isdyadic(p) "Prime ideal must be dyadic"
  K = nf(order(p))
  z = LocalGenusQuad{typeof(K), typeof(p), elem_type(K)}()
  z.isdyadic = true
  z.p = p
  z.ranks = ranks
  z.scales = scales
  z.weights = weights
  z.normgens = normgens
  z.dets = dets
  z.witt = witt
  t = length(ranks)
  # I should do this only on demand ...
  uL = Int[valuation(normgens[i], p) for i in 1:t]
  wL = weights
  sL = scales
  aL = normgens
  _f = Vector{Int}()
  e = ramification_index(p) # absolute
  for k in 1:(t - 1)
    exp = uL[k] + uL[k + 1]
    push!(_f, (isodd(exp) ? exp : min(quadratic_defect(aL[k] * aL[k + 1], p), uL[k] + wL[k + 1], uL[k + 1] + wL[k], e + div(exp, 2) + sL[k])) - 2*sL[k])
  end
  z.f = _f
  return z
end

################################################################################
#
#  Equality of genus symbols
#
################################################################################

function Base.:(==)(G1::LocalGenusQuad, G2::LocalGenusQuad)
  if G1 === G2
    return true
  end

  if prime(G1) != prime(G2)
    return false
  end

  p = prime(G1)

  # Test if the rational spaces are equivalent
  if isdyadic(G1)
    # Could be sped up for low rank
    w1 = witt_invariant(G1)
    d1 = prod(nf_elem[G1.dets[i] for i in 1:length(G1)])
    n1 = rank(G1)
    #s1 = _witt_hasse(w1, n1, d1, p)

    w2 = witt_invariant(G2)
    d2 = prod(nf_elem[G2.dets[i] for i in 1:length(G2)])
    n2 = rank(G2)
    #s2 = _witt_hasse(w2, n2, d2, p)

    if n1 != n2
      return false
    end
    if w1 != w2
      return false
    end
    if !islocal_square(d1 * d2, p)
      return false
    end
  end

  if length(G1) != length(G2)
    return false
  end

  if ranks(G1) != ranks(G2) || scales(G1) != scales(G2)
    return false
  end

  if !isdyadic(G1.p)
    if G1.uniformizer == G2.uniformizer
      return G1.detclasses == G2.detclasses
    else
      q = divexact(G2.uniformizer, G1.uniformizer)
      fl = islocal_square(q, p)
      if fl
        return G1.detclasses == G2.detclasses
      else
        G2adj = Vector{Int}(undef, length(G2))
        for i in 1:length(G2)
          if isodd(G1.ranks[i] * G1.scales[i])
            G2[i] = -G2.detclasses[i]
          else
            G2[i] = G2.detclasses[i]
          end
        end
        return G1.detaclasses == G2adj
      end
    end
  end

  if ranks(G1) != ranks(G2) || scales(G1) != scales(G2) || weights(G1) != weights(G2)
    return false
  end

  r = length(G1.ranks)

  uL1 = norms(G1)
  uL2 = norms(G2)

  if uL1 != uL2
    return false
  end

  bL = nf_elem[divexact(G1.normgens[i], G2.normgens[i]) for i in 1:r]
  qL = Union{PosInf, Int}[quadratic_defect(bL[i], p) for i in 1:r]

  for k in 1:r
    if qL[k] < G1.weights[k] - uL2[k]
      return false
    end
  end

  e = ramification_index(p)

  aL1 = G1.normgens
  aL2 = G2.normgens

  d1 = nf_elem[prod(nf_elem[G1.dets[i] for i in 1:j]) for j in 1:r]
  d2 = nf_elem[prod(nf_elem[G2.dets[i] for i in 1:j]) for j in 1:r]

  for i in 1:(r - 1)
    detquot = divexact(d1[i], d2[i])
    if valuation(detquot, p) != 0
      return false
    end

    if quadratic_defect(detquot, p) < G1.f[i]
      return false
    end

    if G1.f[i] > 2 * e + uL1[i + 1] - G2.weights[i + 1]
      # We have to test if L1^(i) embeds into L2^(i) \perp aL2[i + 1]
      # So let's compute the Hasse invariant of those fields.
      haG1 = _witt_hasse(G1.witt[1], G1.ranks[1], G1.dets[1], p)
      _d1 = G1.dets[1]
      haG2 = _witt_hasse(G2.witt[1], G2.ranks[1], G2.dets[1], p)
      _d2 = G2.dets[1]
      ra = G1.ranks[1]

      for j in 2:i
        haG1 = haG1 * _witt_hasse(G2.witt[j], G1.ranks[j], G1.dets[j], p) * hilbert_symbol(_d1, G1.dets[j], p)
        _d1 = _d1 * G1.dets[j]
        haG2 = haG2 * _witt_hasse(G2.witt[j], G2.ranks[j], G2.dets[j], p) * hilbert_symbol(_d2, G2.dets[j], p)
        _d2 = _d2 * G2.dets[j]
        ra = ra + G1.ranks[j]
      end

      detsecondspace = _d2 * aL2[i + 1]
      hassesecondspace = haG2 * hilbert_symbol(_d2, aL2[i + 1], p)

      if !_can_locally_embed(r, _d1, haG1, r + 1, detsecondspace, hassesecondspace, p)
        return false
      end
    end

    if G1.f[i] > 2 * e + uL1[i] - G2.weights[i]
      # We have to test if L1^(i) embeds into L2^(i) \perp aL2[i]
      # So let's compute the Hasse invariant of those fields.
      haG1 = _witt_hasse(G1.witt[1], G1.ranks[1], G1.dets[1], p)
      _d1 = G1.dets[1]
      haG2 = _witt_hasse(G2.witt[1], G2.ranks[1], G2.dets[1], p)
      _d2 = G2.dets[1]
      ra = G1.ranks[1]

      for j in 2:i
        haG1 = haG1 * _witt_hasse(G2.witt[j], G1.ranks[j], G1.dets[j], p) * hilbert_symbol(_d1, G1.dets[j], p)
        _d1 = _d1 * G1.dets[j]
        haG2 = haG2 * _witt_hasse(G2.witt[j], G2.ranks[j], G2.dets[j], p) * hilbert_symbol(_d2, G2.dets[j], p)
        _d2 = _d2 * G2.dets[j]
        ra = ra + G1.ranks[j]
      end

      detsecondspace = _d2 * aL2[i]
      hassesecondspace = haG2 * hilbert_symbol(_d2, aL2[i], p)

      if !_can_locally_embed(r, _d1, haG1, r + 1, detsecondspace, hassesecondspace, p)
        return false
      end
    end
  end

  return true
end

function islocally_isometric(L::QuadLat, M::QuadLat, p::NfOrdIdl)
  fl = genus(L, p) == genus(M, p)
  @assert fl == islocally_isometric_kirschmer(L, M, p)
  return fl
end

function genus(L::QuadLat, p)
  pi, _sym, _weight, _normgen, _f, dets, witt, uL, J, G, E  = _genus_symbol(L, p)
  ranks = Int[d[1] for d in _sym]
  scales = Int[d[2] for d in _sym]

  if isdyadic(p)
    g = genus(QuadLat, p, ranks, scales, _weight, _normgen, dets, witt,  _f)
  else
    normclass = Int[d[3] for d in _sym]
    g = genus(QuadLat, p, pi, ranks, scales, normclass)
  end
  g.norms = uL
  g.jordec = JorDec(J, G, E, p)
  return g
end

function _genus_symbol(L::QuadLat, p)
  O = order(p)
  nf(O) != base_field(L) && throw(error("Prime ideal must be an ideal of the base field of the lattice"))
  K = nf(O)
  # If you pull from cache, you might have to adjust the symbol according
  # to the uniformizer flag

  J, G, E = jordan_decomposition(L, p)

  t = length(G)

  local pi::nf_elem

  if minimum(p) != 2
    _, _h = ResidueField(O, p)
    h = extend(_h, nf(O))
    _sym = Vector{Tuple{Int, Int, Int}}(undef, length(J))
    pi = elem_in_nf(uniformizer(p))
    for i in 1:t
      r = nrows(J[i])
      _sym[i] = (r, E[i], islocal_square(det(G[i])//pi^(r * E[i]), p) ? 1 : - 1)
    end
    _weight = Vector{Int}()
    _normgen = Vector{elem_type(K)}()
    _f = Int[]
    dets = elem_type(K)[det(G[i]) for i in 1:t]
    witt = Int[]
    uL = Int[]
    #Gs = [ h(prod(diagonal(G[i]))//unif^(E[i] * nrows(J[i]))) for i in 1:length(J)]
    #@assert !(0 in Gs)
    #x  = [ (nrows(J[i]), E[i], issquare(Gs[i])[1] ? 1 : -1) for i in 1:length(J)]
    #return LocalGenusSymbol{QuadLat}(p, x, unif, false, base_field(L), nothing, nothing)
  else
    sL = Int[ minimum(Union{PosInf, Int}[iszero(g[i, j]) ? inf : valuation(g[i, j], p) for j in 1:ncols(g) for i in 1:j]) for g in G]
    @assert sL == E
    _sym = Vector{Tuple{Int, Int, Int}}(undef, t)
    e = ramification_index(p)
    aL = elem_type(K)[]
    uL = Int[]
    wL = Int[]
    witt = Int[]
    dets = elem_type(K)[]
    unif = elem_in_nf(uniformizer(p))
    pi = zero(K)
    for i in 1:t
      _sym[i] = (nrows(J[i]), sL[i], 0)
      push!(dets, det(G[i]))
      push!(witt, witt_invariant(quadratic_space(K, G[i]), p))
      GG = diagonal_matrix(eltype(G)[ j < i ? unif^(2*(sL[i] - sL[j])) * G[j] : G[j] for j in 1:t])
      D = diagonal(GG)
      m, pos = findmin(Union{Int, PosInf}[iszero(d) ? inf : valuation(d, p) for d in D])
      if e + sL[i] <= m
        push!(aL, unif^(e + sL[i]))
      else
        push!(aL, D[pos])
      end
      push!(uL, valuation(aL[i], p))
      push!(wL, min(e + sL[i], minimum(Union{PosInf, Int}[uL[i] + quadratic_defect(d//aL[i], p) for d in D])))
    end
    _f = Int[]
    for k in 1:(t - 1)
      exp = uL[k] + uL[k + 1]
      push!(_f, (isodd(exp) ? exp : min(quadratic_defect(aL[k] * aL[k + 1], p), uL[k] + wL[k + 1], uL[k + 1] + wL[k], e + div(exp, 2) + sL[k])) - 2*sL[k])
    end
    _normgen = aL
    _weight = wL
  end
  return pi, _sym, _weight, _normgen, _f, dets, witt, uL, J, G, E
end

################################################################################
#
#  Gram matrix
#
################################################################################

function _Amatrix(K, a, b)
  z = zero_matrix(K, 2, 2)
  z[1, 1] = a
  z[2, 2] = b
  z[1, 2] = 1
  z[2, 1] = 1
  return z
end

function _special_unit_quad(p, m::Int = -1)
  @assert isdyadic(p)
  O = order(p)
  I = 4 * O
  B = elem_in_nf.(basis(I))
  z = rand(B, -2:2)
  e = valuation(4, p)
  while quadratic_defect(1 + m * z, p) != e
    z = rand(B, -2:2)
  end
  delta = 1 + m * z
  rho = divexact(z, 4)
  @assert valuation(rho, p) == 0
  return delta, rho
end

function _non_square(K, p)
  O = order(p)
  R, mR = ResidueField(O, p)
  u = elem_in_nf(mR\non_square(R))
  @assert !islocal_square(u, p)[1]
  return u
end

function representative(G::LocalGenusQuad)
  K = nf(order(G.p))
  return lattice(quadratic_space(K, gram_matrix(G.jordec)))
end

######

mutable struct LocalGenusSymbol{S}
  P
  data
  x
  iseven::Bool
  E
  isramified
  non_norm
end

prime(G::LocalGenusSymbol) = G.P

uniformizer(G::LocalGenusSymbol{QuadLat}) = G.x

data(G::LocalGenusSymbol) = G.data

base_field(G::LocalGenusSymbol) = G.E

function Base.show(io::IO, G::LocalGenusSymbol)
  print(io, "Local genus symbol (scale, rank, det) at\n")
  print(IOContext(io, :compact => true), G.P)
  compact = get(io, :compact, false)
  if !compact
    print(io, "\nwith base field\n")
    print(io, base_field(G))
  end
  println(io, "\nWith data ", data(G))
  !G.iseven ? println(io, "and unifomizer\n", G.x) : nothing
end

# TODO: I have to redo this

function _genus_symbol_kirschmer(L::QuadLat, p::NfOrdIdl; uniformizer = zero(order(p)))
  O = order(p)
  nf(O) != base_field(L) && throw(error("Prime ideal must be an ideal of the base field of the lattice"))
  # If you pull from cache, you might have to adjust the symbol according
  # to the uniformizer flag

  J, G, E = jordan_decomposition(L, p)
  if !iszero(uniformizer)
    unif = uniformizer
    if valuation(unif, p) != 1
      throw(error("Wrong uniformizer"))
    end
  else
    unif = elem_in_nf(Hecke.uniformizer(p))
  end

  if minimum(p) != 2
    _, _h = ResidueField(O, p)
    h = extend(_h, nf(O))
    Gs = [ h(prod(diagonal(G[i]))//unif^(E[i] * nrows(J[i]))) for i in 1:length(J)]
    @assert !(0 in Gs)
    x  = [ (nrows(J[i]), E[i], issquare(Gs[i])[1] ? 1 : -1) for i in 1:length(J)]
    return LocalGenusSymbol{QuadLat}(p, x, unif, false, base_field(L), nothing, nothing)
  else
    t = length(G)
    sL = [ minimum(iszero(g[i, j]) ? inf : valuation(g[i, j], p) for j in 1:ncols(g) for i in 1:j) for g in G]
    @assert sL == E
    e = ramification_index(p)
    aL = []
    uL = []
    wL = []
    for i in 1:t
      GG = diagonal_matrix([ j < i ? unif^(2*(sL[i] - sL[j])) * G[j] : G[j] for j in 1:t])
      D = diagonal(GG)
      m, pos = findmin(Union{PosInf, Int}[iszero(d) ? inf : valuation(d, p) for d in D])
      if e + sL[i] <= m
        push!(aL, unif^(e + sL[i]))
      else
        push!(aL, D[pos])
      end
      push!(uL, valuation(aL[i], p))
      push!(wL, min(e + sL[i], minimum(uL[i] + quadratic_defect(d//aL[i], p) for d in D)))
    end
    fL = []
    for k in 1:(t - 1)
      exp = uL[k] + uL[k + 1]
      push!(fL, (isodd(exp) ? exp : min(quadratic_defect(aL[k] * aL[k + 1], p), uL[k] + wL[k + 1], uL[k + 1] + wL[k], e + div(exp, 2) + sL[k])) - 2*sL[k])
    end
    return LocalGenusSymbol{QuadLat}(p, ([nrows(G[k]) for k in 1:t], sL, wL, aL, fL, G), unif, true, base_field(L), nothing, nothing)
  end
end

################################################################################
#
#  Enumeration of local Jordan decompositions and genera
#
################################################################################

# Find a_1,...,a_n in p^n such that for y in p^n we have
# y = a_i \mod p^m for some i. (\mod = the "quadratic" equivalence)
function _representatives_for_equivalence(p, n, m)
  @assert n <= m
  u = elem_in_nf(uniformizer(p))^n
  G, mG = local_multiplicative_group_modulo_squares(p)
  k = ngens(G)
  reps = typeof(u)[ u * mG(g) for g in G if iszero(g[k])]
  finer_reps = typeof(u)[reps[1]]
  for j in 2:length(reps)
    uu = reps[j]
    new = true
    for k in 1:length(finer_reps)
      if _is_equivalent_quadratic(uu, finer_reps[k], p, m)
        new = false
        break
      end
    end
    if new
      push!(finer_reps, uu)
    end
  end
  return finer_reps
end

function _representatives_for_equivalence_and_witt(p, n, m, c)
  @assert n <= m
  u = elem_in_nf(uniformizer(p))^n
  G, mG = local_multiplicative_group_modulo_squares(p)
  k = ngens(G)
  reps = typeof(u)[ u * mG(g) for g in G if iszero(g[k])]
  finer_reps = Tuple{typeof(u), Int}[(reps[1], hilbert_symbol(reps[1], reps[1] * c, p))]
  for j in 2:length(reps)
    uu = reps[j]
    new = true
    hi = hilbert_symbol(uu, uu * c, p)
    for k in 1:length(finer_reps)
      if _is_equivalent_quadratic(uu, finer_reps[k][1], p, m) && finer_reps[k][2] == hi
        new = false
        break
      end
    end
    if new
      push!(finer_reps, (uu, hi))
    end
  end
  return first.(finer_reps)::Vector{typeof(u)}
end

function _is_equivalent_quadratic(a, b, p, n)
  ap = valuation(a, p)
  if ap != valuation(b, p)
    return false
  end

  if quadratic_defect(divexact(a, b), p) >= n - ap
    return true
  end

  return false
end

# uni-unimodular, that is, determinant/discriminant equal to 1
function _unimodular_jordan_block(p, m)
  E = nf(order(p))
  e = ramification_index(p)
  @assert isdyadic(p)
  # weight, normgen, det, witt
  res = Vector{Tuple{Int, nf_elem, nf_elem, Int}}()
  
  G, mG = local_multiplicative_group_modulo_squares(p)
  pi = elem_in_nf(uniformizer(p))
  k = ngens(G)
  reps_squares = typeof(pi)[ mG(g) for g in G if iszero(g[k])]

  if isodd(m)
    r = div(m - 1, 2)
    # Norm is always 0
    if m == 1
      weights = Int[e]
    else
      weights = Int[ i for i in 0:e if isodd(i)] # I do the sieving because of the Witt invariant later
      if !isodd(e)
        push!(weights, e)
      end
    end

    # The only norm generator is d

    D = kummer_generator_of_local_unramified_quadratic_extension(p)
    invD = inv(D)

    for w in weights
      for d in reps_squares
        push!(res, (w, (-1)^r * d, d, 1))
        if w != e
          # If w != e, then also -1 is possible
          push!(res, (w, invD * (-1)^r * d, d, -1))
        end
      end
    end
  else
    r = div(m, 2)

    norms = collect(0:e)

    _find_special_class_dict = Dict{nf_elem, nf_elem}()

    __find_special_class = (x, p) -> get!(_find_special_class_dict, x, _find_special_class(x, p))

    mmod4 = mod(m, 4)

    for n in norms
      normgens = pi^n .* reps_squares

      if isodd(n) # odd norm
        _r = Int[ j for j in n:e if iseven(j) ]
        if isodd(e) && (length(_r) == 0 || _r[end] != e)
          push!(_r, e)
        end
      else # iseven(s[3])
        _r = Int[ j for j in n:e if isodd(j) ]
        if iseven(e) && (length(_r) == 0 || _r[end] != e)
          push!(_r, e)
        end
      end
      weights = _r

      a = gen(E)

      for w in weights
        for d in reps_squares
          if mmod4 == 0 || mmod4 == 1
            gamma = __find_special_class(d, p) - 1
            #@assert islocal_square(d//(1 + gamma), p)
            #@assert valuation(d, p) == valuation(1 + gamma, p)
            dis = d
          else
            gamma = __find_special_class(-d, p) - 1
            #@assert islocal_square(-d//(1 + gamma), p)
            #@assert valuation(-d, p) == valuation(1 + gamma, p)
            dis = -d
          end
          #@assert quadratic_defect(1 + gamma, p) == (iszero(gamma) ? inf : valuation(gamma, p))
          if !(iszero(gamma) || valuation(gamma, p) >= w + n)
            continue
          end
          
          if iseven(n + w)
            @assert w == e
          end

          # This is a good candidate for the determinant
          # It is not sufficient to look for 
          _normgens = _representatives_for_equivalence_and_witt(p, n, w, -dis)
          for ng in _normgens
            
            if r == 1 && isodd(w + n)
              if !(w == e || (e > w && !iszero(gamma) && w == valuation(gamma, p) - valuation(ng, p)))
                continue
              end
            end

            if (m == 2 && isodd(n + w))
              # A(\alpha, -\gamma \alpha^-1)
              wi = hilbert_symbol(ng, ng * -dis, p)
              push!(res, (w, ng, d, wi))
            elseif iseven(n + w)
              wi = hilbert_symbol(ng, ng * -dis, p)
              push!(res, (w, ng, d, wi))
            else
              push!(res, (w, ng, d, 1))
              push!(res, (w, ng, d, -1))
            end
          end
        end
      end
    end
  end
  return res
end

@doc Markdown.doc"""
    local_jordan_decomposition(E::NumField, p; rank::Int
                                               det_val::Int
                                               max_scale::Int)

Given a prime ideal $\mathfrak p$, returns all abstract Jordan decompositions
of rank `r` with determinant valuation `det_val` and scales of the blocks
bounded by `max_scale`.
"""
function local_jordan_decompositions(E, p; rank::Int, det_val::Int, max_scale = nothing)
  local _max_scale::Int

  if max_scale === nothing
    _max_scale = det_val
  else
    _max_scale = max_scale
  end

  scales_rks = Vector{Tuple{Int, Int}}[]

  for rkseq in _integer_lists(rank, _max_scale + 1)
    d = 0
    pgensymbol = Tuple{Int, Int}[]
    for i in 0:(_max_scale + 1) - 1
      d += i * rkseq[i + 1]
      if rkseq[i + 1] != 0
        push!(pgensymbol, (i, rkseq[i + 1]))
      end
    end
    if d == det_val
        push!(scales_rks, pgensymbol)
    end
  end

  res = JorDec{typeof(E), typeof(p), elem_type(E)}[]

  if !isdyadic(p)
    ns = _non_square(E, p)  
    u = elem_in_nf(uniformizer(p))
    for scalerank in scales_rks
      class1 = elem_type(E)[u^(s[1] * s[2]) for s in scalerank]
      class2 = elem_type(E)[ns * u^(s[1] * s[2]) for s in scalerank]
      l = length(scalerank)
      @assert l <= sizeof(UInt) * 8
      # I need to compute all possiblities to distribute class1/class2
      # among the blocks.
      t = zero(UInt)
      for i in 1:2^l
        v = Vector{elem_type(E)}(undef, l)
        for j in 1:l
          if Bool((t >> (j - 1)) & 1)
            v[j] = class1[j]
          else
            v[j] = class2[j]
          end
        end
        push!(res, JorDec(p, Int[s[1] for s in scalerank], Int[s[2] for s in scalerank], v))
        t += 1
      end
    end
    return res
  else
    G, mG = local_multiplicative_group_modulo_squares(p)
    pi = elem_in_nf(uniformizer(p))
    k = ngens(G)
    reps_squares = typeof(pi)[ mG(g) for g in G if iszero(g[k])]
    @assert all(valuation(u, p) == 0 for u in reps_squares)

    e = ramification_index(p)

    # collect the possible ranks

    possible_ranks = unique!(reduce(vcat, Vector{Int}[[r[2] for r in s] for s in scales_rks]))

    decs_per_rank = Dict{Int, Vector{Tuple{Int, nf_elem, nf_elem, Int}}}()

    for m in possible_ranks
      decs_per_rank[m] = _unimodular_jordan_block(p, m)
    end

    for sr in scales_rks
      it = Iterators.product([decs_per_rank[r] for (s, r) in sr]...)
      for local_blocks in it
        # local blocks in form weight, normgen, det, witt
        # JorDec(p, sc::Vector{Int},
        #           rks::Vector{Int},
        #           normgens::Vector{nf_elem},
        #           weights::Vector{Int},
        #           dets::Vector{nf_elem},
        #           witts::Vector{Int}) 

        l = length(sr)
        J = JorDec(p, Int[s[1] for s in sr],
                      Int[s[2] for s in sr],
                      nf_elem[pi^sr[i][1] * local_blocks[i][2] for i in 1:l],
                      Int[sr[i][1] + local_blocks[i][1] for i in 1:l],
                      nf_elem[pi^(sr[i][1] * sr[i][2]) * local_blocks[i][3] for i in 1:l],
                      Int[isodd(sr[i][2]) ? local_blocks[i][4] : local_blocks[i][4] * hilbert_symbol(pi^sr[i][1], (-1)^divexact(sr[i][2]*(sr[i][2] - 1), 2) * pi^(sr[i][1] * sr[i][2]) * local_blocks[i][3], p) for i in 1:l])
        push!(res, J)
      end
    end
    return res
    #for srwndw in scales_rks_norms_weights_normgens_dets_witts
    #  push!(res, JorDec(p, Int[s[1] for s in srwndw], Int[s[2] for s in srwndw], nf_elem[pi^s[1] * s[5] for s in srwndw], Int[s[1] + s[4] for s in srwndw], nf_elem[pi^(s[1] * s[2]) * s[6] for s in srwndw], Int[isodd(s[2]) ? s[7] : s[7] * hilbert_symbol(pi^s[1], (-1)^divexact(s[2]*(s[2] - 1), 2) * pi^(s[1] * s[2]) * s[6], p) for s in srwndw]))
    #end
    #return res
  end
end


function local_genera_quadratic(K, p; rank::Int, det_val::Int, max_scale = nothing)
  J = local_jordan_decompositions(K, p, rank = rank, det_val = det_val, max_scale = max_scale)
  res = local_quadratic_genus_type(K)[]
  for j in J
    g = genus(j)
    if !(g in res)
      push!(res, g)
    end
  end
  return res
end

################################################################################
#
#  Global genus
#
################################################################################

mutable struct GenusQuad{S, T, U}
  K::S
  primes::Vector{T}
  LGS::Vector{LocalGenusQuad{S, T, U}}
  rank::Int
  signatures::Dict{InfPlc, Int}
  d::U
  space

  function GenusQuad{S, T, U}(K) where {S, T, U}
    z = new{typeof(K), ideal_type(order_type(K)), elem_type(K)}()
    z.rank = -1
    return z
  end
end

genus_quad_type(K) = GenusQuad{typeof(K), ideal_type(order_type(K)), elem_type(K)}

function GenusQuad(K, d, LGS, signatures)
  z = genus_quad_type(K)(K)
  z.LGS = LGS
  z.signatures = signatures
  z.d = d
  z.rank = rank(LGS[1])
  z.primes = [prime(g) for g in LGS]
  z.K = K
  return z
end

function genus(L::QuadLat)
  bad = bad_primes(L, even = true)
  S = real_places(base_field(L))
  D = diagonal(rational_span(L))
  signatures = Dict{InfPlc, Int}(s => count(d -> isnegative(d, s), D) for s in S)
  return GenusQuad(base_field(L), prod(D), [genus(L, p) for p in bad], signatures)
end

function Base.:(==)(G1::GenusQuad, G2::GenusQuad)
  if G1.K != G2.K
    return false
  end

  if length(G1.primes) != length(G2.primes)
    return false
  end

  if G1.signatures != G2.signatures
    return false
  end

  for g1 in G1.LGS
    p1 = prime(g1)
    found = false
    for g2 in G2.LGS
      p2 = prime(g2)
      if p1 == p2
        found = true
        if g1 != g2
          return false
        end
        break
      end
    end
    if !found
      return false
    end
  end

  return true
end

primes(G::GenusQuad) = G.primes

function genera_quadratic(K; rank::Int, signatures, det)
  OK = maximal_order(K)

  _max_scale = 2 * det

  primes = support(2 * det)

  local_symbols = Vector{local_quadratic_genus_type(K)}[]

  ms = _max_scale
  ds = det
  for p in primes
    det_val = valuation(ds, p)
    mscale_val = valuation(ms, p)
    push!(local_symbols, local_genera_quadratic(K, p, rank = rank, det_val = det_val, max_scale = mscale_val))
  end

  res = genus_quad_type(K)[]
  it = Iterators.product(local_symbols...)
  for gs in it
    c = collect(gs)::Vector{local_quadratic_genus_type(K)}
    de = _possible_determinants(K, c, signatures)::Vector{nf_elem}
    for d in de
      b = _check_global_quadratic_genus(c, d, signatures)
      if b
        push!(res, GenusQuad(K, d, c, signatures))
      end
    end
  end

  return res
end

function _check_global_quadratic_genus(c, d, signatures)
  # c = vector or tuple of local quadratic genera
  # signatures = dict{pl => n}
  P = [ i for i in 1:length(c) if hasse_invariant(c[i]) == -1]
  if rank(c[1]) == 1 && length(P) == 0
    return false
  end

  if rank(c[1]) == 2
    for i in P
      #@show islocal_square(-d, prime(c[i]))
      if islocal_square(-d, prime(c[i]))
        return false
      end
    end
  end

  s = length([ s for (s, n) in signatures if (n % 4) in [2, 3]])
  return iseven(length(P) + s)
end

function _possible_determinants(K, local_symbols, signatures)
  # This is probably independent of the local symbol?
  C, mC = class_group(K)
  if length(local_symbols) == 0
    OK = maximal_order(K)
  else
    OK = order(prime(local_symbols[1]))
  end
  I = 1 * OK
  for g in local_symbols
    I = I * prime(g)^valuation(det(g), prime(g))
  end
  classofI = mC\(I)
  U, mU = unit_group_fac_elem(OK)
  classes = elem_type(C)[]
  for c in C
    if iszero(classofI + 2 * c)
      push!(classes, c)
    end
  end
  s = ideal_type(OK)[]
  current_classes = elem_type(C)[]
  primes = PrimeIdealsSet(OK, 2, -1)

  if id(C) in classes
    push!(s, 1 * OK)
    push!(current_classes, id(C))
  end

  for P in primes
    if length(classes) == length(current_classes)
      break
    end

    c = mC\(P)
    if c in current_classes
      continue
    end

    if c in classes
      push!(current_classes, c)
      push!(s, P)
    end
  end
  rlp = real_places(K)
  local R::GrpAbFinGen
  R, _exp, _log = infinite_primes_map(OK, rlp, 1 * OK)
  tar = R(Int[isodd(signatures[sigma]) ? 1 : 0 for sigma in rlp])
  gensU = gens(U)
  S, mS = sub(R, elem_type(R)[_log(mU(u)) for u in gensU], false)
  # I need totally positive units / OK^*2
  Q, mQ = quo(U, 2, false)
  f = hom(Q, R, elem_type(R)[_log(mU(mQ\u)) for u in gens(Q)])
  Ker, mKer = kernel(f)
  transver = elem_type(K)[ evaluate(mU(mQ\(mKer(k)))) for k in Ker]

  dets = elem_type(K)[]

  for P in s
    J = I * P^2
    fl, u = isprincipal(J)
    @assert fl
    # I need to change u such that sign(u, sigma) = (-1)^signatures[sigma]
    v = _log(elem_in_nf(u)) + tar
    fl, y = haspreimage(mS, v)
    if fl
      z = elem_in_nf(u) * prod(elem_type(K)[ evaluate(mU(gensU[i]))^y.coeff[i] for i in 1:length(gensU)])
      @assert z * OK == J
      @assert all(sigma -> sign(z, sigma) == (-1)^signatures[sigma], rlp)
      for t in transver
        possible_det = z * t
        good = true
        for g in local_symbols
          # I need to test if the determinant is locally correct
          if !islocal_square(possible_det * det(g), prime(g))
            good = false
            break
          end
        end
        if good
          push!(dets, possible_det)
        end
      end
    end
  end
  return dets
end

function quadratic_space(G::GenusQuad)
  if isdefined(G, :space)
    return G.space::quadratic_space_type(G.K)
  end

  c = G.LGS
  K = G.K
  P = ideal_type(order_type(K))[ prime(c[i]) for i in 1:length(c) if hasse_invariant(c[i]) == -1]
  d = G.d
  signa = G.signatures
  rk = G.rank
  G.space = quadratic_space(G.K, _quadratic_form_with_invariants(rk, d, P, signa))
  return G.space::quadratic_space_type(G.K)
end

################################################################################
#
#  Representative
#
################################################################################

function representative(G::GenusQuad)
  K = G.K
  OK = order(primes(G)[1])
  # Let's follow the Lorch paper. This is also how we do it in the Hermitian case.
  V = quadratic_space(G)
  M = maximal_integral_lattice(V)
  for g in G.LGS
    p = prime(g)
    @vprint :Lattice 1 "Finding representative for $g at $(prime(g))...\n"
    L = representative(g)
    M = find_lattice(M, L, p)
    @assert islocally_isometric(M, L, p)
  end
  return M
end

function find_lattice(M::QuadLat, L::QuadLat, p)
  k, h = ResidueField(order(p), p)
  m = rank(M)
  chain = typeof(L)[ L ]
  ok, LL = ismaximal_integral(L, p)
  E = nf(order(p))
  while !ok
    push!(chain, LL)
    ok, LL = ismaximal_integral(LL, p)
  end
  pop!(chain)
  LL = M
  reverse!(chain)
  for X in chain 
    BM = local_basis_matrix(LL, p, type = :submodule)
    pM = _module_scale_ideal(pseudo_matrix(LL), fractional_ideal(order(p), p))
    while true
      v = [ rand(k) for i in 1:m ]
      while all(i -> iszero(v[i]), 1:m)
        v = [ rand(k) for i in 1:m ]
      end
      _, KM = kernel(matrix(k, length(v), 1, v), side = :left)
      KM = map_entries(x -> E(h\x), KM)
      _new_pmat = _sum_modules(pseudo_matrix(KM * BM), pM)
      LL = lattice(ambient_space(M), _new_pmat)
      if islocally_isometric(X, LL, p)
        break
      end
    end
  end
  @assert islocally_isometric(L, LL, p)
  return LL
end

function representatives(G::GenusQuad)
  return genus_representatives(representative(G))
end
