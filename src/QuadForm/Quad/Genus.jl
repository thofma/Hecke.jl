################################################################################
#
#  Abstract Jordan decomposition
#
################################################################################

function JorDec(p, scales::Vector{Int}, ranks::Vector{Int}, dets::Vector{AbsSimpleNumFieldElem})
  K = nf(order(p))
  _weight = Vector{Int}()
  _normgen = Vector{elem_type(K)}()
  _f = Int[]
  witt = Int[]
  z = JorDec{typeof(K), typeof(p), elem_type(K)}()
  z.is_dyadic = is_dyadic(p)
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

function show(io::IO, ::MIME"text/plain", J::JorDec)
  io = pretty(io)
  println(io, "Jordan decomposition for quadratic lattices")
  print(io, Indent(), "over ", Lowercase())
  Base.show(io, MIME"text/plain"(), order(J.p))
  println(io, Dedent())
  println(IOContext(io, :compact => true), "Prime ideal: ", J.p)
  if length(J) in [0,1]
    print(io, "Jordan block ")
  else
    print(io, "Jordan blocks ")
  end
  if is_dyadic(J.p)
    print(io, "(scale, rank, norm generator, weight, det, Witt):")
  else
    print(io, "(scale, rank, determinant class):")
  end
  print(io, Indent())
  if length(J) == 0
    nothing
  elseif !is_dyadic(J.p)
    println(io)
    for i in 1:length(J)-1
      println(io, "(", J.ranks[i], ", ", J.scales[i], ", ", J.dets[i], ")")
    end
    print(io, "(", J.ranks[end], ", ", J.scales[end], ", ", J.dets[end], ")")
  else
    println(io)
    for i in 1:length(J)-1
      println(io, "(", J.scales[i], ", ", J.ranks[i], ", ", J.normgens[i], ", ", J.weights[i], ", ", J.dets[i], ", ", J.witt[i], ")")
    end
    print(io, "(", J.scales[end], ", ", J.ranks[end], ", ", J.normgens[end], ", ", J.weights[end], ", ", J.dets[end], ", ", J.witt[end], ")")
  end
  print(io, Dedent())
end

function Base.show(io::IO, J::JorDec)
  p = J.p
  if is_terse(io)
    if length(J) == 0
      print(io, "Empty Jordan decomposition")
    else
      print(IOContext(io, :compact => true), p, ": ")
      if !is_dyadic(p)
        for i in 1:length(J)
          print(io, "(", J.scales[i], ", ", J.ranks[i], ", ", J.dets[i], ")")
        end
      else
        for i in 1:length(J)
          print(io, "(", J.scales[i], ", ", J.ranks[i], ", ", J.normgens[i], ", ", J.weights[i], ", ", J.dets[i], ", ", J.witt[i], ")")
        end
      end
    end
  else
    print(io, "Jordan decomposition for quadratic lattices over the ", absolute_minimum(J.p), "-adic integers")
  end
end

length(J::JorDec) = length(J.ranks)

function JorDec(p, sc::Vector{Int}, rks::Vector{Int}, normgens::Vector{AbsSimpleNumFieldElem}, weights::Vector{Int}, dets::Vector{AbsSimpleNumFieldElem}, witts::Vector{Int})
  K = nf(order(p))
  z = JorDec{typeof(K), typeof(p), elem_type(K)}()
  z.is_dyadic = is_dyadic(p)
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
  _, _h = residue_field(O, p)
  h = extend(_h, K)
  if !is_dyadic(p)
    dets = elem_type(K)[det(G[i]) for i in 1:t]
    _weight = Vector{Int}()
    _normgen = Vector{elem_type(K)}()
    _f = Int[]
    witt = Int[]
    #Gs = [ h(prod(diagonal(G[i]))//unif^(E[i] * nrows(J[i]))) for i in 1:length(J)]
    #@assert !(0 in Gs)
    #x  = [ (nrows(J[i]), E[i], is_square(Gs[i])[1] ? 1 : -1) for i in 1:length(J)]
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
  z.is_dyadic = is_dyadic(p)
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

@doc raw"""
    gram_matrix(J::JorDec, i::Int) -> MatElem

Given an abstract Jordan decomposition $J$ and $i$, return the Gram matrix of
of the $i$-th block of $J$.
"""
function gram_matrix(J::JorDec, i::Int)
  @req 1 <= i <= length(J) "Index ($i) must be in range 1:$(length(J))"
  p = J.p
  if J.is_dyadic
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
    @assert begin L = quadratic_lattice(nf(order(p)), gram = z); witt_invariant(L, p) == winew end

    @assert valuation(det(z), p) == 0
    zz = pi^s * z
    if wi < 2
      @assert begin L = quadratic_lattice(nf(order(p)), gram = zz); witt_invariant(L, p) == wi end
    end
    return zz
  else
    r = J.ranks[i]
    s = J.scales[i]
    z = identity_matrix(J.K, r)
    pi = elem_in_nf(uniformizer(p))
    q = J.dets[i]//pi^(r * s)
    @assert valuation(q, p) == 0
    if is_local_square(pi^(r * s) * J.dets[i], p)
      z[r, r] = one(parent(pi))
    else
      z[r, r] = _non_square(J.K, p)
    end
    return pi^s * z
  end
end

@doc raw"""
    gram_matrix(J::JorDec) -> MatElem

Given an abstract Jordan decomposition, return the Gram matrix of a lattice
admitting this Jordan decomposition.
"""
function gram_matrix(J::JorDec)
  K = J.K
  if length(J) > 0
    D = diagonal_matrix(dense_matrix_type(K)[gram_matrix(J, i) for i in 1:length(J)])
  else
    D = zero_matrix(K, 0, 0)
  end
  return D
end

@doc raw"""
    lattice(J::JorDec) -> MatElem

Given an abstract Jordan decomposition, return a lattice admitting this Jordan
decomposition.
"""
function lattice(J::JorDec)
  return quadratic_lattice(J.K, gram = gram_matrix(J))
end

@doc raw"""
    genus(J::JorDec) -> QuadLocalGenus

Given an abstract Jordan decomposition, return the local genus to which the
corresponding matrix belongs.
"""
function genus(J::JorDec)
  r = length(J.ranks)
  sca = J.scales
  p = J.p
  pi = elem_in_nf(uniformizer(p))
  if !is_dyadic(p)
    detclass = Int[]
    for i in 1:length(J.ranks)
      push!(detclass, is_local_square(J.dets[i]//pi^(J.ranks[i] * J.scales[i]), p) ? 1 : -1)
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
      # Also, there is some redundancy here, the z is actually independent of i
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
  g.jordec = J
  return g
end

function direct_sum(J1::JorDec{S, T, U}, J2::JorDec{S, T, U}) where {S, T, U}
  @req J1.p === J2.p "Jordan decompositions must be over same prime"
  if !(J1.is_dyadic)
    i1 = 1
    i2 = 1
    _sca = Int[]
    _rk = Int[]
    _dets = U[]
    while i1 <= length(J1) && i2 <= length(J2)
      if J1.scales[i1] < J2.scales[i2]
        push!(_sca, J1.scales[i1])
        push!(_rk, J1.ranks[i1])
        push!(_dets, J1.dets[i1])
        i1 += 1
      elseif J2.scales[i2] < J1.scales[i1]
        push!(_sca, J2.scales[i2])
        push!(_rk, J2.ranks[i2])
        push!(_dets, J2.dets[i2])
        i2 += 1
      else
        push!(_sca, J1.scales[i1])
        push!(_rk, J1.ranks[i1] + J2.ranks[i2])
        push!(_dets, J1.dets[i1] * J2.dets[i2])
        i1 += 1
        i2 += 1
      end
    end

    if i1 <= length(J1)
      append!(_sca, J1.scales[i1:length(J1)])
      append!(_rk, J1.ranks[i1:length(J1)])
      append!(_dets, J1.dets[i1:length(J1)])
    end

    if i2 <= length(J2)
      append!(_sca, J2.scales[i2:length(J2)])
      append!(_rk, J2.ranks[i2:length(J2)])
      append!(_dets, J2.dets[i2:length(J2)])
    end

    return JorDec(J1.p, _sca, _rk, _dets)
  else
    # Lazy
    return JorDec(direct_sum(lattice(J1), lattice(J2))[1], J1.p)
  end
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
      @assert is_local_square(d//(1 + gamma), p)
      @assert valuation(d, p) == valuation(1 + gamma, p)
    else
      gamma = _find_special_class(-d, p) - 1
      @assert is_local_square(-d//(1 + gamma), p)
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
      error("This should not happen")
    end
  end
end

################################################################################
#
#  Local genus symbol
#
################################################################################

local_genus_quad_type(K) = QuadLocalGenus{typeof(K), ideal_type(order_type(K)), elem_type(K)}

function in(L::QuadLat, G::QuadLocalGenus)
  return genus(L, prime(G)) == G
end

# Access
prime(G::QuadLocalGenus) = G.p

length(G::QuadLocalGenus) = length(G.ranks)

scales(G::QuadLocalGenus) = G.scales

ranks(G::QuadLocalGenus) = G.ranks

dets(G::QuadLocalGenus) = G.detclasses

weights(G::QuadLocalGenus) = G.weights

scale(G::QuadLocalGenus, i::Int) = scales(G)[i]

rank(G::QuadLocalGenus, i::Int) = ranks(G)[i]

base_field(G::QuadLocalGenus) = nf(prime(G))

function witt_invariant(G::QuadLocalGenus)
  if G.witt_inv != 0
    return G.witt_inv
  end

  p = prime(G)

  @assert is_dyadic(p)

  w, d, n = G.witt[1], G.dets[1], G.ranks[1]

  for i in 2:length(G)
    d, w, n = _witt_of_direct_sum(d, w, n, G.dets[i], G.witt[i], G.ranks[i], p)
  end

  G.witt_inv = w

  return w
end

function rank(G::QuadLocalGenus)
  if G.rank != 0
    return G.rank
  end

  rk = sum(G.ranks, init=0)

  G.rank = rk
  return rk
end

function det(G::QuadLocalGenus)
  if isdefined(G, :det)
    return G.det
  end

  if isdefined(G, :dets)
    d = prod(G.dets, init = one(nf(order(G.p))))
    G.det = d
  else
    pi = uniformizer(G)
    d = reduce(*, AbsSimpleNumFieldElem[pi^(G.ranks[i] * G.scales[i]) * G.detclasses[i] for i in 1:length(G)], init = one(nf(order(G.p))))
    G.det = d
  end
  return d
end

function det(G::QuadLocalGenus, i::Int)
  #if is_dyadic(G)
    return G.dets[i]
  #else
  #  pi = uniformizer(G)
  #  return pi^(G.ranks[i] * G.scales[i]) * G.detclasses[i]
  #end
end

function hasse_invariant(G::QuadLocalGenus)
  if rank(G) == 0
    return 1
  end
  if is_dyadic(G)
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

function uniformizer(G::QuadLocalGenus)
  @req !is_dyadic(G) "Genus symbol must not be dyadic"
  return G.uniformizer
end

is_dyadic(G::QuadLocalGenus) = G.is_dyadic

function norm_generators(G::QuadLocalGenus)
  @req is_dyadic(G) "Genus symbol must be dyadic"
  return G.normgens
end

function norms(G::QuadLocalGenus)
  @req is_dyadic(G) "Genus symbol must be dyadic"
  if !isdefined(G, :norms)
    p = prime(G)
    G.norms = Int[valuation(a, p) for a in norm_generators(G)]
    return G.norms
  else
    return G.norms
  end
end

function jordan_decomposition(g::QuadLocalGenus)
  if isdefined(g,:jordec)
    j = g.jordec
  elseif rank(g) == 0
    j = JorDec(g.p, Int[], Int[], AbsSimpleNumFieldElem[])
    g.jordec = j
    return j
  else
    # We don't know how to determine the Jordan decomposition
    # directly from the fundamental invariants. We just list all
    # possible jordan decompositions.
    # TODO: We could do it in the good case
    possible_jdec = _local_jordan_decompositions(number_field(order(g.p)),
                                                 g.p,
                                                 collect(zip(g.scales, g.ranks)))
    for j in possible_jdec
      if genus(j) == g
        g.jordec = j
        return j
      end
    end
  end
  return j
end

function show(io::IO, ::MIME"text/plain", G::QuadLocalGenus)
  p = prime(G)
  io = pretty(io)
  println(io, "Local genus symbol for quadratic lattices")
  print(io, Indent(),  "over ", Lowercase())
  Base.show(io, MIME"text/plain"(), order(p))
  println(io, Dedent())
  println(IOContext(io, :compact => true), "Prime ideal: ", p)
  if !is_dyadic(p)
    println(io, "Unifomizer: ", uniformizer(G))
  end
  if length(G) in [0,1]
    print(io, "Jordan block ")
  else
    print(io, "Jordan blocks ")
  end
  if !is_dyadic(p)
    print(io, "(scale, rank, determinant class):")
  else
    print(io, "(scale, rank, norm generator, weight, det, Witt):")
  end
  print(io, Indent())
  if length(G) == 0
    nothing
  elseif !is_dyadic(G)
    println(io)
    for i in 1:length(G)-1
      println(io, "(", G.scales[i], ", ", G.ranks[i], ", ", G.detclasses[i], ")")
    end
    print(io, "(", G.scales[end], ", ", G.ranks[end], ", ", G.detclasses[end], ")")
  else
    println(io)
    for i in 1:length(G)-1
      println(io, "(", G.scales[i], ", ", G.ranks[i], ", ", G.normgens[i], ", ", G.weights[i], ", ", G.dets[i], ", ", G.witt[i], ")")
    end
    print(io, "(", G.scales[end], ", ", G.ranks[end], ", ", G.normgens[end], ", ", G.weights[end], ", ", G.dets[end], ", ", G.witt[end], ")")
  end
  print(io, Dedent())
end

function Base.show(io::IO, G::QuadLocalGenus)
  if is_terse(io)
    if length(G) == 0
      print(io, "Empty local quadratic genus")
    elseif !is_dyadic(G)
      for i in 1:length(G)
        print(io, "(", G.scales[i], ", ", G.ranks[i], ", ", G.detclasses[i], ")")
      end
    else
      for i in 1:length(G)
        print(io, "(", G.scales[i], ", ", G.ranks[i], ", ", G.normgens[i], ", ", G.weights[i], ", ", G.dets[i], ", ", G.witt[i], ")")
      end
    end
  else
    print(io, "Local genus symbol for quadratic lattices over the ", absolute_minimum(prime(G)), "-adic integers")
  end
end

# Creation of non-dyadic genus symbol

function genus(::Type{QuadLat}, p, pi::AbsSimpleNumFieldElem, ranks::Vector{Int},
                                                scales::Vector{Int},
                                                normclass::Vector{Int})
  @req !is_dyadic(p) "Prime ideal must not be dyadic"
  K = nf(order(p))
  z = QuadLocalGenus{typeof(K), typeof(p), elem_type(K)}()
  z.p = p
  z.uniformizer = pi
  z.is_dyadic = false
  keep = [i for (i,k) in enumerate(ranks) if k != 0]  # We only keep the blocks with non zero rank
  z.ranks = ranks[keep]
  z.scales = scales[keep]
  z.detclasses = normclass[keep]
  return z
end

# Creation of dyadic genus symbols, with the f already computed

function genus(::Type{QuadLat}, p, ranks::Vector{Int}, scales::Vector{Int},
                                   weights::Vector{Int}, normgens::Vector{T},
                                   dets::Vector{T}, witt::Vector{Int},
                                   f::Vector{Int}) where {T}
  @req is_dyadic(p) "Prime ideal must be dyadic"
  K = nf(order(p))
  z = QuadLocalGenus{typeof(K), typeof(p), elem_type(K)}()
  z.is_dyadic = true
  z.p = p
  keep = [i for (i,k) in enumerate(ranks) if k != 0]   # We only keep the blocks with non zero rank
  z.ranks = ranks[keep]
  z.scales = scales[keep]
  z.weights = weights[keep]
  z.normgens = normgens[keep]
  z.dets = dets[keep]
  z.witt = witt[keep]
  z.f = f
  return z
end

# Creation of dyadic genus symbols, without the f already computed
function genus(::Type{QuadLat}, p, ranks::Vector{Int}, scales::Vector{Int},
                                   weights::Vector{Int}, dets::Vector{T},
                                   normgens::Vector{T},
                                   witt::Vector{Int}) where {T}
  @req is_dyadic(p) "Prime ideal must be dyadic"
  K = nf(order(p))
  z = QuadLocalGenus{typeof(K), typeof(p), elem_type(K)}()
  z.is_dyadic = true
  z.p = p
  keep = [i for (i,k) in enumerate(ranks) if k != 0]   # We only keep the blocks with non zero rank
  z.ranks = ranks[keep]
  z.scales = scales[keep]
  z.weights = weights[keep]
  z.normgens = normgens[keep]
  z.dets = dets[keep]
  z.witt = witt[keep]
  t = length(ranks[keep])
  # I should do this only on demand ...
  uL = Int[valuation(normgens[i], p) for i in keep]
  wL = weights[keep]
  sL = scales[keep]
  aL = normgens[keep]
  _f = Vector{Int}()
  e = ramification_index(p) # absolute
  for k in 1:(t - 1)
    exp = uL[k] + uL[k + 1]
    push!(_f, (isodd(exp) ? exp : min(quadratic_defect(aL[k] * aL[k + 1], p), uL[k] + wL[k + 1], uL[k + 1] + wL[k], e + div(exp, 2) + sL[k])) - 2*sL[k])
  end
  z.f = _f
  return z
end

# creation of rank zero genus symbol
function genus(::Type{QuadLat}, p)
  if is_dyadic(p)
    T = elem_type(nf(order(p)))
    return genus(QuadLat, p, Int[], Int[], Int[], T[], T[], Int[])
  else
    return genus(QuadLat, p, elem_in_nf(uniformizer(p)), Int[], Int[], Int[])
  end
end

################################################################################
#
#  Equality of genus symbols and hashes
#
################################################################################

function Base.hash(g::QuadLocalGenus, u::UInt)
  u = Base.hash(base_field(g), u)   # We only compare local symbols over the same parent base field
  u = Base.hash(prime(g), u)
  # In any case, equal local symbols should have some ranks and scale valuations
  h = xor(hash(scales(g)), hash(ranks(g)))
  # In the non-dyadic case, there is no obvious invariant we can compare more.
  # For the dyadic case, weights, witt invariants and norms should be the same,
  # according to the next equality test. Then, there is no other invariants we
  # can attach to the local genus. (because local genera with different
  # uniformizer can be equal under certain conditions, for instance).
  if is_dyadic(g)
    h = xor(h, hash(weights(g)))
    h = xor(h, hash(witt_invariant(g)))
    h = xor(h, hash(norms(g)))
  end
  return xor(h, u)
end

function Base.:(==)(G1::QuadLocalGenus, G2::QuadLocalGenus)
  if G1 === G2
    return true
  end

  if prime(G1) != prime(G2)
    return false
  end

  p = prime(G1)

  # Test if the rational spaces are isometric
  if is_dyadic(G1)
    # Could be sped up for low rank
    w1 = witt_invariant(G1)
    d1 = prod(AbsSimpleNumFieldElem[G1.dets[i] for i in 1:length(G1)])
    n1 = rank(G1)
    #s1 = _witt_hasse(w1, n1, d1, p)

    w2 = witt_invariant(G2)
    d2 = prod(AbsSimpleNumFieldElem[G2.dets[i] for i in 1:length(G2)])
    n2 = rank(G2)
    #s2 = _witt_hasse(w2, n2, d2, p)

    if n1 != n2
      return false
    end
    if w1 != w2
      return false
    end
    if !is_local_square(d1 * d2, p)
      return false
    end
  end

  if length(G1) != length(G2)
    return false
  end

  if ranks(G1) != ranks(G2) || scales(G1) != scales(G2)
    return false
  end

  if !is_dyadic(G1.p)
    if G1.uniformizer == G2.uniformizer
      return G1.detclasses == G2.detclasses
    else
      q = divexact(G2.uniformizer, G1.uniformizer)
      fl = is_local_square(q, p)
      if fl
        return G1.detclasses == G2.detclasses
      else
        G2adj = Vector{Int}(undef, length(G2))
        for i in 1:length(G2)
          if isodd(G1.ranks[i] * G1.scales[i])
            G2adj[i] = -G2.detclasses[i]
          else
            G2adj[i] = G2.detclasses[i]
          end
        end
        return G1.detclasses == G2adj
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

  bL = AbsSimpleNumFieldElem[divexact(G1.normgens[i], G2.normgens[i]) for i in 1:r]
  qL = Union{PosInf, Int}[quadratic_defect(bL[i], p) for i in 1:r]

  for k in 1:r
    if qL[k] < G1.weights[k] - uL2[k]
      return false
    end
  end

  e = ramification_index(p)

  aL1 = G1.normgens
  aL2 = G2.normgens

  d1 = AbsSimpleNumFieldElem[prod(AbsSimpleNumFieldElem[G1.dets[i] for i in 1:j]) for j in 1:r]
  d2 = AbsSimpleNumFieldElem[prod(AbsSimpleNumFieldElem[G2.dets[i] for i in 1:j]) for j in 1:r]

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
        haG1 = haG1 * _witt_hasse(G1.witt[j], G1.ranks[j], G1.dets[j], p) * hilbert_symbol(_d1, G1.dets[j], p)
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
        haG1 = haG1 * _witt_hasse(G1.witt[j], G1.ranks[j], G1.dets[j], p) * hilbert_symbol(_d1, G1.dets[j], p)
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

function is_locally_isometric(L::QuadLat, M::QuadLat, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  fl = genus(L, p) == genus(M, p)
  #@assert fl == is_locally_isometric_kirschmer(L, M, p)
  return fl
end

function genus(L::QuadLat, p)
  if !has_attribute(L, :local_genera)
    local_genera = Dict{ideal_type(base_ring(L)), local_genus_quad_type(base_field(L))}()
    set_attribute!(L, :local_genera, local_genera)
  else
    local_genera = get_attribute(L, :local_genera)
  end

  if haskey(local_genera, p)
    return local_genera[p]::local_genus_quad_type(base_field(L))
  end

  pi, _sym, _weight, _normgen, _f, dets, witt, uL, J, G, E  = _genus_symbol(L, p)
  ranks = Int[d[1] for d in _sym]
  scales = Int[d[2] for d in _sym]

  if is_dyadic(p)
    g = genus(QuadLat, p, ranks, scales, _weight, _normgen, dets, witt,  _f)
  else
    normclass = Int[d[3] for d in _sym]
    g = genus(QuadLat, p, pi, ranks, scales, normclass)
  end
  g.norms = uL
  g.jordec = JorDec(J, G, E, p)
  local_genera[p] = g
  return g::local_genus_quad_type(base_field(L))
end

function _genus_symbol(L::QuadLat, p)
  O = order(p)
  nf(O) != base_field(L) && error("Prime ideal must be an ideal of the base field of the lattice")
  K = nf(O)
  # If you pull from cache, you might have to adjust the symbol according
  # to the uniformizer flag

  J, G, E = jordan_decomposition(L, p)

  t = length(G)

  local pi::AbsSimpleNumFieldElem

  if minimum(p) != 2
    _, _h = residue_field(O, p)
    h = extend(_h, nf(O))
    _sym = Vector{Tuple{Int, Int, Int}}(undef, length(J))
    pi = elem_in_nf(uniformizer(p))
    for i in 1:t
      r = nrows(J[i])
      _sym[i] = (r, E[i], is_local_square(det(G[i])//pi^(r * E[i]), p) ? 1 : - 1)
    end
    _weight = Vector{Int}()
    _normgen = Vector{elem_type(K)}()
    _f = Int[]
    dets = elem_type(K)[det(G[i]) for i in 1:t]
    witt = Int[]
    uL = Int[]
    #Gs = [ h(prod(diagonal(G[i]))//unif^(E[i] * nrows(J[i]))) for i in 1:length(J)]
    #@assert !(0 in Gs)
    #x  = [ (nrows(J[i]), E[i], is_square(Gs[i])[1] ? 1 : -1) for i in 1:length(J)]
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
#  Sum of genus symbols
#
################################################################################

function direct_sum(G1::QuadLocalGenus, G2::QuadLocalGenus)
  @req prime(G1) === prime(G2) "Local genera must have the same prime ideal"
  if !G1.is_dyadic
    p = prime(G1)
    if uniformizer(G1) != uniformizer(G2)
      q = divexact(G2.uniformizer, G1.uniformizer)
      fl = is_local_square(q, p)
      local G2adj::Vector{Int}
      if fl
        G2adj = G2.detclasses
      else
        G2adj = Vector{Int}(undef, length(G2))
        for i in 1:length(G2)
          if isodd(G2.ranks[i] * G2.scales[i])
            G2adj[i] = -G2.detclasses[i]
          else
            G2adj[i] = G2.detclasses[i]
          end
        end
      end
    else
      G2adj = G2.detclasses
    end
    G3 = _direct_sum_easy(G1, G2, G2adj)
  else
    L1 = representative(G1)
    L2 = representative(G2)
    L3, = direct_sum(L1, L2)
    G3 = genus(L3, prime(G1))
  end

  if isdefined(G1, :jordec) && isdefined(G2, :jordec)
    G3.jordec = direct_sum(G1.jordec, G2.jordec)
  end

  return G3
end

function _direct_sum_easy(G1::QuadLocalGenus, G2::QuadLocalGenus, detclassesG2 = G2.detclasses)
  # We do a merge sort
  i1 = 1
  i2 = 1
  _sca = Int[]
  _rk = Int[]
  _detclass = Int[]
  while i1 <= length(G1) && i2 <= length(G2)
    if scale(G1, i1) < scale(G2, i2)
      push!(_sca, scale(G1, i1))
      push!(_rk, rank(G1, i1))
      push!(_detclass, G1.detclasses[i1])
      i1 += 1
    elseif scale(G2, i2) < scale(G1, i1)
      push!(_sca, scale(G2, i2))
      push!(_rk, rank(G2, i2))
      push!(_detclass, G2.detclasses[i2])
      i2 += 1
    else
      push!(_sca, scale(G1, i1))
      push!(_rk, rank(G1, i1) + rank(G2, i2))
      push!(_detclass, G1.detclasses[i1] * G2.detclasses[i2])
      i1 += 1
      i2 += 1
    end
  end

  if i1 <= length(G1)
    append!(_sca, G1.scales[i1:length(G1)])
    append!(_rk, G1.ranks[i1:length(G1)])
    append!(_detclass, G1.detclasses[i1:length(G1)])
  end

  if i2 <= length(G2)
    append!(_sca, G2.scales[i2:length(G2)])
    append!(_rk, G2.ranks[i2:length(G2)])
    append!(_detclass, G2.detclasses[i2:length(G2)])
  end

  return genus(QuadLat, prime(G1), uniformizer(G1), _rk, _sca, _detclass)
end

Base.:(+)(G1::QuadLocalGenus, G2::QuadLocalGenus) = direct_sum(G1, G2)

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

function _non_square(K, p)
  O = order(p)
  R, mR = residue_field(O, p)
  u = elem_in_nf(mR\non_square(R))
  @assert !is_local_square(u, p)[1]
  return u
end

function representative(G::QuadLocalGenus)
  K = nf(order(G.p))
  return lattice(quadratic_space(K, gram_matrix(jordan_decomposition(G))))
end

######

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

function _genus_symbol_kirschmer(L::QuadLat, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}; uniformizer = zero(order(p)))
  O = order(p)
  nf(O) != base_field(L) && error("Prime ideal must be an ideal of the base field of the lattice")
  # If you pull from cache, you might have to adjust the symbol according
  # to the uniformizer flag

  J, G, E = jordan_decomposition(L, p)
  if !iszero(uniformizer)
    unif = uniformizer
    if valuation(unif, p) != 1
      error("Wrong uniformizer")
    end
  else
    unif = elem_in_nf(Hecke.uniformizer(p))
  end

  if minimum(p) != 2
    _, _h = residue_field(O, p)
    h = extend(_h, nf(O))
    Gs = [ h(prod(diagonal(G[i]))//unif^(E[i] * nrows(J[i]))) for i in 1:length(J)]
    @assert !(0 in Gs)
    x  = [ (nrows(J[i]), E[i], is_square(Gs[i])[1] ? 1 : -1) for i in 1:length(J)]
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
      if _is_isometric_quadratic(uu, finer_reps[k][1], p, m) && finer_reps[k][2] == hi
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

function _is_isometric_quadratic(a, b, p, n)
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
  @assert is_dyadic(p)
  # weight, normgen, det, witt
  res = Vector{Tuple{Int, AbsSimpleNumFieldElem, AbsSimpleNumFieldElem, Int}}()

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

    _find_special_class_dict = Dict{AbsSimpleNumFieldElem, AbsSimpleNumFieldElem}()

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
            #@assert is_local_square(d//(1 + gamma), p)
            #@assert valuation(d, p) == valuation(1 + gamma, p)
            dis = d
          else
            gamma = __find_special_class(-d, p) - 1
            #@assert is_local_square(-d//(1 + gamma), p)
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

@doc raw"""
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

  if !is_dyadic(p)
    ns = _non_square(E, p)
    u = elem_in_nf(uniformizer(p))
    for scalerank in scales_rks
      _local_jordan_decompositions_nondyadic!(res, E, p, scalerank, ns, u)
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

    decs_per_rank = Dict{Int, Vector{Tuple{Int, AbsSimpleNumFieldElem, AbsSimpleNumFieldElem, Int}}}()

    for m in possible_ranks
      decs_per_rank[m] = _unimodular_jordan_block(p, m)
    end

    for sr in scales_rks
      _local_jordan_decompositions_dyadic!(res, E, p, sr, G, mG, pi, k, reps_squares, e, possible_ranks, decs_per_rank)
    end
    return res
    #for srwndw in scales_rks_norms_weights_normgens_dets_witts
    #  push!(res, JorDec(p, Int[s[1] for s in srwndw], Int[s[2] for s in srwndw], AbsSimpleNumFieldElem[pi^s[1] * s[5] for s in srwndw], Int[s[1] + s[4] for s in srwndw], AbsSimpleNumFieldElem[pi^(s[1] * s[2]) * s[6] for s in srwndw], Int[isodd(s[2]) ? s[7] : s[7] * hilbert_symbol(pi^s[1], (-1)^divexact(s[2]*(s[2] - 1), 2) * pi^(s[1] * s[2]) * s[6], p) for s in srwndw]))
    #end
    #return res
  end
end

function _local_jordan_decompositions(E, p, scalerank)
  res = JorDec{typeof(E), typeof(p), elem_type(E)}[]
  if is_dyadic(p)
    _local_jordan_decompositions_dyadic!(res, E, p, scalerank)
  else
    _local_jordan_decompositions_nondyadic!(res, E, p, scalerank)
  end
  return res
end

function _local_jordan_decompositions_nondyadic!(res, E, p, scalerank)
  ns = _non_square(E, p)
  u = elem_in_nf(uniformizer(p))
  return _local_jordan_decompositions_nondyadic!(res, E, p, scalerank, ns, u)
end

function _local_jordan_decompositions_nondyadic!(res, E, p, scalerank, ns, u)
  class1 = elem_type(E)[u^(s[1] * s[2]) for s in scalerank]
  class2 = elem_type(E)[ns * u^(s[1] * s[2]) for s in scalerank]
  l = length(scalerank)
  @assert l <= sizeof(UInt) * 8
  # I need to compute all possibilities to distribute class1/class2
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

function _local_jordan_decompositions_dyadic!(res, E, p, scalerank, G, mG, pi, k, reps_squares, e, possible_ranks, decs_per_rank)
  sr = scalerank

  it = Iterators.product([decs_per_rank[r] for (s, r) in sr]...)
  for local_blocks in it
    # local blocks in form weight, normgen, det, witt
    # JorDec(p, sc::Vector{Int},
    #           rks::Vector{Int},
    #           normgens::Vector{AbsSimpleNumFieldElem},
    #           weights::Vector{Int},
    #           dets::Vector{AbsSimpleNumFieldElem},
    #           witts::Vector{Int})

    l = length(sr)
    J = JorDec(p, Int[s[1] for s in sr],
               Int[s[2] for s in sr],
               AbsSimpleNumFieldElem[pi^sr[i][1] * local_blocks[i][2] for i in 1:l],
               Int[sr[i][1] + local_blocks[i][1] for i in 1:l],
               AbsSimpleNumFieldElem[pi^(sr[i][1] * sr[i][2]) * local_blocks[i][3] for i in 1:l],
               Int[isodd(sr[i][2]) ? local_blocks[i][4] : local_blocks[i][4] * hilbert_symbol(pi^sr[i][1], (-1)^divexact(sr[i][2]*(sr[i][2] - 1), 2) * pi^(sr[i][1] * sr[i][2]) * local_blocks[i][3], p) for i in 1:l])
    push!(res, J)
  end
end

function _local_jordan_decompositions_dyadic!(res, E, p, scalerank)
  G, mG = local_multiplicative_group_modulo_squares(p)
  pi = elem_in_nf(uniformizer(p))
  k = ngens(G)
  reps_squares = typeof(pi)[ mG(g) for g in G if iszero(g[k])]
  @assert all(valuation(u, p) == 0 for u in reps_squares)

  e = ramification_index(p)

  # collect the possible ranks

  possible_ranks = unique!(reduce(vcat, Vector{Int}[[r[2] for r in s] for s in [scalerank]]))

  decs_per_rank = Dict{Int, Vector{Tuple{Int, AbsSimpleNumFieldElem, AbsSimpleNumFieldElem, Int}}}()

  for m in possible_ranks
    decs_per_rank[m] = _unimodular_jordan_block(p, m)
  end

  return _local_jordan_decompositions_dyadic!(res, E, p, scalerank, G, mG, pi, k, reps_squares, e, possible_ranks, decs_per_rank)
end


function quadratic_local_genera(K, p; rank::Int, det_val::Int, max_scale = nothing)
  J = local_jordan_decompositions(K, p, rank = rank, det_val = det_val, max_scale = max_scale)
  res = local_genus_quad_type(K)[]
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

genus_quad_type(K) = QuadGenus{typeof(K), ideal_type(order_type(K)), elem_type(K)}

# All the functions calling `QuadGenus` filter the local symbols so
# that we keep only the one defined over bad primes or which are not unimodular
function QuadGenus(K, d, LGS, signatures)
  z = genus_quad_type(K)(K)
  z.LGS = LGS
  z.signatures = signatures
  z.d = d
  z.rank = rank(LGS[1])
  z.primes = [prime(g) for g in LGS]
  z.K = K
  return z
end

function show(io::IO, ::MIME"text/plain", G::QuadGenus)
  io = pretty(io)
  println(io, "Genus symbol for quadratic lattices")
  print(io, Indent(), "over ", Lowercase())
  Base.show(io, MIME"text/plain"(), maximal_order(G.K))
  println(io, Dedent())
  sig = G.signatures
  lgs = G.LGS
  if length(sig) == 1
    print(io, "Signature: ")
  else
    print(io, "Signatures: ")
  end
  print(io, Indent())
  for (pl, v) in sig
    println(io)
    Base.show(terse(io), Lowercase(), pl)
    print(io, " => ", v)
  end
  print(io, Dedent())
  if length(lgs) == 1
    print(io, "\n", "Local symbol: ")
  else
    print(io, "\n", "Local symbols: ")
  end
  print(io, Indent())
  for g in lgs
    println(io)
    print(IOContext(io, :compact => true), prime(g), " => ")
    print(terse(io), Lowercase(), g)
  end
  print(io, Dedent())
end

function show(io::IO, G::QuadGenus)
  if is_terse(io)
    print(io, "Genus symbol for quadratic lattices")
  else
    io = pretty(io)
    print(io, "Genus symbol for quadratic lattices of rank $(G.rank) over ")
    print(terse(io), Lowercase(), maximal_order(G.K))
  end
end

function genus(L::QuadLat{})
  return get_attribute!(L, :genus) do
    bad = bad_primes(L, even = true)
    S = real_places(base_field(L))
    D = diagonal(rational_span(L))
    signatures = Dict{InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}, Int}(s => count(d -> is_negative(d, _embedding(s)), D) for s in S)
    G = QuadGenus(base_field(L), prod(D), [genus(L, p) for p in bad], signatures)
    return G::genus_quad_type(base_field(L))
  end
end

function Base.:(==)(G1::QuadGenus, G2::QuadGenus)
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

function Base.hash(G::QuadGenus, u::UInt)
  u = Base.hash(base_field(G), u)   # We compare symbol over the same parent base field
  # The theory/definition tells us that a genus symbols is uniquely determined by its
  # signatures (infinite local data) and the local symbol (finite local data).
  h = reduce(xor, (hash(x) for x in local_symbols(G)), init = hash(signatures(G)))
  return xor(h,u)
end

base_field(G::QuadGenus) = G.K

signatures(G::QuadGenus) = G.signatures

primes(G::QuadGenus) = G.primes

function quadratic_genera(K; rank::Int, signatures, det)
  OK = maximal_order(K)
  # For genera of quadratic lattices, bad primes are those dividing 2 in the
  # base field
  bd = support(2*OK)
  _max_scale = 2 * det

  primes = support(2 * det)

  local_symbols = Vector{local_genus_quad_type(K)}[]

  ms = _max_scale
  ds = det
  for p in primes
    det_val = valuation(ds, p)
    mscale_val = valuation(ms, p)
    push!(local_symbols, quadratic_local_genera(K, p, rank = rank, det_val = det_val, max_scale = mscale_val))
  end

  res = genus_quad_type(K)[]
  it = Iterators.product(local_symbols...)
  for gs in it
    c = collect(gs)::Vector{local_genus_quad_type(K)}
    # We only keep local symbols which are defined over a bad prime, or which
    # are not unimodular.
    filter!(g -> (prime(g) in bd) || scales(g) != Int[0], c)
    de = _possible_determinants(K, c, signatures)::Vector{AbsSimpleNumFieldElem}
    for d in de
      b = _check_global_quadratic_genus(c, d, signatures)
      if b
        push!(res, QuadGenus(K, d, c, signatures))
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
      #@show is_local_square(-d, prime(c[i]))
      if is_local_square(-d, prime(c[i]))
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
  rlp = real_embeddings(K)
  local R::FinGenAbGroup
  R, _exp, _log = sign_map(OK, rlp, 1 * OK)
  tar = R(Int[isodd(signatures[infinite_place(sigma)]) ? 1 : 0 for sigma in rlp])
  gensU = gens(U)
  S, mS = sub(R, elem_type(R)[_log(mU(u)) for u in gensU], false)
  # I need totally positive units / OK^*2
  Q, mQ = quo(U, 2, false)
  f = hom(Q, R, elem_type(R)[_log(mU(mQ\u)) for u in gens(Q)])
  Ker, mKer = kernel(f, false)
  transver = elem_type(K)[ evaluate(mU(mQ\(mKer(k)))) for k in Ker]

  dets = elem_type(K)[]

  for P in s
    J = I * P^2
    fl, u = is_principal_with_data(J)
    @assert fl
    # I need to change u such that sign(u, sigma) = (-1)^signatures[sigma]
    v = _log(elem_in_nf(u)) + tar
    fl, y = has_preimage_with_preimage(mS, v)
    if fl
      z = elem_in_nf(u) * prod(elem_type(K)[ evaluate(mU(gensU[i]))^y.coeff[i] for i in 1:length(gensU)])
      @assert z * OK == J
      @assert all(sigma -> sign(z, sigma) == (-1)^signatures[infinite_place(sigma)], rlp)
      for t in transver
        possible_det = z * t
        good = true
        for g in local_symbols
          # I need to test if the determinant is locally correct
          if !is_local_square(possible_det * det(g), prime(g))
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

function quadratic_space(G::QuadGenus)
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

function representative(G::QuadGenus)
  K = G.K
  OK = order(primes(G)[1])
  # Let's follow the Lorch paper. This is also how we do it in the Hermitian case.
  V = quadratic_space(G)
  M = maximal_integral_lattice(V)
  for g in G.LGS
    p = prime(g)
    @vprintln :Lattice 1 "Finding representative for $g at $(prime(g))..."
    L = representative(g)
    M = locally_isometric_sublattice(M, L, p)
    @assert is_locally_isometric(M, L, p)
  end
  return M
end

function locally_isometric_sublattice(M::QuadLat, L::QuadLat, p)
  k, h = residue_field(order(p), p)
  m = rank(M)
  chain = typeof(L)[ L ]
  local LL::typeof(M)
  ok, LL = is_maximal_integral(L, p)
  E = nf(order(p))
  while !ok
    push!(chain, LL)
    ok, LL = is_maximal_integral(LL, p)
  end
  pop!(chain)
  LL = M
  reverse!(chain)
  for X in chain
    BM = local_basis_matrix(LL, p, type = :submodule)
    pM = _module_scale_ideal(pseudo_matrix(LL), fractional_ideal(order(p), p))
    while true
      local v::Vector{elem_type(k)}
      v = elem_type(k)[ rand(k) for i in 1:m ]
      while all(iszero, v)
        v = elem_type(k)[ rand(k) for i in 1:m ]
      end
      KM = kernel(matrix(k, length(v), 1, v), side = :left)
      KM = map_entries(x -> E(h\x)::elem_type(E), KM)
      _new_pmat = _sum_modules(pseudo_matrix(KM * BM), pM)
      LL = lattice(ambient_space(M), _new_pmat)
      if is_locally_isometric(X, LL, p)
        break
      end
    end
  end
  @assert is_locally_isometric(L, LL, p)
  return LL
end

function representatives(G::QuadGenus)
  return genus_representatives(representative(G))
end

################################################################################
#
#  Direct sum of genus symbols
#
################################################################################

function direct_sum(G1::QuadGenus{S, T, U}, G2::QuadGenus{S, T, U}) where {S, T, U}
  @req G1.K === G2.K "Global genus symbols must be defined over the same field"
  K = G1.K
  # For genera of quadratic lattice, are bad all primes dividing 2
  bd = support(2*maximal_order(K))
  LGS = local_genus_quad_type(K)[]
  P1 = Set(primes(G1))
  P2 = Set(primes(G2))
  for p in union(P1, P2)
    if p in P1
      i = findfirst(g -> prime(g) == p, G1.LGS)::Int
      g1 = G1.LGS[i]
    else
      @assert !is_dyadic(p)
      fl = is_local_square(G1.d, p)
      dcl = fl ? 1 : -1
      g1 = genus(QuadLat, p, [(0, rank(G1), dcl)])
    end

    if p in P2
      i = findfirst(g -> prime(g) == p, G2.LGS)
      g2 = G2.LGS[i]
    else
      @assert !is_dyadic(p)
      fl = is_local_square(G2.d, p)
      dcl = fl ? 1 : -1
      g2 = genus(QuadLat, p, [(0, rank(G2), dcl)])
    end
    g3 = direct_sum(g1, g2)
    push!(LGS, g3)
  end
  sig1 = G1.signatures
  sig2 = G2.signatures
  sig3 = merge(+, sig1, sig2)
  # We only keep local symbols which are defined at a bad prime or which are not
  # unimodular.
  filter!(g -> (prime(g) in bd) || scales(g) != Int[0], LGS)
  return QuadGenus(K, G1.d * G2.d, LGS, sig3)
end

Base.:(+)(G1::QuadGenus, G2::QuadGenus) = direct_sum(G1, G2)

################################################################################
#
#  Test if lattice is contained in genus
#
################################################################################

@doc raw"""
    in(L::QuadLat, G::QuadGenus) -> Bool

Test if the lattice $L$ is contained in the genus $G$.
"""
Base.in(L::QuadLat, G::QuadGenus) = genus(L) == G


