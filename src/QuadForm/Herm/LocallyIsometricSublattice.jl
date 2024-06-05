################################################################################
#
#  Find a given lattice locally
#
################################################################################

# TODO: This still needs to be cleaned up, but these are only internal changes

# The split case

function _locally_isometric_sublattice_split(M, L, p, P, absolute_map)
  pi = p_uniformizer(P)
  BM, _, SM = jordan_decomposition(M, p)
  BL, _, SL = jordan_decomposition(L, p)
  _SM = Vector{Int}[Int[SM[i] for j in 1:nrows(BM[i])] for i in 1:length(BM)]
  SMall = reduce(vcat, _SM)
  _SL = Vector{Int}[Int[SL[i] for j in 1:nrows(BL[i])] for i in 1:length(BL)]
  SLall = reduce(vcat, _SL)
  BMall = reduce(vcat, BM)
  @assert nrows(BMall) == rank(M)
  E = Int[ SLall[i] - SMall[i] for i in 1:nrows(BMall) ]
  for i in 1:nrows(BMall)
    multiply_row!(BMall, pi^E[i], i)
  end
  pM = pseudo_matrix(M)
  pmaxEpM = P^maximum(E) * pM
  _new_pmat = _sum_modules(M, pseudo_matrix(BMall), pmaxEpM)
  pminEpM = P^minimum(E) * pM
  _new_pmat = _intersect_modules_with_map(_new_pmat, pminEpM, absolute_map)
  return lattice(ambient_space(M), _new_pmat)
end

# The inert case

function _locally_isometric_sublattice_inert(M, L, p, P, absolute_map)
  OE = base_ring(M)
  E = nf(OE)
  genL = genus(L, p)
  r0 = 0
  mtype = dense_matrix_type(E)
  for i in 1:length(genL)
    if iseven(scale(genL, i))
      r0 += rank(genL, i)
    end
  end

  if is_dyadic(p)
    nsn = zero(E)
  else
    nsn = elem_in_nf(_non_square_norm(P))
  end

  B, G, S = jordan_decomposition(M, p)
  @assert all(s in [0, 1] for s in S)
  if S[1] == 0
    BB = mtype[ B[1][i:i, :] for i in 1:nrows(B[1])]
    m = div(length(BB) - r0, 2)
    k, h = residue_field(base_ring(OE), p)
    hext = extend(h, base_field(E))
    YY = mtype[ BB[i] for i in (2*m + 1):length(BB) ]
    for i in 1:m
      # Transform <BB[2i-1], BB[2i]> into H(0).
      el = coeff(-G[1][2*i, 2*i]//G[1][2*i - 1, 2*i - 1], 0)
      b, s = is_square_with_sqrt(hext(el))
      if b
        push!(YY, BB[2*i] + E(hext\s)*BB[2*i - 1])
      else
        el = coeff(-G[1][2*i, 2*i]//G[1][2*i - 1, 2*i - 1], 0) * norm(nsn)
        b, s = is_square_with_sqrt(hext(el))
        @assert b
        push!(YY, nsn * BB[2*i] + E(hext\s) * BB[2*i - 1])
      end
    end
    if length(B) == 2
      Y = vcat(reduce(vcat, YY), B[2])
    else
      Y = reduce(vcat, YY)
    end
    pM = pseudo_matrix(M)
    PpM = P*pseudo_matrix(M)
    _new_pmat = _sum_modules(M, pseudo_matrix(Y), PpM)
    _new_pmat = _intersect_modules_with_map(_new_pmat, pM, absolute_map)
    LL = lattice(ambient_space(M), _new_pmat)
  else
    LL = M
  end
  B, _, _ = jordan_decomposition(LL, p)
  Y = reduce(vcat, B)
  #  Now Y generates the Gerstein reduction of L_p locally.
  #  So we simply rescale the generators in Y appropriately and assemble
  #  the global solution.

  pi = elem_in_nf(p_uniformizer(p))
  i = 1
  j = r0 + 1
  for l in 1:length(genL)
    s = pi^div(scale(genL, l), 2)
    if iseven(scale(genL, l))
      for k in 1:rank(genL, l)
        multiply_row!(Y, s, i)
        i = i + 1
      end
    else
      for k in 1:rank(genL, l)
        multiply_row!(Y, s, j)
        j = j + 1
      end
    end
  end
  max = scale(genL, length(genL))
  PmaxpM = P^max * pseudo_matrix(M)
  _new_pmat = _sum_modules(pseudo_matrix(Y), PmaxpM)
  _new_pmat = _intersect_modules(_new_pmat, pseudo_matrix(M))
  return lattice(ambient_space(M), _new_pmat)
end

# The odd (non-dyadic) ramified case

function _locally_isometric_sublattice_odd_ramified(M, L, p, P, absolute_map)
  E = nf(base_ring(M))
  K = base_field(E)

  mtype = dense_matrix_type(E)
  local c::local_genus_herm_type(E)
  local LL::typeof(M)
  c = genus(L, p)
  C = typeof(c)[ c ]
  while scale(c, length(c)) >= 2
    c0 = genus(HermLat, E, p, [(scale(c, i), rank(c, i), det(c, i)) for i in 1:length(c) if scale(c, i) in [0, 2]])
    if length(c0) == 2
      c0 = genus(HermLat, E, p, [(0, sum(ranks(c0)), prod(dets(c0)))])
    elseif length(c0) == 1
      c0 = genus(HermLat, E, p, [(0, rank(c0, 1), det(c0, 1))])
    end
    c1 = genus(HermLat, E, p, [(scale(c, i), rank(c, i), det(c, i)) for i in 1:length(c) if scale(c, i) in [1, 3]])
    if length(c1) == 2
      c1 = genus(HermLat, E, p, [(1, sum(ranks(c1)), prod(dets(c1)))])
    elseif length(c1) == 1
      c1 = genus(HermLat, E, p, [(1, rank(c1, 1), det(c1, 1))])
    end
    c = genus(HermLat, E, p,
              vcat(c0.data, c1.data, [(scale(c, i) - 2, rank(c, i), det(c, i)) for i in 1:length(c) if scale(c, i) >= 4]))
    push!(C, c)
  end
  # C contains the genus symbols of all Gernstein reduced lattices above L_p.

  B, G, S = jordan_decomposition(M, p)
  @assert all(s in [-1, 0] for s in S)
  B0 = S[end] == 0 ? mtype[ B[end][i:i, :] for i in 1:nrows(B[end]) ] : mtype[]
  B1 = S[1] == -1 ? mtype[ B[1][i:i, :] for i in 1:nrows(B[1]) ] : mtype[]
  r0 = scale(c, 1) == 0 ? rank(c, 1) : 0
  for i in 1:div(r0 - length(B0), 2)
    push!(B0, B1[2*i - 1])
  end
  if length(B0) == 0
    LL = lattice(ambient_space(M), P * pseudo_matrix(M))
  else
    Ppm = P * pseudo_matrix(M)
    _new_pmat = _sum_modules(pseudo_matrix(reduce(vcat, B0)), Ppm)
    _new_pmat = _intersect_modules(_new_pmat, pseudo_matrix(M))
    LL = lattice(ambient_space(M), _new_pmat)
  end
  @assert genus(LL, p) == c

  k, h = residue_field(order(p), p)
  hext = extend(h, K)
  for j in length(C)-1:-1:1
    c = C[j]
    if all(!(scale(c, i) in [0, 1]) for i in 1:length(c))
      @assert scale(C[1], 1) - valuation(scale(LL), P) >= 0
      s = div(scale(C[1], 1) - valuation(scale(LL), P), 2)
      LL = lattice(ambient_space(LL), P^s * pseudo_matrix(LL))
      break
    end
    B, G, S = jordan_decomposition(LL, p)
    r = findfirst(i -> scale(c, i) == 1, 1:length(c))
    if r !== nothing
      r = rank(c, r)
      i = findfirst(j -> j == 1, S)
      @assert i !== nothing
      Y1 = mtype[ B[i][j:j,:] for j in 1:r]
    else
      Y1 = mtype[]
    end
    _r = findfirst(i -> scale(c, i) == 0, 1:length(c))
    _Y0 = mtype[]
    if _r !== nothing
      r = rank(c, _r)
      B = mtype[ B[1][j:j, :] for j in 1:nrows(B[1]) ]
      n = length(B)
      _G = G[1]
      local NN::Vector{Int}
      NN = Int[ i for i in 1:n if !(is_square(hext(coeff(_G[i, i], 0))))]
      if length(NN) == 0 && det(c, 1) == -1
        while true
          s = hext\rand(k)
          tmp = hext(coeff(_G[n - 1, n - 1] + s^2 * _G[n, n], 0))
          if !iszero(tmp) && !is_square(tmp)
            break
          end
        end
        _Y0 = vcat(B[1:r-1], mtype[B[n - 1] + s * B[n]])
      else
        SS = setdiff(1:n, NN)
        if det(c, 1) == 1
          Y0 = Int[]
        else
          Y0 = Int[ NN[1] ]
          popfirst!(NN)
        end
        if isodd(r - length(Y0))
          if length(SS) == 0
            while true
              s = hext\rand(k)
              tmp = hext(coeff(_G[n - 1, n - 1] + s^2 * _G[n, n], 0))
              if !iszero(tmp) && is_square(tmp)
                break
              end
            end
            v = B[n - 1]
            B[n - 1] = B[n - 1] + E(s) * B[n]
            B[n] = B[n] - s * _G[n, n]//_G[n - 1, n - 1] * v
            filter!(i -> i < n - 1, NN)
            SS = Int[n - 1, n]
          end
          push!(Y0, SS[1])
          popfirst!(SS)
        end
        Y0 = vcat(Y0, NN[1:2*div(length(NN), 2)], SS)::Vector{Int}
        _Y0 = B[Y0[1:r]]
      end
    end
    Ppm = P * pseudo_matrix(LL)
    _new_pmat = _sum_modules(pseudo_matrix(reduce(vcat, vcat(_Y0, Y1))), Ppm)
    _new_pmat = _intersect_modules(_new_pmat, pseudo_matrix(LL))
    LL = lattice(ambient_space(M), _new_pmat)
    @assert genus(LL, p) == c
  end
  return LL
end

# The even (dyadic) ramified case
# The approach below is VERY lame.
# What we should do is the following:
# 1. Find an (sufficiently good approximation of an) isometry between the ambient spaces of M_p and L_p.
# 2. Let Y_p be the image of L_p under this map. If it is good enough, then Y_p \isom L_p.
# 3. Contsruct a lattice X in the space of M such that X_p = Y_p and X_q = M_q for all q \ne p.

function  _locally_isometric_sublattice_even_ramified(M, L, p, P, absolute_map)
  k, h = residue_field(order(P), P)
  m = rank(M)
  chain = typeof(M)[ L ]
  ok, LL = is_maximal_integral(L, p)
  E = nf(order(P))
  while !ok
    push!(chain, LL)
    ok, LL = is_maximal_integral(LL, p)
  end
  pop!(chain)
  LL = M
  reverse!(chain)
  for X in chain
    BBM = local_basis_matrix(LL, P, type = :submodule)
    pM = P * pseudo_matrix(LL)
    while true
      v = elem_type(k)[ rand(k) for i in 1:m ]
      while all(Bool[iszero(v[i]) for i in 1:m])
        v = elem_type(k)[ rand(k) for i in 1:m ]
      end
      _KM = kernel(matrix(k, length(v), 1, v), side = :left)
      KM = map_entries(x -> E(h\x), _KM)
      _new_pmat = _sum_modules(pseudo_matrix(KM * BBM), pM)
      LL = lattice(ambient_space(M), _new_pmat)

      if is_locally_isometric(X, LL, p)
        break
      end
    end
  end
  return LL
end

################################################################################
#
#  Locally isometric sublattices
#
################################################################################

@doc raw"""
    locally_isometric_sublattice(M::HermLat, L::HermLat, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> HermLat

Given rationally isometric hermitian lattices `M` and `L` over $E/K$ and a prime ideal `p`
of $\mathcal O_K$, return a sublattice `N` of `M` with $N_q = M_q$ for $q \neq p$ and
$N_p$ isometric to $L_p$.
"""
function locally_isometric_sublattice(M::HermLat, L::HermLat, p)
  @assert base_ring(M) == base_ring(L)
  @assert is_rationally_isometric(M, L, p)
  @assert is_maximal_integral(M, p)[1]

  D = prime_decomposition(base_ring(L), p)

  absolute_map = absolute_simple_field(ambient_space(M))[2]

  P = D[1][1]

  if length(D) == 2 # split case
    LL = _locally_isometric_sublattice_split(M, L, p, P, absolute_map)
  elseif length(D) == 1 && D[1][2] == 1 # inert case
    LL = _locally_isometric_sublattice_inert(M, L, p, P, absolute_map)
  elseif !is_dyadic(p) # odd ramified
    LL = _locally_isometric_sublattice_odd_ramified(M, L, p, P, absolute_map)
  else # even ramified
    LL = _locally_isometric_sublattice_even_ramified(M, L, p, P, absolute_map)
  end
  @assert is_locally_isometric(L, LL, p)
  return LL::typeof(L)
end

