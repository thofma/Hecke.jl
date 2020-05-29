# Genus representatives for quadratic lattices,
#
# With permission ported from Magma package of Markus Kirschmer:
# http://www.math.rwth-aachen.de/~Markus.Kirschmer/magma/lat.html

################################################################################
#
#  Genus representatives for hermitian lattices
#
################################################################################

@doc Markdown.doc"""
    genus_representatives(L::HermLat; max = inf, use_auto = false)
                                                        -> Vector{HermLat}

Computes representatives for the isometry classes in the genus of $L$.

At most `max` representatives are returned. The use of automorphims can be
disabled by
"""
function genus_representatives(L::HermLat; max = inf, use_auto::Bool = true)
  @req rank(L) >= 3 "Lattice must have rank >= 2"
  R = base_ring(L)
  definite = isdefinite(L)
  gens, fl, P0 = genus_generators(L)
  a = involution(L)
  LL = typeof(L)[ L ]
  for g in gens
    if definite && g[1] == P0
      continue
    end
    I = g[1]^Int(g[2] - 1)
    J = a(I)
    N = neighbours_with_ppower(L, g[1], g[2] - 1, use_auto = use_auto)::Vector{typeof(L)}
    inter = typeof(L)[]
    for i in 2:length(LL)
      M = pseudo_matrix(LL[i])
      IM = I * M
      JM = J * M
      inter = append!(inter, lattice(ambient_space(L), meet(IM + pseudo_matrix(x), JM) for x in N))
    end
    LL = vcat(LL, N, inter)
  end
  @assert length(LL) == prod(Int[g[2] for g in gens if !definite || g[1] != P0])
  @assert all(X -> genus(X) == genus(L), LL)

  local result::Vector{typeof(L)}
  
  if definite
    result = typeof(L)[]
    for L in LL
      # Should never happen!
      @assert all(X -> !isisometric(X, L), result)
      neig = iterated_neighbours(L, P0, max = max, use_auto = use_auto)
      append!(result, neig)
      max = max - length(result)
    end
    for i in 1:length(result)
      for j in 1:i-1
        @assert !(isisometric(result[i], result[j])[1])
      end
    end
  else
    result = LL
  end
  return result
end

function _neighbours(L, P, result, max, callback = stdcallback, use_auto = true)
  ok, scale = ismodular(L, P);
  @req ok "The lattice must be locally modular"
  R = base_ring(L)
  K = nf(R)
  a = involution(L)
  T = local_basis_matrix(L, P, type = :submodule)
  # This is a bit tricky, since C does not know enough to construct the residue field ...
  # C = a(P)
  p = minimum(P)
  lp = prime_decomposition(R, p)
  if length(lp) == 1
    C = P
  else
    if lp[1][1] == P
      C = lp[2][1]
    elseif lp[2][1] == P
      C = lp[1][1]
    else
      throw(error("This should not happen."))
    end
  end
  k, h = ResidueField(R, C)
  hext = extend(h, K)
  local form::dense_matrix_type(K)
  form = gram_matrix(ambient_space(L))
  special = false
  if scale != 0
    if isramified(R, minimum(P))
      special = isodd(scale)
      scale = div(scale + 1, 2)
    end
    form = K(elem_in_nf(uniformizer(minimum(P))))^(-scale) * form
  end
  n = rank(L)
  W = vector_space(k, n)

  if use_auto
    G = automorphism_group_generators(L)
    @hassert :GenRep 1 all(g -> g * gram_matrix(ambient_space(L)) * transpose(g) == gram_matrix(ambient_space(L)), G)
    Tinv = inv(T)
    adjust_gens = eltype(G)[T * g * Tinv for g in G]
    @hassert :GenRep 1 all(g -> g * form * transpose(g) == form, adjust_gens)
    adjust_gens_mod_p = dense_matrix_type(k)[map_entries(hext, g) for g in adjust_gens]
    adjust_gens_mod_p = dense_matrix_type(k)[x for x in adjust_gens_mod_p if !isdiagonal(x)]
    @hassert :GenRep 1 all(g -> g * pform * transpose(g) == pform, adjust_gens_mod_p)
    if length(adjust_gens_mod_p) > 0
      _LO = line_orbits(adjust_gens_mod_p)
      LO = Vector{eltype(k)}[x[1] for x in _LO]
      @vprint :GenRep 1 "Checking $(length(LO)) representatives (instead of $(div(order(k)^n - 1, order(k) - 1)))\n"
    else
      @vprint :GenRep 1 "Enumerating lines over $k of length $n\n"
      LO = enumerate_lines(k, n)
    end
  else
    @vprint :GenRep 1 "Enumerating lines over $k of length $n\n"
    LO = enumerate_lines(k, n)
  end

  keep = true
  cont = true

  if P != C
    _G = T * form * _map(transpose(T), a)
    G = map_entries(hext, _G)
    pi = p_uniformizer(P)
    pih = h(pi)
    for w in LO
      x = elem_type(K)[ sum(T[i, j] * (hext\w[i]) for i in 1:n) for j in 1:ncols(T)]
      LL = neighbour(L, T, pih * matrix(k, 1, length(w), w) * G, K(pi) .* x, hext, P, C, true)
      keep, cont = callback(result, LL)
      if keep
        push!(result, LL)
      end
      if !cont || (length(result) >= max)
        break
      end
    end
  elseif special
    pi = uniformizer(P)
    _G = elem_in_nf(pi) * T * form * _map(transpose(T), a)
    G = map_entries(hext, _G)
    for w::Vector{fq} in LO
      Gw = G * matrix(k, length(w), 1, w)
      ok = 0
      for d in 1:n
        if !iszero(Gw[d])
          ok = d
          break
        end
      end
      @assert ok != 0
      x = elem_type(K)[ sum(T[i, j] * (hext\w[i]) for i in 1:n) for j in 1:ncols(T)]
      nrm = _inner_product(form, x, x, a)
      b = hext\(-hext(nrm) // (2*Gw[ok, 1]))
      #x = x + b * pi * B[ok]
      for j in 1:ncols(T)
        x[j] = x[j] + b * elem_in_nf(pi) * T[ok, j]
      end
      nrm = _inner_product(form, x, x, a)
      LL = neighbour(L, T, matrix(k, 1, length(w), w) * G, x, hext, P, P, false)
      keep, cont = callback(result, LL)
      if keep
        push!(result, LL)
      end
      if !cont || length(result) >= max
        break
      end
    end
  else
    _G = T * form * _map(transpose(T), a)
    G = map_entries(hext, _G)
    ram = isramified(R, minimum(P))
    if ram
      pi = uniformizer(P)
      S = [ h\x for x in k ]
    else
      p = minimum(P)
      pi = uniformizer(p)
      kp, hp = ResidueField(order(p), p)
      alpha = h\(degree(k) == 1 ? one(k) : gen(k))
      Tram = matrix(kp, 2, 1, [2, hp(tr(alpha))])
    end
    for w::Vector{fq} in LO
      __w = [ (hext\w[i]) for i in 1:n]
      x = [ sum(T[i, j] * (__w[i]) for i in 1:n if !iszero(w[i])) for j in 1:ncols(T)]
      nrm = _inner_product(form, x, x, a) #(x*Form, v) where v:= Vector([ a(e): e in Eltseq(x) ]);
      if !(nrm in P)
        continue
      end
      wG = matrix(k, 1, length(w), w) * G
      ok = 0
      for j in 1:n
        if !iszero(wG[j])
          ok = j
          break
        end
      end
      @assert ok != 0
      if !ram
        el = order(p)(base_field(K)(nrm)//pi)
        b, s, V = can_solve_with_kernel(Tram, matrix(kp, 1, 1, [hp(-el)]), side = :left)
        @assert b
        @assert s * Tram == matrix(kp, 1, 1, [hp(-el)])
        #s, V = solution(Tram, vector(kp, [hp(-el)]))
        #@show _all_row_span(V)
        _kernel = [ matrix(kp, 1, 2, v) for v in _all_row_span(V)]
        l = a(hext\(inv(wG[ok])))
        S = elem_type(K)[ l * (hext\((s + v)[1]) + (hext\(s + v)[2])*alpha) for v in _kernel ]
      end
      for s in S
        LL = neighbour(L, T, wG, elem_type(K)[x[o] + pi*s*T[ok, o] for o in 1:ncols(T)], hext, P, P, false)
        keep, cont = callback(result, LL)
        if keep
          push!(result, LL)
        end
        if !cont || (length(result) >= max)
          break
        end
      end
    end
  end
  return result
end

function neighbour(L, B, xG, x, h, P, CC, split)
  R = order(P)
  K = nf(R)
  n = nrows(B)

  local C::ideal_type(R)

  if CC isa Int 
    C = split ? involution(L)(P) : P
  else
    C = CC
  end

  I = Int[ i for i in 1:n if !iszero(xG[i])]
  i = I[1]
  a = involution(L)
  M = zero_matrix(K, n - length(I), ncols(B))
  for (k, nk) in enumerate(setdiff(1:n, I))
    for j in 1:ncols(B)
      M[k, j] = B[nk, j]
    end
  end
  CI = fractional_ideal_type(R)[ K(1) * R for j in 1:(n - length(I)) ]
  for j in I
    if j != i
      M = vcat(M, matrix(K, 1, ncols(B), elem_type(K)[B[j, k] - a(h\(divexact(xG[j], xG[i]))) * B[i, k] for k in 1:ncols(B)]))
      push!(CI, K(1) * R)
    end
  end
  M = vcat(M, sub(B, i:i, 1:ncols(B)))
  push!(CI, fractional_ideal(order(P), P))
  M = vcat(M, matrix(K, 1, ncols(B), x))
  push!(CI, inv(C))
  pm = pseudo_hnf(pseudo_matrix(M, CI))
  _M = _sum_modules(pm, _module_scale_ideal((split ? P : P * C), pseudo_matrix(L)))
  LL = lattice(ambient_space(L), _M)

  @assert islocally_isometric(L, LL, P)
  return LL
end

function neighbours(L::HermLat, P, max = inf)
#{The immediate P-neighbours of L}
#  require Order(P) eq BaseRing(L): "Arguments are incompatible";
#  require IsPrime(P): "Second argument must be prime";
#  require not IsRamified(P) or Minimum(P) ne 2: "Second argument cannot be a ramified prime over 2";
#  require IsModular(L, P) : "The lattice must be locally modular";
#  require Rank(L) ge 2: "The rank of the lattice must be at least 2";
#  require IsIsotropic(L, P): "The lattice must be locally isotropic";
#
  return _neighbours(L, P, [], max)
end

function stdcallback(list, L)
  keep = all(LL -> !isisometric(LL, L)[1], list)
#//  keep, #List;
  return keep, true;
end

function iterated_neighbours(L::HermLat, P; use_auto = false, max = inf, callback = false)# AutoOrbits, CallBack:= false, Max:= Infinity()) -> []
  #require Order(P) eq BaseRing(L): "Arguments are incompatible";
  #require IsPrime(P): "Second argument must be prime";
  #require not IsRamified(P) or Minimum(P) ne 2: "Second argument cannot be a ramified prime over 2";
  #require IsModular(L, P) : "The lattice must be locally modular";
  #require Rank(L) ge 2: "The rank of the lattice must be at least 2";
  #require IsIsotropic(L, P): "The lattice must be locally isotropic";
  
  if callback == false && isdefinite(L)
    _callback = stdcallback
  else
    _callback = callback
  end

  result = typeof(L)[ L ]
  i = 1
  while length(result) < max && i <= length(result)
    # _Neighbours and the callback only add new lattices if not isometric to known ones and stop if Max is reached.
    # So we have nothing to at all.
    result = _neighbours(result[i], P, result, max, _callback)# : CallBack:= CallBack);
    i = i + 1
  end
  return result
end


