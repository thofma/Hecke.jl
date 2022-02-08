export representatives, genus_representatives


# Genus representatives for quadratic lattices,
#
# With permission ported from Magma package of Markus Kirschmer:
# http://www.math.rwth-aachen.de/~Markus.Kirschmer/magma/lat.html

################################################################################
#
#  Neighbours methods
#
################################################################################

function _all_row_span(M)
  F = base_ring(M)
  rows = Vector{Vector{elem_type(F)}}(undef, nrows(M))
  for i in 1:nrows(M)
    rows[i] = elem_type(F)[M[i, j] for j in 1:ncols(M)]
  end
  n = nrows(M)
  it = Iterators.product([F for i in 1:n]...)
  res = Vector{Vector{elem_type(F)}}()
  for c in it
    z = Ref(c[1]) .* rows[1]
    for i in 2:n
      z = z .+ (Ref(c[i]) .* rows[i])
    end
    push!(res, z)
  end
  return res
end

@doc Markdown.doc"""
    smallest_neighbour_prime(L::HermLat) -> Bool, NfRelOrdIdl, Vector{NfOrdIdl}

Given a hermitian lattice `L`, return `def, P0, bad` such that:

- `def` is `true` if `L` is definite, else `false`;
- `P0` is a prime ideal in the base ring `O` of `L` which is not bad, such that
  `L` is isotropic at `minimum(P0)` and `P0` has smallest minimum among the primes 
  satisfying these properties; if `L` is indefinite, `P0` is set to be the trivial ideal;
- `bad` is a vector of prime ideals `p` in the maximal order of the fixed field 
  of `L` such that `L_p` is not modular or `p` is dyadic and is not coprime to
  the discriminant of `O`.
"""
function smallest_neighbour_prime(L)
  S = base_ring(L)
  R = base_ring(S)
  lp = bad_primes(L)
  bad = ideal_type(R)[p for p in lp if !ismodular(L, p)[1] ]
  for (p,_) in factor(discriminant(S))
    if isdyadic(p) && !(p in bad)
      push!(bad, p)
    end
  end

  if !isdefinite(L)
    return false, 1*S, bad
  end

  # TODO: This does not find the prime ideal with smallest norm,
  # but with smallest minimum ...

  m = rank(L)
  p = 1
  P = ideal_type(R)[]
  while length(P) == 0
    p = next_prime(p)
    lp = ideal_type(R)[ p[1] for p in prime_decomposition(R, p)]
    P = setdiff(lp, bad)
    if m == 2
      P = filter(p -> isisotropic(L, p), P)
    end
  end
  Q = prime_decomposition(S, P[1])[1][1]

  if isempty(bad)
    I = 1 * S
  else
    I = prod(bad) * S
  end
  n = absolute_norm(Q)
  if n >= 1000
    PP = prime_ideals_up_to(S, 1000)
    for QQ in PP
      if !iscoprime(QQ, I)
        continue
      end

      if isisotropic(L, QQ)
        return true, QQ, bad
      end
    end
  end
  PP = prime_ideals_up_to(S, n)
  for QQ in PP
    if !iscoprime(QQ, I)
      continue
    end
    if isisotropic(L, QQ)
      return true, QQ, bad
    end
  end
  throw(error("Impossible"))
end

function _neighbour(L, B, xG, x, h, P, CC, split)
  R = order(P)
  K = nf(R)
  n = nrows(B)
  a = involution(L)

  local C::ideal_type(R)

  if CC isa Int
    C = split ? a(P) : P
  else
    C = CC
  end

  I = Int[ i for i in 1:n if !iszero(xG[i])]
  i = I[1]
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
  pm = pseudo_matrix(M, CI)
  _M = _sum_modules(L, _module_scale_ideal((split ? P : P * C), pseudo_matrix(L)), pm)
  LL = lattice(ambient_space(L), _M)

  @assert islocally_isometric(L, LL, P)
  return LL
end

function stdcallback(list, L)
  keep = all(LL -> !isisometric(LL,L)[1], list)
  return keep, true
end

function eqcallback(list, L)
  keep = all(LL -> LL != L, list)
  return keep, true
end

function _neighbours(L, P, result, max, callback = eqcallback, use_auto = true)
  ok, scale = ismodular(L, P)
  @req ok "The lattice must be locally modular"
  R = base_ring(L)
  K = nf(R)
  a = involution(L)

  if !isdefinite(L) && use_auto
    use_auto = false
  end 

  T = local_basis_matrix(L, P, type = :submodule)
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
      error("This should not happen.")
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
    Tinv = inv(T)
    adjust_gens = eltype(G)[T * g * Tinv for g in G]
    adjust_gens_mod_p = dense_matrix_type(k)[map_entries(hext, g) for g in adjust_gens]
    adjust_gens_mod_p = dense_matrix_type(k)[x for x in adjust_gens_mod_p if !isdiagonal(x)]
    if length(adjust_gens_mod_p) > 0
      _LO = line_orbits(adjust_gens_mod_p)
      LO = Vector{eltype(k)}[x[1] for x in _LO]
    else
      LO = enumerate_lines(k, n)
    end
  else
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
      LL = _neighbour(L, T, pih * matrix(k, 1, length(w), w) * G, K(pi) .* x, hext, P, C, true)
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
      for j in 1:ncols(T)
        x[j] = x[j] + b * elem_in_nf(pi) * T[ok, j]
      end
      nrm = _inner_product(form, x, x, a)
      LL = _neighbour(L, T, matrix(k, 1, length(w), w) * G, x, hext, P, P, false)
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
      nrm = _inner_product(form, x, x, a) 
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
        _kernel = [ matrix(kp, 1, 2, v) for v in _all_row_span(V)]
        l = a(hext\(inv(wG[ok])))
        S = elem_type(K)[ l * (hext\((s + v)[1]) + (hext\(s + v)[2])*alpha) for v in _kernel ]
      end
      for s in S
        LL = _neighbour(L, T, wG, elem_type(K)[x[o] + K(elem_in_nf(pi))*s*T[ok, o] for o in 1:ncols(T)], hext, P, P, false)
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

@doc Markdown.doc"""
    neighbours(L::HermLat, P::NfRelOrdIdl, max = inf) -> Vector{HermLat}

Return the immediate `P`-neighbours of `L`. At most `max` neighbours are returned.

If `L` is definite, this function uses by default the automorphism group of `L`. If 
`L` is indefinite, the use of the automorphism group is automatically disabled.
"""
function neighbours(L::HermLat, P, max = inf)
  @req order(P) == base_ring(L) "Arguments are incompatible"
  @req isprime(P) "Second argument must be prime"
  @req !isramified(order(P), minimum(P)) || !Hecke.isdyadic(minimum(P)) "Second argument cannot be a ramified prime over 2"
  @req ismodular(L, P)[1] "The lattice must be locally modular"
  @req rank(L) >= 2 "The rank of the lattice must be at least 2"
  @req Hecke.isisotropic(L, P) "The lattice must be locally isotropic"

  return _neighbours(L, P, [], max)
end

@doc Markdown.doc"""
    iterated_neighbours(L:HermLat, P::NfRelOrdIdl; use_auto = false, max = inf,
				                   callback = eqcallback,
						   missing_mass = Ref{fmpq}(zero(fmpq)))
                                                                            -> Vector{HermLat}

Return a set of representatives of `N(L,P)` (see [Kir16, Definition 5.2.6]). At most
`max` representatives are returned.

The use of the automorphism group of `L` is disabled by default. If `use_auto` is set on
`true`, the function uses the automorphism group in the definite case; in the indefinite
case, this keyword has no effect.
If `callback = false`, it uses `stdcallback` in the case where `L` is definite, `eqcallback`
otherwise. By defaut, the use of the mass is disabled.
"""
function iterated_neighbours(L::HermLat, P; use_auto = false, max = inf,
                                            callback = false,
                                            missing_mass = Ref{fmpq}(zero(fmpq)))
  @req order(P) == base_ring(L) "Arguments are incompatible"
  @req isprime(P) "Second argument must be prime"
  @req !isramified(order(P), minimum(P)) || !Hecke.isdyadic(minimum(P)) "Second argument cannot be a ramified prime over 2"
  @req ismodular(L, P)[1] "The lattice must be locally modular"
  @req rank(L) >= 2 "The rank of the lattice must be at least 2"
  @req Hecke.isisotropic(L, P) "The lattice must be locally isotropic"

  if callback == false && isdefinite(L)
    _callback = stdcallback
  elseif callback == false && !isdefinite(L)
    _callback = eqcallback
  else
    _callback = callback
  end

  result = typeof(L)[ L ]

  use_mass = !iszero(missing_mass[])

  if use_mass
    _mass = missing_mass[] - 1//automorphism_group_order(L)
  end

  i = 1
  oldlength = length(result)
  while length(result) < max && i <= length(result)
    result = _neighbours(result[i], P, result, max, _callback, use_auto)
    no_lattices = length(result) - oldlength
    oldlength = length(result)
    if use_mass && no_lattices > 0
      _mass = _mass - sum(fmpq[1//automorphism_group_order(result[i]) for i in (length(result) - no_lattices + 1):length(result)])
      if iszero(_mass)
        break
      end
    end
    if use_mass && _mass < 0
      throw(error("This should not happen"))
    end
    i = i + 1
  end
  if use_mass
    missing_mass[] = _mass
  end
  return result
end

@doc Markdown.doc"""
    neighbours_with_ppower(L::HermLat, P::NfRelOrdIdl, e::Integer, use_auto = true)
                                                                      -> Vector{HermLat}

Return a sequence of `P`-neighbours of length `e`, `L=L_1, L_2, \dots, L_e` such that
`L_{i-1} != L_{i+1}` for `i = 2, \dots, e-1` (see [Kir19, Algorithm 4.7.]).

If the lattice is definite, the use of the automorphism group is by default enabled.
In the indefinite case, the automorphism group is not used.
"""
function neighbours_with_ppower(L, P, e)
  result = typeof(L)[]
  for i = 1:e
    if i == 1
      L = neighbours(L, P, 1)[1]
    else
      N = neighbours(L, P,  2)
      L = N[1] == result[end] ? N[2] : N[1]
    end
  push!(result, L)
  end
  return result
end

################################################################################
#
#  Genus representatives for hermitian lattices
#
################################################################################

@doc Markdown.doc"""
    genus_generators(L::HermLat) -> Vector{Tuple{NfRelOrdIdl, fmpz}}, Bool, 
                                    NfRelOrdIdl

Given a hermitian lattice `L`, return `gens, def, P0` such that:

- `gens` is a vector of tuples `(P,e)` consisting of a prime ideal `P` in the base ring of `L`
  and an integer `e \geq 2` which can be used to compute the ideal `\mathfrak A` in line 11
  of [Kir19, Algorithm 4.7.]); 
- `def` is `true` if `L` is definite, else `false`;
- `P0` is a prime ideal in the base ring of `L` which is not bad, such that
  `L` is isotropic at `minimum(P0)` and `P0` has smallest minimum among the primes 
  satisfying these properties.
"""
function genus_generators(L::HermLat)
  R = base_ring(L)
  E = nf(R)
  D = different(R)
  a = involution(L)
  def, P0, bad = smallest_neighbour_prime(L)

  local bad_prod::ideal_type(base_ring(R))

  if isempty(bad)
    bad_prod = 1 * base_ring(R)
  else
    bad_prod = prod(bad)
  end

  # First the ideals coming from the C/C0 quotient
  Eabs, EabstoE = absolute_simple_field(ambient_space(L))
  Rabs = maximal_order(Eabs)
  C, h = class_group(Rabs)
  RR = base_ring(R)
  C0 = support(D)
  CC, hh = class_group(RR)
  for p in find_gens(pseudo_inv(hh), PrimesSet(2, -1))[1]
    if !(p in C0)
      push!(C0, sum(R * R(EabstoE(elem_in_nf(b))) for b in basis(p)))
    end
  end
  Q0, q0 = quo(C, elem_type(C)[ h\ideal(Rabs, [Rabs(EabstoE\b) for b in absolute_basis(i)]) for i in C0])
  q00 = pseudo_inv(q0) * h
  PP = ideal_type(R)[]

  local F::GaloisField

  local W::Generic.QuotientModule{gfp_elem}

  if iseven(rank(L))
    for (P, e) in factor(D)
      p = minimum(P)
      G = genus(L, p)
      if any(i -> isodd(rank(G, i)), 1:length(G))
        continue
      elseif !isdyadic(p)
        if any(i -> iseven(scale(G, i)), 1:length(G))
          continue
        end
      else
        if any(i -> isodd(e  + scale(G, i)) || (e + scale(G, i) != G.ni[i]), 1:length(G))
          continue
        end
      end
      push!(PP, P)
    end

    if !isempty(PP)
      U, f = unit_group_fac_elem(Rabs)
      UU, ff = unit_group_fac_elem(RR)
      nnorm = hom(U, UU, GrpAbFinGenElem[ff\FacElem(nf(RR)(norm(f(U[i])))) for i in 1:ngens(U)])
      l = length(PP)
      VD = Int[ valuation(D, P) for P in PP ]
      K, k = kernel(nnorm)
      F = GF(2, cached = false)
      V = VectorSpace(F, length(PP))
      S = elem_type(V)[]
      for u in gens(K)
        z = elem_type(F)[]
        for i in 1:length(PP)
          zz = R(EabstoE(evaluate(f(k(u))))) - 1
          if iszero(zz) || (valuation(zz, PP[i]) >= VD[i])
            push!(z, F(0))
          else
            push!(z, F(1))
          end
        end
        push!(S, V(z)::elem_type(V))
      end
      _T, _ = sub(V, S)
      W, w = quo(V, _T)
      if dim(W) == 0
        PP = ideal_type(R)[]
      end
    end
  end

  Gens = Tuple{ideal_type(R), fmpz}[]

  if isempty(PP)
    S = GrpAbFinGenElem[]
    Q, q = quo(Q0, S)::Tuple{GrpAbFinGen, GrpAbFinGenMap}
    Work = def ? typeof(P0)[ P0 ] : typeof(P0)[]
    p = 2
    while order(Q) > 1
      while isempty(Work)
        p = next_prime(p)
        Work = ideal_type(R)[ QQ for QQ in support(p * R) if length(prime_decomposition(R,minimum(QQ))) == 2 && valuation(bad_prod, minimum(QQ)) == 0 ]
      end
      P = popfirst!(Work)
      c = (q00\(EabstoE\P))::GrpAbFinGenElem
      o = order(q(c))::fmpz
      if !isone(o)
        push!(S, c)
        Q, q = quo(Q0, S)::Tuple{GrpAbFinGen, GrpAbFinGenMap}
        push!(Gens, (P, o))
      end
    end
  else
    ll = Int(order(Q0))
    cocycle = Matrix{elem_type(W)}(undef, ll, ll)
    for i in 1:ll
      for j in 1:ll
        cocycle[i,j] = zero(W)
      end
    end
    C = collect(Q0)
    ideals = ideal_type(Rabs)[ q00(C[i]) for i in 1:length(C) ]
    for i in 1:ll
      for j in 1:i
        ij = findfirst(isequal(C[i] + C[j]), C)
        Iabs = ideals[i] * ideals[j] * inv(ideals[ij])
        I = EabstoE(Iabs)
        J = I * inv(a(I))
        Jabs = EabstoE\J
        ok, x = isprincipal(Jabs)
        u = f(nnorm\(-(ff\FacElem(nf(RR)(norm(x))))))
        x = x * u
        @assert norm(x) == 1
        if evaluate(x) == 1
          y = w(V(zeros(F,length(PP))))
        else
          y = w(V([ valuation(EabstoE(evaluate(x) - 1), PP[i]) >= VD[i] ? F(0) : F(1) for i in 1:length(PP)]))
        end
        cocycle[i, j] = y
        cocycle[j, i] = y
      end
    end

    S = Tuple{elem_type(Q0), Generic.QuotientModuleElem{elem_type(F)}}[(id(Q0), zero(W))]
    Work = def ? typeof(P0)[ P0 ] : typeof(P0)[]
    p = 2
    sizW = dim(W) * characteristic(W.base_ring)
    while length(S) != order(Q0) * sizW
      while isempty(Work)
        p = next_prime(p)
        Work = ideal_type(R)[ QQ for QQ in support(p * R) if length(prime_decomposition(R, minimum(QQ))) == 2 && valuation(bad_prod, minimum(QQ)) == 0 ]
      end
      P = popfirst!(Work)
      c = q00\(EabstoE\P)
      i = findfirst(isequal(c), C)
      Iabs = EabstoE\P * inv(ideals[i])
      I = EabstoE(Iabs)
      J = I * inv(a(I))
      Jabs = EabstoE\J
      ok, x = isprincipal(Jabs)
      u = f(nnorm\(-(ff\FacElem(nf(RR)(norm(x))))))
      x = x * u
      @assert norm(x) == 1
      if evaluate(x) == 1
        y = zeros(F,length(PP))
      else
        y = [ valuation(EabstoE(evaluate(x) - 1), PP[i]) >= VD[i] ? F(0) : F(1) for i in 1:length(PP)]
      end
      idx = findfirst(isequal(P), PP)
      if idx !== nothing
        y = elem_type(F)[i == idx ? y[i] + 1 : y[i]  for i in 1:dim(V)]
      end
      elt = (c, w(V(y)))
      elt1 = elt
      o = 1
      siz = length(S)
      while !(elt1 in S)
        j = findfirst(isequal(elt1[1]), C)
        @assert !isnothing(j)
        for l in 1:siz
          elt2 = S[l]
          k = findfirst(isequal(elt2[1]), C)
          @assert !isnothing(k)
          prod = (elt1[1] + elt2[1], elt1[2] + elt2[2] + cocycle[j, k])
          if !(prod in S)
            push!(S, prod)
          end
        end
        elt1 = (elt[1] + elt1[1], elt[2] + elt1[2] + cocycle[i, j])
        o = o + 1
      end
      @assert length(S) == siz * o
      if o != 1
        push!(Gens, (P, o))
      end
    end
  end
  return Gens, def, P0
end

@doc Markdown.doc"""
    genus_representatives(L::HermLat; max = inf, use_auto = true,
                                                 use_mass = false)
                                                          -> Vector{HermLat}

Compute representatives for the isometry classes in the genus of $L$. At most 
`max` representatives are returned.

If `L` is definite, the use of the automorphism group of `L` is enabled by default.
It can be disabled by `use_auto = false`. In the case where `L` is indefinite, the entry 
`use_auto` has no effect. The computation of the mass can be enabled by `use_mass = true`.
"""
function genus_representatives(L::HermLat; max = inf, use_auto::Bool = true,
                                                      use_mass::Bool = false)
  @req rank(L) >= 2 "Lattice must have rank >= 2"
  R = base_ring(L)
  gens, def, P0 = genus_generators(L)
  a = involution(L)
  LL = typeof(L)[ L ]
  for g in gens
    if def && g[1] == P0
      continue
    end
    I = g[1]^Int(g[2] - 1)
    J = inv(a(I))
    N = neighbours_with_ppower(L, g[1], g[2] - 1)
    inter = typeof(L)[]
    for i in 2:length(LL)
      M = pseudo_matrix(LL[i])
      IM = _module_scale_ideal(I,M)
      JM = _module_scale_ideal(J,M)
      inter = append!(inter, lattice(ambient_space(L), _intersect_modules(_sum_modules(IM, pseudo_matrix(x)), JM) for x in N))
    end
    LL = vcat(LL, N, inter)
  end
  @assert length(LL) == prod(Int[g[2] for g in gens if !def || g[1] != P0])
  @assert all(X -> genus(X) == genus(L), LL)

  if use_mass
    mass = Hecke.mass(L)
  else
    mass = zero(fmpq)
  end

  missing_mass = Ref(mass)

  local result::Vector{typeof(L)}

  if def
    result = typeof(L)[]
    for L in LL
      neig = iterated_neighbours(L, P0, max = max, use_auto = use_auto, missing_mass = missing_mass)
      append!(result, neig)
      max = max - length(result)
    end
  else
    result = LL
  end
  return result
end

@doc Markdown.doc"""
    representatives(G::GenusHerm) -> Vector{HermLat}

Return representatives for the isometry classes in $G$.
"""
function representatives(G::GenusHerm)
  return genus_representatives(representative(G))
end

