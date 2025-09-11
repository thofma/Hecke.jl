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

@doc raw"""
    smallest_neighbour_prime(
      L::HermLat,
    ) -> Bool, RelNumFieldOrderIdeal, Vector{AbsNumFieldOrderIdeal}

Given a hermitian lattice ``L``, return `def, P0, bad` where:

- `def` is `true` if ``L`` is definite, else `false`;
- `P0` is a prime ideal in the base ring $O_E$ of ``L`` which is not bad,
  such that ``L`` is isotropic at $minimum(P0)$ and `P0` has smallest minimum
  among the primes satisfying these properties; if ``L`` is indefinite, `P0`
  is set to be the trivial ideal;
- `bad` is a vector of prime ideals $\mathfrak p$ in the fixed ring $O_K$ of
  ``L`` such that $L_{\mathfrak p}$ is not modular or $\mathfrak p$ is dyadic
  and is not coprime to the discriminant of $O_E$.
"""
function smallest_neighbour_prime(L::HermLat)
  S = base_ring(L)
  R = base_ring(S)
  lp = bad_primes(L)
  bad = ideal_type(R)[p for p in lp if !is_modular(L, p)[1] ]
  for (p,_) in factor(discriminant(S))
    if is_dyadic(p) && !(p in bad)
      push!(bad, p)
    end
  end

  if !is_definite(L)
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
      P = filter(p -> is_isotropic(L, p), P)
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
      if !is_coprime(QQ, I)
        continue
      end

      if is_isotropic(L, QQ)
        return true, QQ, bad
      end
    end
  end
  PP = prime_ideals_up_to(S, n)
  for QQ in PP
    if !is_coprime(QQ, I)
      continue
    end
    if is_isotropic(L, QQ)
      return true, QQ, bad
    end
  end
  error("Impossible")
end

function _neighbour(
    L::HermLat,
    B::MatElem,
    xG::FqMatrix,
    x::Vector,
    h::Map,
    P::NumFieldOrderIdeal,
    CC::NumFieldOrderIdeal,
    split::Bool,
  )
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

  @assert is_locally_isometric(L, LL, P)
  return LL
end

function neighbours(
    L::HermLat,
    P::RelNumFieldOrderIdeal,
    algorithm::Symbol = :orbit;
    rand_neigh::Int=75,
    callback::Function=(M -> M != L),
    inv_dict::Dict=Dict(),
    invariants::Function=(M -> []),
    use_mass::Bool=true,
    missing_mass::Base.RefValue{QQFieldElem}=Ref{QQFieldElem}(-1),
    vain::Base.RefValue{Int}=Ref{Int}(0),
    stop_after::IntExt=inf,
    max::IntExt=inf,
  )
  ok, scale = is_modular(L, P)
  @req ok "The lattice must be locally modular"
  @assert algorithm in [:orbit, :random, :exhaustive]
  R = base_ring(L)
  K = nf(R)
  a = involution(L)

  if use_mass
    __mass = missing_mass[]
  end

  T = local_basis_matrix(L, P; type=:submodule)
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
  k, h = residue_field(R, C)
  hext = extend(h, K)
  local form::dense_matrix_type(K)
  form = gram_matrix(ambient_space(L))
  special = false
  if scale != 0
    if is_ramified(R, minimum(P))
      special = isodd(scale)
      scale = div(scale + 1, 2)
    end
    # we rescale so that L things stay integral
    form = K(elem_in_nf(anti_uniformizer(minimum(P))))^(scale) * form
  end
  n = rank(L)
  W = vector_space(k, n)

  if algorithm == :orbit
    genUL = automorphism_group_generators(L)
    Tinv = inv(T)
    adjust_gens_mod_p = dense_matrix_type(k)[map_entries(hext, T*g*Tinv) for g in genUL]
    adjust_gens_mod_p = dense_matrix_type(k)[x for x in adjust_gens_mod_p if length(unique!(diagonal(x))) != 1]
    if length(adjust_gens_mod_p) > 0
      _LO = line_orbits(adjust_gens_mod_p)
      LO = Vector{eltype(k)}[x[1] for x in _LO]
      maxlines = length(LO)
    else
      LO = enumerate_lines(k, n)
      if length(LO) <= 50000
        algorithm = :exhaustive
        maxlines = length(LO)
      else
        algorithm = :random
        maxlines = min(rand_neigh, length(LO))
      end
    end
    @vprintln :GenRep 1 "$(maxlines) orbits of lines to try"
  else
    LO = enumerate_lines(k, n)
    maxlines = algorithm == :random ? min(rand_neigh, length(LO)) : length(LO)
    @vprintln :GenRep 1 "Try $(maxlines) lines"
  end

  result = typeof(L)[]

  if P != C
    _G = T * form * _map(transpose(T), a)
    G = map_entries(hext, _G)
    pi = p_uniformizer(P)
    pih = h(pi)
  elseif special
    pi = uniformizer(P)
    _G = elem_in_nf(pi) * T * form * _map(transpose(T), a)
    G = map_entries(hext, _G)
  else
    _G = T * form * _map(transpose(T), a)
    G = map_entries(hext, _G)
    ram = is_ramified(R, minimum(P))
    if ram
      pi = uniformizer(P)
      S = elem_type(R)[ h\x for x in k ]
    else
      p = minimum(P)
      pi = uniformizer(p)
      kp, hp = residue_field(order(p), p)
      hpext = extend(hp, base_field(K))
      alpha = h\(degree(k) == 1 ? one(k) : gen(k))
      Tram = matrix(kp, 2, 1, [2, hp(tr(alpha))])
    end
  end

  for i in 1:maxlines
    vain[] > stop_after && break
    if algorithm == :orbit
      w = LO[i]
    elseif algorithm == :random
      w = rand(LO)
    else
      w = next(LO)
    end

    if P != C
      x = elem_type(K)[ sum(T[i, j] * (hext\w[i]) for i in 1:n) for j in 1:ncols(T)]
      LL = _neighbour(L, T, pih * matrix(k, 1, length(w), w) * G, K(pi) .* x, hext, P, C, true)
      keep = callback(LL)
      if !keep
        vain[] += 1
        continue
      end
      vain[] = Int(0)
      @vprintln :GenRep 1 "Keep an isometry class"
      invLL = invariants(LL)
      if haskey(inv_dict, invLL)
        push!(inv_dict[invLL], LL)
      else
        inv_dict[invLL] = typeof(LL)[LL]
      end
      push!(result, LL)

      if use_mass
        s = automorphism_group_order(LL)
        sub!(__mass, __mass, 1//s)
        is_zero(__mass) && return result
      end

      length(result) == max && return result
    elseif special
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
      keep = callback(LL)
      if !keep
        vain[] += 1
        continue
      end
      vain[] = Int(0)
      @vprintln :GenRep 1 "Keep an isometry class"
      invLL = invariants(LL)
      if haskey(inv_dict, invLL)
        push!(inv_dict[invLL], LL)
      else
        inv_dict[invLL] = typeof(LL)[LL]
      end
      push!(result, LL)

      if use_mass
        s = automorphism_group_order(LL)
        sub!(__mass, __mass, 1//s)
        is_zero(__mass) && return result
      end

      length(result) == max && return result
    else
      __w = elem_type(K)[ (hext\w[i]) for i in 1:n]
      x = elem_type(K)[ sum(T[i, j] * (__w[i]) for i in 1:n if !iszero(w[i])) for j in 1:ncols(T)]
      nrm = _inner_product(form, x, x, a)
      @assert is_integral(nrm)
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
        b, s, V = can_solve_with_solution_and_kernel(Tram, matrix(kp, 1, 1, [hp(-el)]); side=:left)
        @assert b
        @assert s * Tram == matrix(kp, 1, 1, [hp(-el)])
        _kernel = FqMatrix[ matrix(kp, 1, 2, v) for v in _all_row_span(V)]
        l = a(hext\(inv(wG[ok])))
        S = elem_type(K)[ l * K((hpext\((s + v)[1])) + K(hpext\(s + v)[2])*alpha) for v in _kernel ]
      end
      for s in S
        LL = _neighbour(L, T, wG, elem_type(K)[x[o] + K(elem_in_nf(pi))*s*T[ok, o] for o in 1:ncols(T)], hext, P, P, false)
        keep = callback(LL)
        if !keep
          vain[] += 1
          continue
        end
        vain[] = Int(0)
        @vprintln :GenRep 1 "Keep an isometry class"
        invLL = invariants(LL)
        if haskey(inv_dict, invLL)
          push!(inv_dict[invLL], LL)
        else
          inv_dict[invLL] = typeof(LL)[LL]
        end
        push!(result, LL)

        if use_mass
          s = automorphism_group_order(LL)
          sub!(__mass, __mass, 1//s)
          is_zero(__mass) && return result
        end

        length(result) == max && return result
      end
    end
  end
  return result
end

@doc raw"""
    neighbours_with_ppower(
      L::HermLat,
      P::RelNumFieldOrderIdeal,
      e::Integer,
    ) -> Vector{HermLat}

Return a sequence of `P`-neighbours of length `e`, $L=L_1, L_2, \dots, L_e$ such that
$L_{i-1} \neq L_{i+1}$ for $i = 2, \dots, e-1$ (see [Kir19, Algorithm 4.7.]).
"""
function neighbours_with_ppower(
    L::HermLat,
    P::RelNumFieldOrderIdeal,
    e::IntegerUnion,
  )
  result = typeof(L)[]
  for i = 1:e
    if i == 1
      L = only(neighbours(L, P, :exhaustive; max=1, use_mass=false))
    else
      N = neighbours(L, P, :exhaustive; max=2, use_mass=false)
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

@doc raw"""
Given a degree 2 extension of number field E/K, with Eabs an absolute simple
number field isomorphic to E and R a maximal order in E, return the quotient
C/C_0 where C is the class group of E and C_0 is the subgroup of classes
consisting of s-invariant ideals. C_0 is generated by the ramified
primes in E, and the representatives in the class group of K.
We denote by s the generator of Gal(E/K)
"""
function _class_group_modulo_invariant_classes(
    EabstoE::NumFieldHom,
    R::NumFieldOrder,
  )
  D = different(R)
  Eabs = domain(EabstoE)
  Rabs = maximal_order(Eabs)
  C, h = class_group(Rabs)
  RR = base_ring(R)
  C0 = support(D)::Vector{ideal_type(R)}
  CC, hh = class_group(RR)
  for p in find_gens(pseudo_inv(hh), PrimesSet(2, -1))[1]
    P = sum(R * R(b) for b in basis(p); init=0*R)
    if !(P in C0)
      push!(C0, P)
    end
  end
  Q0, q0 = quo(C, elem_type(C)[ h\ideal(Rabs, [Rabs(EabstoE\b) for b in absolute_basis(i)]) for i in C0])
  q00 = pseudo_inv(q0) * h
  return Q0, q00
end

@doc raw"""
    genus_generators(
      L::HermLat,
    ) -> Vector{Tuple{RelNumFieldOrderIdeal, ZZRingElem}}, Bool, RelNumFieldOrderIdeal

Given a hermitian lattice ``L``, return `gens, def, P0` where:

- `gens` is a vector of tuples $(P,e)$ consisting of a prime ideal `P` in the
  base ring of ``L`` and an integer $e \geq 2$ which can be used to compute the
  ideal $\mathfrak A$ in line 11 of [Kir19, Algorithm 4.7.]);
- `def` is `true` if ``L`` is definite, else `false`;
- `P0` is a prime ideal in the base ring of ``L`` which is not bad, such that
  ``L`` is isotropic at $minimum(P0)$ and `P0` has smallest minimum among the
  primes satisfying these properties.
"""
function genus_generators(L::HermLat)
  R = base_ring(L)
  RR = fixed_ring(L)
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
  Q0, q00 = _class_group_modulo_invariant_classes(EabstoE, R)
  PP = ideal_type(R)[]

  local F::FqField

  local W::Generic.QuotientModule{FqFieldElem}

  if iseven(rank(L))
    for (P, e) in factor(D)
      p = minimum(P)
      G = genus(L, p)
      if any(i -> isodd(rank(G, i)), 1:length(G))
        continue
      elseif !is_dyadic(p)
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
      nnorm = hom(U, UU, FinGenAbGroupElem[ff\FacElem(nf(RR)(norm(f(U[i])))) for i in 1:ngens(U)])
      l = length(PP)
      VD = Int[ valuation(D, P) for P in PP ]
      K, k = kernel(nnorm)
      F = GF(2, cached = false)
      V = vector_space(F, length(PP))
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

  Gens = Tuple{ideal_type(R), ZZRingElem}[]

  if isempty(PP)
    S = FinGenAbGroupElem[]
    Q, q = quo(Q0, S)::Tuple{FinGenAbGroup, FinGenAbGroupHom}
    Work = def ? typeof(P0)[ P0 ] : typeof(P0)[]
    p = 2
    while order(Q) > 1
      while isempty(Work)
        p = next_prime(p)
        Work = ideal_type(R)[ QQ for QQ in support(p * R) if length(prime_decomposition(R,minimum(QQ))) == 2 && valuation(bad_prod, minimum(QQ)) == 0 ]
      end
      P = popfirst!(Work)
      c = (q00\(EabstoE\P))::FinGenAbGroupElem
      o = order(q(c))::ZZRingElem
      if !isone(o)
        push!(S, c)
        Q, q = quo(Q0, S)::Tuple{FinGenAbGroup, FinGenAbGroupHom}
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
        ok, x = is_principal_with_data(Jabs)
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
      ok, x = is_principal_with_data(Jabs)
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

@doc raw"""
   spinor_genera_in_genus(
     L::HermLat;
     max::IntExt=inf,
   ) -> Vector{HermLat}, RelNumFieldOrderIdeal

Given a hermitian lattice ``L``, return a complete list of representatives
for the spinor genera in the genus of ``L`` together with a good prime
ideal `P0` for the neighbours method. Namely `P0` is not a bad prime
for ``L``, the lattice ``L`` is isotropic at `minimum(P0)`, `P0` has
minimal norm with these properties, and neighbours construction at `P0`
preserve spinor genera.
"""
function spinor_genera_in_genus(
    L::HermLat;
    max::IntExt=inf,
  )
  @req rank(L) >= 2 "Lattice must have rank >= 2"
  s = denominator(scale(L))
  L = rescale(L, s)
  R = base_ring(L)
  gens, def, P0 = genus_generators(L)
  a = involution(L)
  res = typeof(L)[ L ]
  if max == 1
    return res
  end
  for g in gens
    if def && g[1] == P0
      continue
    end
    I = g[1]^Int(g[2] - 1)
    J = inv(a(I))
    N = neighbours_with_ppower(L, g[1], g[2] - 1)
    inter = typeof(L)[]
    for i in 2:length(res)
      M = pseudo_matrix(res[i])
      IM = _module_scale_ideal(I,M)
      JM = _module_scale_ideal(J,M)
      inter = append!(inter, lattice(ambient_space(L), _intersect_modules(_sum_modules(IM, pseudo_matrix(x)), JM)) for x in N)
    end
    res = vcat(res, N, inter)
  end
  @assert length(res) == prod(Int[g[2] for g in gens if !def || g[1] != P0])
  @assert all(X -> genus(X) == genus(L), res)

  n = min(max, length(res))
  return typeof(L)[rescale(res[i], 1//s) for i in 1:n], P0
end

function _short_vectors_trace_form(L::HermLat)
  LZ = restrict_scalars(L, QQ, one(base_field(L)))
  n = minimum(LZ)
  k = kissing_number(LZ)
  return n, k
end

function default_invariant_function(L::HermLat)
  s = automorphism_group_order(L)
  n, k = _short_vectors_trace_form(L)
  return (s, n, k)
end

@doc raw"""
    enumerate_definite_genus(known::Vector{HermLat}, algorithm::Symbol = :default) -> Vector{HermLat}, QQFieldElem
    enumerate_definite_genus(L::HermLat, algorithm::Symbol = :default) -> Vector{HermLat}
    enumerate_definite_genus(G::HermGenus, algorithm::Symbol = :default) -> Vector{HermLat}

Enumerate lattices in a given genus of definite hermitian lattices of rank at
least `2`, using Kneser's neighbour algorithm.

The output consists of a list of lattices representing the isometry classes
in the given genus.

For the first argument, one can choose to give directly a genus symbol ``G`` or
a lattice ``L`` in ``G``. Otherwise, one can give a list of known lattices
``G`` to continue an incomplete enumeration (in which case the lattices are
assumed to be in the same spinor genus).

The second argument gives the choice to which algorithm to use for the
enumeration. We currently support three algorithms:
- `:exhaustive` which enumerates all isotropic lines in the neighbour
  algorithm;
- `:orbit` which computes orbits of isotropic lines before constructing
  neighbours.
- `:random` which finds new isometry classes by constructing neighbours from
  random isotropic lines;
If `algorithm = :default`, the function chooses the most appropriate algorithm
depending on some invariants of the genus to be enumerated, and on the value
of the keyword argument `use_auto`.
* If `use_auto = true` and there are less than 900000 (default) lines to
  enumerate in the neighbour algorithm, then `algorithm` is set to `:orbit`;
* If `use_auto = false` and there are less than 50000 (default) libes to
  enumerate in the neighbour algorithm, then `algorithm` is set to
  `:exhaustive`;
* In all the other cases, `algorithm` is set to `:random`.
The number of lines to enumerate is decided via the choice of a prime ideal
of small norm for Kneser algorithm of neighbours, and the choice of this prime
ideal depends on the invariants of the genus to enumerate.

There are other possible extra optional arguments:
- `rand_neigh::Int` (default = `75`) -> for random enumeration, how many
  random neighbours are computed at each iteration;
- `invariant_function::Function` (default = `default_invariant_function`) -> a
  function to compute isometry invariants in order to avoid unnecessary isometry
  tests;
- `use_mass::Bool` (default = `true`) -> whether to use the mass formula as
  termination condition;
- `stop_after::IntExt` (default = `inf`) -> the algorithm stops after the
  specified amount of vain iterations without finding a new isometry class
  is reached;
- `max::IntExt` (default = `inf`) -> the algorithm stops after finding `max`
  new isometry classes.

In the case where one gives a list of `known` lattices in input, the output
list contains a copy of `known` together with any new lattice computed. The
extra output of the function is a rational number giving the portion of the
mass of the (spinor) genus which is missing. It is set to be `0` whenever the
mass is not used (`use_mass = false`).
Moreover, there are two other possible extra optional arguments:
- `distinct::Bool` (default = `false`) -> whether the lattices in `known` are
  known to be pairwise non-isometric;
- `missing_mass::QQFieldElem` (default = `nothing`) -> if `use_mass` and
  `distinct` are true, and the partial mass of `known` is known, gives what is
  the part of the mass which is missing;
If `distinct == false`, the function first compares all the lattices in `known`
to only keep one representative for each isometry class represented.

The `default_invariant_function` currently computes:
- the absolute length of a shortest vector in the trace form of the given
  lattice;
- the kissing number of the trace form of the given lattice, which is
  proportional to the number of vectors of shortest length;
- the order of the isometry group of the given lattice.
"""
enumerate_definite_genus(::Union{HermLat, HermGenus, Vector{HermLat}}, ::Symbol)

function enumerate_definite_genus(
    known::Vector{T},
    P::Union{RelNumFieldOrderIdeal, Nothing} = nothing,
    algorithm::Symbol = :default;
    rand_neigh::Int=75,
    distinct::Bool=false,
    invariant_function::Function=default_invariant_function,
    use_auto::Bool=true,
    use_mass::Bool=true,
    missing_mass::Union{QQFieldElem, Nothing}=nothing,
    vain::Base.RefValue{Int}=Ref{Int}(0),
    stop_after::IntExt=inf,
    max::IntExt=inf,
  ) where T <: HermLat
  @req !isempty(known) "Should know at least one lattice in the genus"
  @req all(LL -> genus(LL) == genus(known[1]), known) "Known lattices must be in the same genus"
  if algorithm != :default
    @req algorithm == :orbit || algorithm == :random || algorithm == :exhaustive "Only :exhaustive, :random and :orbit algorithms are currently implemented"
  end
  @req order(P) === base_ring(known[1]) "Arguments are incompatible"
  @req is_prime(P) "Second argument must be prime"
  @req !is_ramified(order(P), minimum(P)) || !Hecke.is_dyadic(minimum(P)) "Second argument cannot be a ramified prime over 2"
  @req is_modular(known[1], P)[1] "The lattices must be locally modular at P"
  @req rank(known[1]) >= 2 "The rank of the lattices must be at least 2"
  @req Hecke.is_isotropic(known[1], P) "The lattices must be locally isotropic at P"

  @req !is_finite(max) || max > 0 "max must be infinite or positive"

  if isnothing(P)
    _, P, _ = smallest_neighbour_prime(known[1])
  end
  res = copy(known)
  !distinct && _unique_iso_class!(res)

  L, itk = Iterators.peel(res)
  inv_lat = invariant_function(L)
  inv_dict = Dict{typeof(inv_lat), typeof(known)}(inv_lat => eltype(known)[L])
  for N in itk
    inv_lat = invariant_function(N)
    if haskey(inv_dict, inv_lat)
      push!(inv_dict[inv_lat], N)
    else
      inv_dict[inv_lat] = eltype(known)[N]
    end
  end

  function invariants(M::HermLat)
    for (I, Z) in inv_dict
      M in Z && return I
    end
    return invariant_function(M)
  end

  callback = function(M::HermLat)
    any(isequal(M), res) && return false
    invM = invariants(M)
    !haskey(inv_dict, invM) && return true
    keep = all(N -> !is_isometric(N, M), inv_dict[invM])
    return keep
  end

  if use_mass
    _mass = mass(L)
    if isnothing(missing_mass)
      found = sum(1//automorphism_group_order(M) for M in res; init=QQ(0))
      _missing_mass = Ref{QQFieldElem}(_mass-found)
    else
      _missing_mass = Ref{QQFieldElem}(missing_mass)
    end
  else
    _missing_mass = Ref{QQFieldElem}(-1)
  end

  r = rank(L)
  q = absolute_norm(P)

  if algorithm == :default
    nlines = divexact(ZZ(q)^r-1, q-1)
    if use_auto && nlines < 900000
      algorithm = :orbit
    elseif !use_auto && nlines <= 50000
      algorithm = :exhaustive
    else
      algorithm = :random
    end
  end

  count_new = Int(0)
  i = Int(0)
  while i != length(res) && count_new < max
    i += 1
    N = neighbours(
                   res[i],
                   P,
                   algorithm;
                   rand_neigh,
                   callback,
                   inv_dict,
                   invariants,
                   use_mass,
                   missing_mass=_missing_mass,
                   vain,
                   stop_after,
                   max
                  )

    if !is_empty(N)
      for M in N
        count_new += 1
        push!(res, M)
        if count_new >= max
          return res, _missing_mass[]
        end
      end
      use_mass && is_zero(_missing_mass[]) && break
      if use_mass
        @v_do :GenRep 2 perc = Float64(_missing_mass[]//_mass) * 100
        @vprintln :GenRep 2 "Lattices : $(length(res)), Target mass: $(_mass), Missing $(_missing_mass[]) ($(perc)%)"
      end
    elseif vain[] > stop_after
      break
    end
  end
  return res, _missing_mass[]
end

function enumerate_definite_genus(
    L::HermLat,
    algorithm::Symbol = :default;
    rand_neigh::Int=75,
    invariant_function::Function=default_invariant_function,
    use_auto::Bool=true,
    use_mass::Bool=true,
    stop_after::IntExt=inf,
    max::IntExt=inf,
  )
  @req is_definite(L) "Lattice must be definite"
  edg = typeof(L)[]
  sc = denominator(scale(L))
  _L = rescale(L, sc)

  spinor_genera, P0 = spinor_genera_in_genus(_L)

  for M in spinor_genera
    vain = Ref{Int}(0)
    if use_mass
      missing_mass = mass(M)//length(spinor_genera)
      s = automorphism_group_order(M)
      sub!(missing_mass, missing_mass, 1//s)
    else
      @req 0 < stop_after < inf "Need to provide a finite positive value for stop_after if the mass is not used. Otherwise the algorithm may eventually never stops"
      missing_mass = QQ(-1)
    end
    _edg = typeof(M)[M]
    while vain[] <= stop_after && length(edg) + length(_edg) < max
      use_mass && iszero(missing_mass) && break
      _edg, missing_mass = enumerate_definite_genus(
                                                    _edg,
                                                    P0,
                                                    algorithm;
                                                    distinct=true,
                                                    rand_neigh,
                                                    invariant_function,
                                                    use_auto,
                                                    use_mass,
                                                    missing_mass,
                                                    vain,
                                                    stop_after,
                                                    max=max-length(edg)-length(_edg)
                                                   )
    end
    append!(edg, _edg)
    length(edg) >= max && break
  end
  sc != 1 && map!(L -> rescale(L, 1//sc), edg, edg)
  return edg
end

function enumerate_definite_genus(
    G::HermGenus,
    algorithm::Symbol = :default;
    rand_neigh::Int=75,
    invariant_function::Function=default_invariant_function,
    use_auto::Bool=true,
    use_mass::Bool=true,
    stop_after::IntExt=inf,
    max::IntExt=inf,
  )
  L = representative(G)
  isone(max) && return typeof(L)[L]
  return enumerate_definite_genus(L, algorithm; rand_neigh, invariant_function, use_mass, stop_after, max)
end

@doc raw"""
    genus_representatives(L::HermLat) -> Vector{HermLat}

Return representatives for the isometry classes in the genus of the hermitian
lattice `L`. At most `max` representatives are returned.

If `L` is definite, the use of the automorphism group of `L` and of the mass
formula are enabled by default. For more flexibility on these two points,
one may call the function `enumerate_definite_genus` instead.
"""
function genus_representatives(
    L::HermLat;
    max::IntExt=inf,
    use_auto::Bool=true,
    use_mass::Bool=true,
  )
  if rank(L) == 0 || max == 1
    return typeof(L)[L]
  elseif rank(L) == 1
    # According to Proposition 2.9 of "Prime order isometries of
    # unimodular lattices and automorphisms of IHS manifolds" by
    # S. Brandhorst Al. Cattaneo, the set of isometry classes in
    # the genus of L is in bijection with the quotient J/J_0.
    #
    # We denote by s the generator of Gal(E/K),
    # by J the set of fractional ideals I of O_E such that I*s(I) = O_E
    # and by J_0 = {e O_E | e \in E: e*s(e) = 1 }.
    # To compute representatives of classes in J/J_0, we use the bijection
    #
    #                C/C_0 -> J/J_0, I -> I/s(I)
    #
    # where C is the class group of E and C_0 is the subgroup of classes
    # consisting of s-invariant ideals. C_0 is generated by the ramified
    # primes in E, and the representatives in the class group of K.
    #
    # The following piece of code is re-used from `genus_generators` above.
    E = base_field(L)
    R = base_ring(L)
    Eabs, EabstoE = absolute_simple_field(E)
    class_number(Eabs) == 1 && return typeof(L)[L] # C is trivial so there is only 1 class
    is_cm_field(Eabs)[1] && relative_class_number(Eabs) == 1 && return typeof(L)[L] # #(J/J_0) = h^-(E)
    Q0, q00 = _class_group_modulo_invariant_classes(EabstoE, R)
    CmodC0 = Hecke.ideal_type(R)[EabstoE(I) for I in q00.(collect(Q0))]
    s = involution(L)
    JmodJ0 = Hecke.fractional_ideal_type(R)[I*inv(s(I)) for I in CmodC0]
    n = min(max, length(JmodJ0))
    return typeof(L)[JmodJ0[i]*L for i in 1:n]
  end

  if is_definite(L)
    res = enumerate_definite_genus(L; use_auto, max, use_mass)
  else
    res, _ = spinor_genera_in_genus(L; max)
  end
  return res
end

@doc raw"""
    representatives(G::HermGenus) -> Vector{HermLat}

Given a global genus symbol `G` for hermitian lattices, return representatives
for the isometry classes of hermitian lattices in `G`.
"""
function representatives(G::HermGenus)
  return genus_representatives(representative(G))
end

