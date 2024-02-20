################################################################################
#
#  AbsSimpleNumFieldOrder/ResidueRingMultGrp.jl : Multiplicative group of Residue Rings
#
################################################################################

################################################################################
#
#  High Level Interface
#
################################################################################

@doc raw"""
    multiplicative_group(Q::AbsSimpleNumFieldOrderQuoRing) -> FinGenAbGroup, Map{FinGenAbGroup, AbsSimpleNumFieldOrderQuoRing}
    unit_group(Q::AbsSimpleNumFieldOrderQuoRing) -> FinGenAbGroup, Map{FinGenAbGroup, AbsSimpleNumFieldOrderQuoRing}

Returns the unit group of $Q$ as an abstract group $A$ and
an isomorphism map $f \colon A \to Q^\times$.
"""
function multiplicative_group(Q::AbsSimpleNumFieldOrderQuoRing)
  if !isdefined(Q, :multiplicative_group)
    if is_maximal_known_and_maximal(base_ring(Q))
      G, GtoQ = _multgrp(Q)
    else
      G, GtoQ = _multgrp_non_maximal(Q)
    end
    Q.multiplicative_group = GtoQ
  end
  mQ = Q.multiplicative_group::GrpAbFinGenToNfOrdQuoRingMultMap
  return domain(mQ), mQ
end

unit_group(Q::AbsSimpleNumFieldOrderQuoRing) = multiplicative_group(Q)

@doc raw"""
    multiplicative_group_generators(Q::AbsSimpleNumFieldOrderQuoRing) -> Vector{AbsSimpleNumFieldOrderQuoRingElem}

Return a set of generators for $Q^\times$.
"""
function multiplicative_group_generators(Q::AbsSimpleNumFieldOrderQuoRing)
  return multiplicative_group(Q).generators
end

# Factors Q.ideal, the result is saved in Q.factor
function factor(Q::AbsSimpleNumFieldOrderQuoRing)
  if !isdefined(Q, :factor)
    Q.factor = factor(Q.ideal)
  end
  return Q.factor
end


################################################################################
#
#  Internals
#
################################################################################

@doc raw"""
    _multgrp(Q::AbsSimpleNumFieldOrderQuoRing) -> (FinGenAbGroup, GrpAbFinGenToAbsOrdQuoRingMultMap)

Returns the group $Q^\times$ and a map from this group to $Q$.
"""
function _multgrp(Q::AbsSimpleNumFieldOrderQuoRing, save_tame_wild::Bool = false; method = nothing)

  fac = factor(Q)

  if isempty(fac)
    disc_log = function(x::AbsSimpleNumFieldOrderQuoRingElem)
      return ZZRingElem[]
    end
    GtoQ = GrpAbFinGenToAbsOrdQuoRingMultMap(Q, elem_type(Q)[], ZZRingElem[], disc_log)
    return domain(GtoQ), GtoQ
  end

  prime_powers = Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
  groups = Vector{FinGenAbGroup}()
  maps = Vector{GrpAbFinGenToNfOrdQuoRingMultMap}()
  tame_ind = Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}[]
  ind = 1
  for (p, vp) in fac
    pvp = p^vp
    G1, mG1 = _multgrp_mod_pv(p, vp, pvp; method = method)
    push!(tame_ind, (p, ind))
    ind += ngens(G1)
    push!(prime_powers, pvp)
    push!(groups, G1)
    push!(maps, mG1)
  end

  G, GtoQ = _direct_product(groups, maps, prime_powers, Q, save_tame_wild)
  S, StoG, StoQ = snf(G, GtoQ)

  if save_tame_wild
    for s = 1:length(tame_ind)
      StoQ.tame[tame_ind[s][1]].disc_log = StoG\(G[tame_ind[s][2]]) #Relies on the ordering tame\wild in the construction!
    end
  end

  return S, StoQ
end

################################################################################
#
#  Compute Multiplicative Group For Prime Powers
#
################################################################################

@doc raw"""
    _multgrp_mod_pv(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, v::Int, pv::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> (FinGenAbGroup, GrpAbFinGenToAbsOrdQuoRingMultMap)

Given a prime ideal $p$ in a maximal order $\mathcal O$, an integer $v > 0$ and
$pv = p^v$, the function returns the group $(\mathcal O/p^v)^\times$ and a map
from this group to $O/p^v$.
"""
function _multgrp_mod_pv(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, v::Int, pv::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}; method=nothing)
  @hassert :AbsOrdQuoRing 2 is_prime(p)
  @assert v >= 1
  pnumv = minimum(p, copy = false)^v # to speed up the exponentiation in the GrpAbFinGenToNfAbsOrdMaps
  G1, G1toO = _multgrp_mod_p(p, pnumv)
  Q, OtoQ = quo(order(p), pv)
  tame_part = Dict{AbsNumFieldOrderIdeal, GrpAbFinGenToNfAbsOrdMap}()
  wild_part = Dict{AbsNumFieldOrderIdeal, GrpAbFinGenToNfAbsOrdMap}()
  if v == 1
    G1toO.disc_log = G1[1]
    tame_part[p] = G1toO
    function disc_log(x::AbsSimpleNumFieldOrderQuoRingElem)
      return G1toO.discrete_logarithm((OtoQ\x))
    end
    GtoQ = GrpAbFinGenToAbsOrdQuoRingMultMap(G1, Q, map(OtoQ, G1toO.generators), disc_log)
  else
    G2, G2toO = _1_plus_p_mod_1_plus_pv(p, v, pv, pnumv; method = method)
    @assert is_snf(G2)
    wild_part[p] = G2toO
    gen1 = G1toO(G1[1])

    rel1 = exponent(G1)
    # G2.snf[end] is the order of the biggest cyclic subgroup of G2
    gen1_obcs = powermod(gen1, G2.snf[end], pnumv)
    gens = map(OtoQ, append!([gen1_obcs], G2toO.generators))

    G1toO.generators[1] = gen1_obcs

    G = direct_product(G1, G2, task = :none)

    G1toO.disc_log = G[1]
    tame_part[p] = G1toO

    obcs_inv = gcdx(G2.snf[end], rel1)[2]
    function disc_log2(x::AbsSimpleNumFieldOrderQuoRingElem)
      y = OtoQ\x
      r = mod((G1toO.discrete_logarithm(y))[1]*obcs_inv, rel1)
      y *= powermod(gen1_obcs, mod(-r, rel1), pnumv)
      return append!([r], G2toO.discrete_logarithm(y))
    end

    GtoQ = GrpAbFinGenToAbsOrdQuoRingMultMap(G, Q, gens, disc_log2)
  end
  GtoQ.tame = tame_part
  GtoQ.wild = wild_part
  return domain(GtoQ), GtoQ
end

################################################################################
#
#  Compute Multiplicative Group For Primes
#
################################################################################

# Compute (O_K/p)*
function _multgrp_mod_p(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, pnumv::ZZRingElem = ZZRingElem(0))
  @hassert :AbsOrdQuoRing 2 is_prime(p)
  O = order(p)
  n = norm(p) - 1
  gen = _primitive_element_mod_p(p)
  factor_n = factor(n)
  Q, mQ = residue_field(O, p)
  gen_quo = mQ(gen)
  big_step_cache = Dict{ZZRingElem, Dict{typeof(gen_quo), ZZRingElem}}()
  local discrete_logarithm
  let mQ = mQ, n = n, Q = Q, gen_quo = gen_quo, factor_n = factor_n, big_step_cache = big_step_cache
    function discrete_logarithm(x::AbsSimpleNumFieldOrderElem)
      y = mQ(x)
      if isone(y)
        return ZZRingElem[0]
      elseif y == Q(-1) && iszero(mod(n, 2))
        return ZZRingElem[divexact(n, 2)]
      end
      if n < 11
        res = 1
        el = gen_quo
        while el != y
          el *= gen_quo
          res += 1
          if res > n
            error("should not happen")
          end
        end
        return ZZRingElem[res]
      else
        return ZZRingElem[pohlig_hellman(gen_quo,n,y;factor_n=factor_n, big_step_cache = big_step_cache)]
      end
    end
  end
  map = GrpAbFinGenToNfAbsOrdMap(O, [ gen ], [ n ], discrete_logarithm, pnumv)
  return domain(map), map
end

function _primitive_element_mod_p(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  @hassert :AbsOrdQuoRing 2 is_prime(p)
  O = order(p)
  Q, Q_map = quo(O,p)
  n = norm(p) - 1
  primefactors_n = collect(keys(factor(n).fac))
  while true
    x = rand(Q)
    x == 0 && continue
    order_too_small = false
    for l in primefactors_n
      if isone(x^div(n, l))
        order_too_small = true
        break
      end
    end
    order_too_small || return Q_map\x
  end
end

################################################################################
#
# Computation of (1+p)/(1+p^v)
#
################################################################################

# Compute (1+p)/(1+p^v)
function _1_plus_p_mod_1_plus_pv(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, v::Int, pv::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, pnumv::ZZRingElem = ZZRingElem(0); method=nothing)
  @hassert :AbsOrdQuoRing 2 is_prime(p)
  @assert v >= 1

  if method == :quadratic
    gens, rels, disc_log = _iterative_method(p,v;base_method=:quadratic,use_p_adic=false)
  elseif method == :artin_hasse
    gens, rels, disc_log = _iterative_method(p,v;base_method=:artin_hasse,use_p_adic=false)
  elseif method == :p_adic
    gens, rels, disc_log = _iterative_method(p,v;use_p_adic=true)
  else
    gens, rels, disc_log = _iterative_method(p,v)
  end

  @assert size(rels) == (length(gens),length(gens))
  toO = GrpAbFinGenToNfAbsOrdMap(order(p), gens, rels, disc_log, pnumv)::GrpAbFinGenToAbsOrdMap{AbsSimpleNumFieldOrder, AbsSimpleNumFieldOrderElem}
  Q, OtoQ = quo(order(p), pv)
  S, mS, StoO = snf(toO, OtoQ)
  return S, StoO::GrpAbFinGenToAbsOrdMap{AbsSimpleNumFieldOrder, AbsSimpleNumFieldOrderElem}
end

################################################################################
#
#  Iterative Method for (1+p^u)/(1+p^v)
#
################################################################################

function _iterative_method(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, v::Int; base_method=nothing, use_p_adic=true)
  return _iterative_method(p, 1, v ; base_method = base_method, use_p_adic = use_p_adic)
end

function _iterative_method(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, u::Int, v::Int; base_method = nothing, use_p_adic = true)
  @assert v >= u >= 1
  pnum = minimum(p)
  if use_p_adic
    e = ramification_index(p)
    k0 = 1 + Int(div(ZZRingElem(e),(pnum-1)))::Int
  end
  g = Vector{AbsSimpleNumFieldOrderElem}()
  M = zero_matrix(FlintZZ, 0, 0)
  dlogs = Vector{Function}()

  l = u
  pl = (p^l)::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

  while l != v
    k = l
    pk = pl
    if use_p_adic && k>=k0
      l = v
      pl = p^l
      h, N, disc_log = _p_adic_method(p, k, l; pu = pk, pv = pl)::Tuple{Vector{AbsSimpleNumFieldOrderElem}, Vector{ZZRingElem}, Function}
    elseif base_method == :quadratic
      l = min(2*k, v)
      pl = p^l
      h, N, disc_log = _quadratic_method(p, k, l; pu = pk, pv = pl)::Tuple{Vector{AbsSimpleNumFieldOrderElem}, Vector{ZZRingElem}, Function}
    else
      l = Int(min(pnum*k, v))
      pl = p^l
      h, N, disc_log = _artin_hasse_method(p, k, l; pu = pk, pv = pl)::Tuple{Vector{AbsSimpleNumFieldOrderElem}, Vector{ZZRingElem}, Function}
    end
    g, M = _expand(g, M, h, N, disc_log, pl)
    push!(dlogs, disc_log)
  end

  Q = AbsSimpleNumFieldOrderQuoRing(order(pl), pl)
  local discrete_logarithm
  let Q = Q, dlogs = dlogs, pl = pl
    function discrete_logarithm(b::AbsSimpleNumFieldOrderElem)
      b1 = Q(b)
      a = ZZRingElem[]
      k1 = 1
      for i in 1:length(dlogs)
        a_ = dlogs[i](b1.elem)
        prod = one(Q)
        for j in 1:length(a_)
          if !iszero(a_[j])
            mul!(prod, prod, Q(g[k1])^a_[j])
          end
          k1 += 1
        end
        append!(a, a_)
        b1 = divexact(b1, prod)
      end
      return a
    end
  end

  return g, M, discrete_logarithm
end


#
# Given generators and relations for groups of two consecutives steps, this function computes
# generators and relations for the product
#
function _expand(g::Vector{AbsSimpleNumFieldOrderElem}, M::ZZMatrix, h::Vector{AbsSimpleNumFieldOrderElem}, N::Vector{ZZRingElem}, disc_log::Function, pl::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  if isempty(g)
    M1 = zero_matrix(FlintZZ, length(N), length(N))
    for i = 1:length(N)
      M1[i, i] = N[i]
    end
    return h, M1
  end
  isempty(h) && return g,M
  O = order(pl)
  Q , mQ = quo(O, pl)
  Z = zero_matrix(FlintZZ,nrows(M)+length(N),ncols(M)+length(N))
  for i = 1:nrows(M)
    for j = i:ncols(M)
      Z[i, j] = M[i, j]
    end
  end
  for i=1:length(N)
    Z[i+nrows(M),i+nrows(M)] = N[i]
  end
  for i in 1:nrows(M)
    el = one(Q)
    for j = 1:ncols(M)
      if !iszero(M[i, j])
        mul!(el, el, Q(g[j])^M[i, j])
      end
    end
    alpha = disc_log(el.elem)
    for j in 1:length(N)
      Z[i,j+ncols(M)] = -alpha[j]
    end
  end
  append!(g,h)

  return g, Z
end


#
#  This function returns a set of generators with the corresponding relations and disclog
#

function _pu_mod_pv(pu::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, pv::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})

  O=order(pu)
  b=basis(pu)
  N = basis_matrix(pv, copy = false)*basis_mat_inv(FakeFmpqMat, pu, copy = false)
  @assert isone(N.den)
  G = abelian_group(N.num)
  S, mS=snf(G)

  #Generators
  gens=Vector{AbsSimpleNumFieldOrderElem}(undef, ngens(S))
  for i=1:ngens(S)
    x=mS(S[i])
    gens[i]= zero(O)
    for j=1:ngens(G)
      add!(gens[i], gens[i], mod(x[j], S.snf[end])*b[j])
    end
  end

  #Disclog
  M = basis_mat_inv(FakeFmpqMat, pu, copy = false)*mS.imap
  x_fakemat2 = FakeFmpqMat(zero_matrix(FlintZZ, 1, ncols(M)), ZZRingElem(1))
  local disclog
  let M = M, O = O, S = S, x_fakemat2 = x_fakemat2
    function disclog(x::AbsSimpleNumFieldOrderElem)
      x_fakemat = FakeFmpqMat(matrix(FlintZZ, 1, degree(O), coordinates(x, copy = false)))
      mul!(x_fakemat2, x_fakemat, M)
      #@assert x_fakemat2 == x_fakemat * M
      denominator(x_fakemat2) != 1 && error("Element is in the ideal")
      res = Vector{ZZRingElem}(undef, ncols(x_fakemat2))
      for i = 1:length(res)
        res[i] = x_fakemat2.num[1, i]#mod(x_fakemat.num[1, i], S.snf[end])
      end
      return res
    end
  end
  return gens, S.snf, disclog

end

# Let p be a prime ideal above a prime number pnum. Let e = v_p(pnum) be
# its ramification index. If b > a >= e/(pnum-1) this function computes
# the structure of (1+p^a)/(1+p^b) as an abelian group.
function _1_plus_pa_mod_1_plus_pb_structure(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},a,b)
  b > a >= 1 || return false, nothing
  @hassert :AbsOrdQuoRing 2 is_prime(p)
  O = order(p)
  pnum = minimum(p)
  e = ramification_index(p)
  k0 = 1 + div(ZZRingElem(e),(pnum-1))
  a >= k0 || return false, nothing
  Q = AbsSimpleNumFieldOrderQuoRing(O,p^(b-a))
  return true, group_structure(Q)
end

################################################################################
#
# Quadratic Method for (1+p^u)/(1+p^v)
#
################################################################################

# Compute generators, a relation matrix and a function to compute discrete
# logarithms for (1+p^u)/(1+p^v), where 2*u >= v >= u >= 1
function _quadratic_method(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, u::Int, v::Int; pu::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}=p^u, pv::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}=p^v)
  @hassert :AbsOrdQuoRing 2 is_prime(p)
  @assert 2*u >= v >= u >= 1
  g, M, dlog = _pu_mod_pv(pu,pv)
  map!(x -> x + 1, g, g)
  function discrete_logarithm(x::AbsSimpleNumFieldOrderElem)
    res = dlog(mod(x-1,pv))
    for i = 1:length(res)
      res[i] = mod(res[i], M[end])
    end
    return res
  end
  return g, M, discrete_logarithm
end


################################################################################
#
# Artin-Hasse Method for (1+p^u)/(1+p^v)
#
################################################################################

# Compute generators, a relation matrix and a function to compute discrete
# logarithms for (1+p^u)/(1+p^v), where p is a prime ideal over pnum
# and pnum*u >= v >= u >= 1
function _artin_hasse_method(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, u::Int, v::Int; pu::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}=p^u, pv::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}=p^v)
  @hassert :AbsOrdQuoRing 2 is_prime(p)
  pnum = minimum(p)
  @assert pnum*u >= v >= u >= 1
  @assert ZZRingElem(v) <= pnum*ZZRingElem(u)
  @assert has_minimum(pv)
  Q, mQ = quo(order(p), pv)
  g, M, dlog = _pu_mod_pv(pu,pv)
  map!(x -> artin_hasse_exp(Q(x), pnum), g, g)
  local discrete_logarithm
  let Q = Q, pnum = pnum, dlog = dlog
    function discrete_logarithm(x::AbsSimpleNumFieldOrderElem)
      res = dlog(artin_hasse_log(Q(x), pnum))
      for i = 1:length(res)
        res[i] = mod(res[i], M[end])
      end
      return res
    end
  end
  return g, M, discrete_logarithm
end

function artin_hasse_exp(x::AbsSimpleNumFieldOrderQuoRingElem, pnum::ZZRingElem)
  Q = parent(x)
  s = Q(1)
  fac_i = ZZRingElem(1)
  t = Q(1)
  m = minimum(Q.ideal)
  for i=1:pnum-1
    mul!(t, t, x)
    if iszero(t)
      break
    end
    mul!(fac_i, fac_i, i)
    mod!(fac_i, fac_i, m)
    invfac_i = invmod(fac_i, m)
    add!(s, s, invfac_i*t)
  end
  return s.elem
end

function artin_hasse_log(y::AbsSimpleNumFieldOrderQuoRingElem, pnum::ZZRingElem)
  Q = parent(y)
  x = y - Q(1)
  if iszero(x)
    return x.elem
  end
  m = minimum(Q.ideal)
  s = Q(0)
  t = Q(1)
  for i in 1:pnum-1
    mul!(t, t, x)
    if iszero(t)
      break
    end
    invi = invmod(ZZRingElem(i), m)
    if iseven(i)
      sub!(s, s, invi*t)
    else
      add!(s, s, invi*t)
    end
  end
  return s.elem
end

################################################################################
#
# p-Adic Method for (1+p^u)/(1+p^v)
#
################################################################################

# Compute generators, a relation matrix and a function to compute discrete
# logarithms for (1+p)/(1+p^v) if 1 >= k0, where p is a prime ideal over pnum,
# e the p-adic valuation of pnum, and k0 = 1 + div(e,pnum-1)
function _p_adic_method(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, v::Int; pv=p^v)
  return _p_adic_method(p,1,v)
end

# Compute generators, a relation matrix and a function to compute discrete
# logarithms for (1+p^u)/(1+p^v) if u >= k0, where p is a prime ideal over pnum,
# e the p-adic valuation of pnum, and k0 = 1 + div(e,pnum-1)
function _p_adic_method(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, u::Int, v::Int; pu::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}=p^u, pv::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}=p^v)
  @assert v > u >= 1
  e = ramification_index(p) #ramification index
  k0 = 1 + div(ZZRingElem(e),(minimum(p)-1))
  @assert u >= k0
  g, M, dlog = _pu_mod_pv(pu, pv)
  O = order(p)
  Q = AbsSimpleNumFieldOrderQuoRing(O, pv)
  map!(x -> p_adic_exp(Q, p, v, x), g, g)
  powers = Dict{Int, AbsSimpleNumFieldElem}()
  local discrete_logarithm
  let Q = Q, p = p, v = v, dlog = dlog, powers = powers
    function discrete_logarithm(b::AbsSimpleNumFieldOrderElem)
      res = dlog(p_adic_log(Q, p, v, b, powers))
      for i = 1:length(res)
        res[i] = mod(res[i], M[end])
      end
      return res
    end
  end
  return g, M, discrete_logarithm
end

function _divexact(x::AbsOrdQuoRingElem, y::ZZRingElem)
  Q = parent(x)
  I = ideal(Q)
  OK = order(I)
  m = minimum(I, copy = false)
  s = invmod(y, m)
  res = s*x
  #@assert res == divexact(x, Q(y))
  return res
end


function p_adic_exp(Q::AbsSimpleNumFieldOrderQuoRing, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, v::Int, x::AbsSimpleNumFieldOrderElem)
  O = parent(x)
  iszero(x) && return one(O)
  pnum = p.minimum
  e = ramification_index(p)
  val_p_x = valuation(x, p)
  max_i = floor(Int, v / (val_p_x - (e/(Float64(pnum)-1)))) + 1
  val_p_maximum = Int(max_i*val_p_x) + 1
  Q_ = AbsSimpleNumFieldOrderQuoRing(O, p^val_p_maximum)
  x1 = Q_(x)
  s = one(Q)
  inc = one(Q_)
  val_p_xi = 0
  val_p_fac_i = 0
  i_old = 0
  for i in 1:max_i
    val_pnum_i = valuation(ZZRingElem(i), pnum)
    val_p_i = val_pnum_i * e
    val_p_fac_i += val_p_i
    val_p_xi += val_p_x
    val_p_xi - val_p_fac_i >= v && continue
    @hassert :AbsOrdQuoRing 1 val_p_xi - val_p_fac_i>=0
    @hassert :AbsOrdQuoRing 1 val_p_xi< val_p_maximum
    @hassert :AbsOrdQuoRing 1 val_p_fac_i< val_p_maximum
    i_prod = prod((i_old+1):i)
    deltax = inc*x1^(i-i_old)
    @hassert :AbsOrdQuoRing 1 !iszero(deltax)
    if isone(gcd(i_prod, pnum))
      inc = _divexact(deltax, ZZRingElem(i_prod))
    else
      inc = divexact(deltax, Q_(i_prod))
    end
    add!(s, s, Q(inc.elem))
    i_old = i
  end
  return s.elem
end

function p_adic_log(Q::AbsSimpleNumFieldOrderQuoRing, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, v::Int, y::AbsSimpleNumFieldOrderElem, powers::Dict{Int, AbsSimpleNumFieldElem} = Dict{Int, AbsSimpleNumFieldElem}())
  O = parent(y)
  isone(y) && return zero(O)
  pnum = minimum(p)
  x = y - 1
  val_p_x = valuation(x, p)
  s = zero(Q)
  xi = one(O)
  i_old = 0
  val_p_xi = 0
  anti_uni = anti_uniformizer(p)
  e = ramification_index(p)
  #we have to find a bound for this.
  # it is enough to find the minimum l such that
  # pnum^l v_p(x)>= v+el
  l = 1
  left = pnum*val_p_x
  right=v+e
  while left < right
    left*=pnum
    right+=e
    l+=1
  end
  bound2=pnum^l-pnum
  bound1 = div(v, val_p_x)
  leftlim = bound1 + pnum - mod(ZZRingElem(bound1), pnum)
  for i in 1:bound1
    val_pnum_i = valuation(i, pnum)
    val_p_i = val_pnum_i * e
    val_p_xi += val_p_x
    val_p_xi - val_p_i >= v && continue
    mul!(xi, xi, x^(i-i_old))
    if iszero(val_pnum_i)
      inc = _divexact(Q(xi), ZZRingElem(i))
    else
      if haskey(powers, val_p_i)
        el = powers[val_p_i]
      else
        el = _powermod(anti_uni, val_p_i, pnum^(val_p_i+1))
        powers[val_p_i] = el
      end
      numer = O(xi.elem_in_nf*el, false)
      denom = O(i*el, false)
      inc = divexact(Q(numer),Q(denom))
    end
    if isodd(i)
      add!(s, s, inc)
    else
      sub!(s, s, inc)
    end
    i_old = i
  end
  for i in leftlim:pnum:bound2
    val_pnum_i = valuation(i, pnum)
    val_p_i = val_pnum_i * e
    val_p_xi += val_p_x
    val_p_xi - val_p_i >= v && continue
    mul!(xi, xi, x^(i-i_old))
    if iszero(val_pnum_i)
      inc = _divexact(Q(xi), ZZRingElem(i))
    else
      if haskey(powers, val_p_i)
        el = powers[val_p_i]
      else
        el = _powermod(anti_uni, val_p_i, pnum^(val_p_i+1))
        powers[val_p_i] = el
      end
      numer = O(xi.elem_in_nf*el, false)
      denom = O(i*el, false)
      inc = divexact(Q(numer),Q(denom))
    end
    if isodd(i)
      add!(s, s, inc)
    else
      sub!(s, s, inc)
    end
    i_old = i
  end
  return s.elem
end

################################################################################
#
#  Discrete Logarithm In Cyclic Groups
#
################################################################################
# TODO compare with implementations in UnitsModM.jl

@doc raw"""
    baby_step_giant_step(g, n, h) -> ZZRingElem
    baby_step_giant_step(g, n, h, cache::Dict) -> ZZRingElem

Computes the discrete logarithm $x$ such that $h = g^x$.

$g$ is a generator of order less than or equal to $n$
and $h$ has to be generated by $g$.
If a dictionary `cache` is supplied, it will be used to store the result
of the first step. This allows to speed up subsequent calls with
the same $g$ and $n$.
"""
function baby_step_giant_step(g, n, h, cache::Dict)
  @assert typeof(g) == typeof(h)
  m = ZZRingElem(isqrt(n) + 1)
  if isempty(cache)
    it = g^0
    for j in 0:m
      cache[it] = j
      it *= g
    end
  end
  b = g^(-m)
  y = h
  for i in 0:m-1
    if haskey(cache, y)
      return ZZRingElem(mod(i*m + cache[y], n))
    else
      y *= b
    end
  end
  error("Couldn't find discrete logarithm")
end

function baby_step_giant_step(gen, n, a)
  cache = Dict{typeof(gen), BigInt}()
  return baby_step_giant_step(gen, n, a, cache)
end

@doc raw"""
    pohlig_hellman(g, n, h; factor_n=factor(n)) -> ZZRingElem

Computes the discrete logarithm $x$ such that $h = g^x$.

$g$ is a generator of order $n$ and $h$ has to be generated by $g$.
The factorisation of $n$ can be supplied via `factor_n` if
it is already known.
"""
function pohlig_hellman(g, n, h; factor_n=factor(n), big_step_cache = Dict())
  @assert typeof(g) == typeof(h)
  n == 1 && return ZZRingElem(0)
  results = Vector{ZZRingElem}()
  prime_powers = Vector{ZZRingElem}()
  for (p,v) in factor_n
    pv = p^v
    r = div(n,pv)
    if !haskey(big_step_cache, p)
      big_step_cache[p] = Dict{typeof(g), ZZRingElem}()
    end
    c = _pohlig_hellman_prime_power(g^r,p,v,h^r, big_step_cache = big_step_cache[p])
    push!(results, ZZRingElem(c))
    push!(prime_powers, ZZRingElem(pv))
  end
  if length(results) == 1
    return results[1]
  end
  return crt(results, prime_powers)
end

function _pohlig_hellman_prime_power(g, p, v, h; big_step_cache::Dict)
  p_i = 1
  p_v_min_i_min_1 = p^(v-1)
  g_ = g^(p^(v-1))
  a = baby_step_giant_step(g_,p,h^(p^(v-1)), big_step_cache)
  h *= g^-a
  for i in 1:v-1
    p_i *= p
    p_v_min_i_min_1 = div(p_v_min_i_min_1,p)
    ai = baby_step_giant_step(g_, p , h^p_v_min_i_min_1, big_step_cache)
    ai_p_i = ai * p_i
    a += ai_p_i
    h *= g^(-ai_p_i)
  end
  return a
end

#################################################################################
#
#  p-part of the multiplicative group
#
#################################################################################

function _prime_part_multgrp_mod_p(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, prime::Int)
  @hassert :AbsOrdQuoRing 2 is_prime(p)
  O = order(p)
  Q, mQ = residue_field(O,p)

  n = norm(p) - 1
  s=valuation(n,prime)
  powerp=prime^s
  m=divexact(n,powerp)

  powm=divexact(powerp,prime)
  found=false
  g=Q(1)
  while found==false
    g = rand(Q)
    if g != Q(0)
      g=g^m
      if g^powm != Q(1)
        found=true
      end
    end
  end
  inv=gcdx(m,ZZRingElem(powerp))[2]

  function disclog(x::AbsSimpleNumFieldOrderElem)
    t=mQ(x)^m
    if powerp<10
      w=1
      el=g
      while el!=t
        w+=1
        el*=g
      end
      return ZZRingElem[w*inv]
    else
      return ZZRingElem[_pohlig_hellman_prime_power(g,prime,s,t)*inv]
    end
  end

  map = GrpAbFinGenToNfAbsOrdMap(O, [ mQ\g ], [ ZZRingElem(powerp) ], disclog)
  return domain(map), map
end


function _mult_grp(Q::AbsSimpleNumFieldOrderQuoRing, p::Integer)
  O = Q.base_ring
  OtoQ = NfOrdQuoMap(O, Q)

  tame_part = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, GrpAbFinGenToNfAbsOrdMap}()
  wild_part = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, GrpAbFinGenToNfAbsOrdMap}()

  fac = factor(Q)
  y1 = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
  y2 = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
  for (q, e) in fac
    if is_divisible_by(norm(q) - 1, p)
      y1[q] = Int(1)
    else
      if is_divisible_by(norm(q), p) && e >= 2
        y2[q] = Int(e)
      end
    end
  end

  if isempty(y1) && isempty(y2)
    G = abelian_group(ZZRingElem[])
    disc_log = function(x::AbsSimpleNumFieldOrderQuoRingElem)
      return ZZRingElem[]
    end
    return G, GrpAbFinGenToAbsOrdQuoRingMultMap(G, Q, elem_type(Q)[], disc_log), y1
  end

  ideals_and_maps = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Vector{GrpAbFinGenToNfAbsOrdMap}}()
  for (q, e) in fac
    qe = q^e
    maps = GrpAbFinGenToNfAbsOrdMap[]

    if haskey(y1, q)
      G1, G1toO = _prime_part_multgrp_mod_p(q, p)
      push!(maps, G1toO)
      tame_part[q] = G1toO
    end

    if haskey(y2, q)
      G2, G2toO = _1_plus_p_mod_1_plus_pv(q, y2[q], q^y2[q])

      nq = norm(q) - 1

      @assert is_snf(G2)
      obcs = G2.snf[end] # order of the biggest cyclic subgroup
      obcs_inv = gcdx(nq, obcs)[2]

      disc_log2 = function(x::AbsSimpleNumFieldOrderElem)
        y = Q(x)^Int(nq)
        z = G2toO.discrete_logarithm(y.elem)
        for i = 1:length(z)
          z[i] *= obcs_inv
        end
        return z
      end

      G2toO2 = GrpAbFinGenToNfAbsOrdMap(G2, O, G2toO.generators, disc_log2)
      push!(maps, G2toO2)
      wild_part[q] = G2toO2
    end
    ideals_and_maps[qe] = maps
  end
  G, GtoQ = _direct_product!(ideals_and_maps, Q) # This also changes tame_part and wild_part!
  GtoQ.tame = tame_part
  GtoQ.wild = wild_part

  S, StoG, StoQ = snf(G, GtoQ)

  return S, StoQ, merge(y1, y2)
end

####################################################################################
#
#  multiplicative group mod n
#
####################################################################################

function _find_gen(Q::Union{FqPolyRepField, FqField}, powm::Vector{ZZRingElem}, m::ZZRingElem)
  found = false
  g = one(Q)
  while !found
    g = rand(Q)
    !iszero(g) || continue
    g = g^m
    found = true
    for i=1:length(powm)
      if isone(g^powm[i])
        found = false
        break
      end
    end
  end
  return g
end


function _n_part_multgrp_mod_p(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, n::Int)
  @hassert :AbsOrdQuoRing 2 is_prime(p)
  O = order(p)
  Q, mQ = residue_field(O, p)

  np = norm(p) - ZZRingElem(1)
  @assert !isone(gcd(ZZRingElem(n), np))
  npart, m = ppio(np, ZZRingElem(n))
  k = gcd(npart, ZZRingElem(n))
  fac = factor(k)
  powm = ZZRingElem[divexact(npart, x) for x in keys(fac.fac)]

  #
  #  We search for a random element with the right order
  #
  g = _find_gen(Q, powm, m)
  inv = gcdx(m, npart)[2]
  quot = divexact(npart, k)

  w = g^quot
  local disclog
  let m = m, quot = quot, k = k, w = w, inv = inv
    function disclog(x::AbsSimpleNumFieldOrderElem)
      t = mQ(x)^(m*quot)
      if iszero(t)
        error("Not coprime!")
      end
      if isone(t)
        return ZZRingElem[ZZRingElem(0)]
      end
      if k < 20
        s = 1
        el = deepcopy(w)
        while el != t
          s += 1
          mul!(el, el, w)
        end
        return ZZRingElem[mod(ZZRingElem(s)*inv, k)]
      else
        return ZZRingElem[pohlig_hellman(w, k, t)*inv]
      end
    end
  end
  G = abelian_group([k])
  gens = Vector{AbsSimpleNumFieldOrderElem}(undef, 1)
  gens[1] = preimage(mQ, g)
  map = GrpAbFinGenToNfAbsOrdMap(G, O, gens, disclog)::GrpAbFinGenToAbsOrdMap{AbsSimpleNumFieldOrder, AbsSimpleNumFieldOrderElem}
  return G, map
end


#Cohen, Advanced topics in computational number theory, 4.5 exercise 20
function bound_exp_mult_grp(P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, n::Int)
  @assert is_prime(P)
  e = ramification_index(P)
  f = degree(P)
  p = minimum(P, copy = false)
  s = valuation(n, p)
  return Int((p^s)-1+s*p^s)
end


function _mult_grp_mod_n(Q::AbsSimpleNumFieldOrderQuoRing, y1::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}, y2::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}, n::Integer)

  O = Q.base_ring
  idQ = Q.ideal
  OtoQ = NfOrdQuoMap(O, Q)
  fac = factor(Q)

  tame_part = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, GrpAbFinGenToNfAbsOrdMap}()
  wild_part = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, GrpAbFinGenToNfAbsOrdMap}()

  if isempty(y1) && isempty(y2)
    G = abelian_group(ZZRingElem[])
    disc_log = function(x::AbsSimpleNumFieldOrderQuoRingElem)
      return ZZRingElem[]
    end
    return G, GrpAbFinGenToAbsOrdQuoRingMultMap(G, Q, elem_type(Q)[], disc_log), tame_part, wild_part
  end

  ideals_and_maps = Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Vector{GrpAbFinGenToNfAbsOrdMap}}[]
  tame_ind = Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}[]
  i = 0
  for (q, e) in fac
    qe = q^e
    maps = GrpAbFinGenToNfAbsOrdMap[]

    if haskey(y1, q)
      G1, G1toO = _n_part_multgrp_mod_p(q, n)
      push!(maps, G1toO)
      tame_part[q] = G1toO
      i += 1
      push!(tame_ind, (q, i))
    end

    if haskey(y2, q)
      @assert y2[q] >= 2
      #exp_q = min(y2[q], bound_exp_mult_grp(q, n))
      G2, G2toO = _1_plus_p_mod_1_plus_pv(q, y2[q], qe)
      if haskey(y1, q)
        e = exponent(G2)
        uncom = Int(ppio(ZZRingElem(n), e)[2])
        e1 = e
        while !isone(mod(e1, uncom))
          e1 *= e
        end
        tame_part[q].generators[1] = powermod(tame_part[q].generators[1], e1, minimum(idQ, copy = false))
      end

      i += ngens(G2)
      nq = norm(q) - 1

      @assert is_snf(G2)
      obcs = G2.snf[end] # order of the biggest cyclic subgroup
      obcs_inv = gcdx(nq, obcs)[2]

      local disc_log2
      let Q = Q, nq = nq, G2toO = G2toO
        function disc_log2(x::AbsSimpleNumFieldOrderElem)
          y = Q(x)^nq
          z = G2toO.discrete_logarithm(y.elem)
          for i = 1:length(z)
            z[i] *= obcs_inv
          end
          return z
        end
      end

      G2toO2 = GrpAbFinGenToNfAbsOrdMap(G2, O, G2toO.generators, disc_log2)::GrpAbFinGenToAbsOrdMap{AbsSimpleNumFieldOrder, AbsSimpleNumFieldOrderElem}
      push!(maps, G2toO2)
      wild_part[q] = G2toO2
    end
    push!(ideals_and_maps, (qe, maps))
  end
  G, GtoQ = _direct_product!(ideals_and_maps, Q) # This also changes tame_part and wild_part!

  S, StoG, StoQ = snf(G, GtoQ)

  for s = 1:length(tame_ind)
    tame_part[tame_ind[s][1]].disc_log = StoG\(G[tame_ind[s][2]])
  end
  StoQ.tame = tame_part
  StoQ.wild = wild_part
  return S, StoQ
end

################################################################################
#
#  Functions for the non-maximal case
#
################################################################################

# Computes generators and relations for (O_P/AO_P)^\times, where Pm = P^m, Q = O/A.
function _multgrp_Op_aOp(Q::AbsSimpleNumFieldOrderQuoRing, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, m::Int, Pm::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  A = ideal(Q)
  O = order(A)

  # Compute generators for (1 + (A + P^m))/(1 + P^m)
  I = A + Pm
  I2 = I^2
  S = Set{AbsSimpleNumFieldOrderElem}()
  j = 0
  k = floor(Int, log(2, m))
  while j <= k
    if j > 0
      I = I2
      I2 = I2^2
    end
    for b in basis(I)
      push!(S, mod(b, I2))
    end
    j += 1
  end
  O1 = order(A)(1)
  gens = [ g + O1 for g in S ]

  # Compute (O/P^m)^\times
  G, GtoQQ = _multgrp_mod_pv(P, m, Pm, method = :quadratic)
  QQ = codomain(GtoQQ)
  OtoQQ = NfOrdQuoMap(O, QQ)

  H, GtoH = quo(G, [ GtoQQ\OtoQQ(g) for g in gens])
  @assert GtoH.map == identity_matrix(FlintZZ, ngens(G))
  HtoQQ = GrpAbFinGenToAbsOrdQuoRingMultMap(H, QQ, GtoQQ.generators, GtoQQ.discrete_logarithm)

  return H, HtoQQ
end

function _multgrp_non_maximal(Q::AbsSimpleNumFieldOrderQuoRing)
  A = ideal(Q)
  O = order(A)

  # Determine the prime ideals containing A
  OO = maximal_order(nf(O))
  aOO = extend(A, OO)
  fac = factor(aOO)
  S = Set{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
  for (p, e) in fac
    q = contract(p, O)
    q.is_prime = p.is_prime
    push!(S, q)
  end
  prime_ideals = [ p for p in S ]

  # Compute (upper bounds for) exponents m such that A*O_P \supseteq P^m*O_P
  m = Vector{Int}(undef, length(prime_ideals))
  for i = 1:length(m)
    P = prime_ideals[i]
    p = minimum(P)
    x = valuation(det(basis_matrix(A, copy = false)), p)
    y = valuation(det(basis_matrix(P, copy = false)), p)
    m[i] = Int(ceil(x/y))
  end

  # Compute the groups (O_P/AO_P)^\times
  Pm = [ prime_ideals[i]^m[i] for i in 1:length(prime_ideals)]
  groups = Vector{FinGenAbGroup}(undef, length(prime_ideals))
  maps = Vector{GrpAbFinGenToNfOrdQuoRingMultMap}(undef, length(prime_ideals))
  for i= 1:length(prime_ideals)
    H, HtoQQ = _multgrp_Op_aOp(Q, prime_ideals[i], m[i], Pm[i])
    groups[i] = H
    maps[i] = HtoQQ
  end

  G, GtoQ = _direct_product(groups, maps, Pm, Q)

  S, StoG, StoQ = snf(G, GtoQ)
  return S, StoQ
end

################################################################################
#
#  SNF and direct product (which transform the map too)
#
################################################################################

# For an element x of elements[i] this computes an element y with
# x \equiv y mod ideals[i] and x \equiv 1 mod ideals[j] for all j not equal i.
function make_coprime(elements::Vector{Vector{S}}, ideals::Vector{T}) where { S <: Union{ AbsNumFieldOrderElem, AlgAssAbsOrdElem }, T <: Union{ AbsNumFieldOrderIdeal, AlgAssAbsOrdIdl } }
  @assert !isempty(ideals)
  @assert length(elements) == length(ideals)

  n = length(ideals)
  if n == 1
    return elements[1]
  end

  products = _compute_products_for_make_coprime(ideals)

  One = one(order(ideals[1]))
  result = Vector{S}()
  for i = 1:n
    u, v = idempotents(ideals[i], products[i])
    for j = 1:length(elements[i])
      t = elements[i][j] * v + One * u
      push!(result, t)
    end
  end
  return result
end

# Build the products \prod_{j\neq i} ideals[j] for all i
function _compute_products_for_make_coprime(ideals::Vector{T}) where { T <: Union{ AbsNumFieldOrderIdeal, AlgAssAbsOrdIdl } }
  n = length(ideals)
  @assert n >= 2

  left_halves = Vector{T}(undef, n - 1)
  right_halves = Vector{T}(undef, n - 1)
  left_halves[1] = ideals[1]
  right_halves[1] = ideals[n]
  for i = 2:(n - 1)
    left_halves[i] = left_halves[i - 1]*ideals[i]
    right_halves[i] = right_halves[i - 1]*ideals[n - i + 1]
  end
  products = Vector{T}(undef, n)
  products[1] = right_halves[n - 1]
  products[n] = left_halves[n - 1]
  for i = 2:(n - 1)
    products[i] = left_halves[i - 1]*right_halves[n - i]
  end
  return products
end

# Returns the SNF S of G and a map from S to G and one from S to codomain(GtoR).
# If RtoQ is given, then the generators of S are computed modulo codomain(RtoQ).
# It is assumed, that codomain(GtoR) == domain(RtoQ) in this case.
function snf(G::FinGenAbGroup, GtoR::Union{GrpAbFinGenToAbsOrdQuoRingMultMap, GrpAbFinGenToAbsOrdMap}, modulo_map::AbsOrdQuoMap...)
  S, StoG = snf(G)

  R = codomain(GtoR)

  if ngens(G) == 0
    StoR = typeof(GtoR)(S, R, GtoR.generators, GtoR.discrete_logarithm)
    return S, StoG, StoR
  end

  function disclog(x)
    @assert parent(x) === R
    y = GtoR.discrete_logarithm(x)
    a = StoG\(G(y))
    return ZZRingElem[ a[j] for j = 1:ngens(S) ]
  end

  modulo = (length(modulo_map) == 1)
  if modulo
    RtoQ = modulo_map[1]
  end

  gens_snf = Vector{elem_type(R)}(undef, ngens(S))
  for i = 1:ngens(S)
    x = StoG(S[i]).coeff
    for j = 1:ngens(G)
      x[1, j] = mod(x[1, j], S.snf[end])
    end
    modulo ? y = one(codomain(RtoQ)) : y = one(R)
    for j = 1:ngens(G)
      if modulo
        y *= RtoQ(GtoR.generators[j])^(x[1, j])
      else
        y *= GtoR.generators[j]^(x[1, j])
      end
    end
    modulo ? gens_snf[i] = RtoQ\y : gens_snf[i] = y
  end

  if isdefined(GtoR, :modulus)
    StoR = typeof(GtoR)(S, R, gens_snf, disclog, GtoR.modulus)
  else
    StoR = typeof(GtoR)(S, R, gens_snf, disclog)
  end

  if isdefined(GtoR, :tame)
    StoR.tame = GtoR.tame
  end
  if isdefined(GtoR, :wild)
    StoR.wild = GtoR.wild
  end

  return S, StoG, StoR
end

snf(GtoR::Union{GrpAbFinGenToAbsOrdQuoRingMultMap, GrpAbFinGenToAbsOrdMap}, modulo_map::AbsOrdQuoMap...) = snf(domain(GtoR), GtoR, modulo_map...)

# Let QG = codomain(GtoQ) and QH = codomain(HtoQ) with QG = O/I and QH = O/J.
# This function returns the direct product of G and H and a map from the
# product to O/(IJ).
# It is assumed that I and J are coprime.
function direct_product(G::FinGenAbGroup, GtoQ::GrpAbFinGenToAbsOrdQuoRingMultMap, H::FinGenAbGroup, HtoQ::GrpAbFinGenToAbsOrdQuoRingMultMap)
  return direct_product([G, H], [GtoQ, GtoH])
end

# Let G_i be the groups and Q_i be the codomains of the maps such that
# Q_i = O/I_i for ideals I_i.
# This function returns the direct product of the G_i, a map from the
# product to O/(\prod_i I_i) and a map from O to this quotient.
# It is assumed that the ideals I_i are coprime.
function direct_product(groups::Vector{FinGenAbGroup}, maps::Vector{T}) where T <: GrpAbFinGenToAbsOrdQuoRingMultMap
  @assert length(groups) == length(maps)
  @assert length(groups) != 0

  if length(groups) == 1
    Q = codomain(maps[1])
    return groups[1], maps[1], AbsOrdQuoMap(base_ring(Q), Q)
  end

  ideals = Vector{typeof(ideal(codomain(maps[1])))}(undef, length(maps))
  for i = 1:length(maps)
    ideals[i] = ideal(codomain(maps[i]))
  end

  O = order(ideals[1])
  @assert all([ order(ideals[i]) == O for i = 1:length(ideals) ])
  Q, OtoQ = quo(O, prod(ideals))
  return _direct_product(groups, maps, ideals, Q)..., OtoQ
end

# This function returns the direct product of the G_i and a map from the
# product to Q.
function direct_product(groups::Vector{FinGenAbGroup}, maps::Vector{T}, Q::AbsOrdQuoRing) where T <: GrpAbFinGenToAbsOrdQuoRingMultMap
  @assert length(groups) == length(maps)
  @assert length(groups) != 0

  ideals = Vector{ideal_type(base_ring(Q))}(undef, length(maps))
  for i = 1:length(maps)
    ideals[i] = ideal(codomain(maps[i]))
  end
  return _direct_product(groups, maps, ideals, Q)
end

# This function does NOT require length(group) == length(ideals), but only
# length(groups) <= length(ideals). The generators of groups[i] will be made
# coprime to ALL ideals except ideals[i] in any case.
# If tame_wild is true, it is assumed, that for each map in maps the field tame
# is defined and contains exactly one key. The returned map will then contain
# a dictionary of all given tame respectively wild parts with changed generators.
function _direct_product(groups::Vector{FinGenAbGroup}, maps::Vector{U}, ideals::Vector{T}, Q::AbsOrdQuoRing{S, T}, tame_wild::Bool = false) where {S, T, U <: GrpAbFinGenToAbsOrdQuoRingMultMap}
  @assert length(groups) == length(maps)
  @assert length(groups) != 0
  @assert length(ideals) >= length(groups)

  if length(groups) == 1 && length(ideals) == 1
    if codomain(maps[1]) === Q
      return groups[1], maps[1]
    end

    gens = map(Q, [ g.elem for g in maps[1].generators ])

    local disc_log1
    let maps = maps
      function disc_log1(x::AbsOrdQuoRingElem)
        xx = codomain(maps[1])(x.elem)
        return maps[1].discrete_logarithm(xx)
      end
    end

    m = GrpAbFinGenToAbsOrdQuoRingMultMap(groups[1], Q, gens, disc_log1)
    if tame_wild
      m.tame = maps[1].tame
      m.wild = maps[1].wild
    end
    return groups[1], m
  end

  G = direct_product(groups..., task = :none)::FinGenAbGroup

  if tame_wild
    tame = Dict{T, GrpAbFinGenToAbsOrdMap{S}}()
    wild = Dict{T, GrpAbFinGenToAbsOrdMap{S}}()
  end

  O = base_ring(Q)
  oneO = one(O)
  generators = Vector{elem_type(Q)}()
  moduli = _compute_products_for_make_coprime(ideals)
  for i = 1:length(groups)
    if tame_wild
      @assert length(keys(maps[i].tame)) == 1
      p = first(keys(maps[i].tame))
      wild_generators = Vector{elem_type(O)}()
    end
    for j = 1:ngens(groups[i])
      g = crt(maps[i].generators[j].elem, ideals[i], oneO, moduli[i])
      push!(generators, Q(g))
      if tame_wild
        if j == 1
          tame[p] = GrpAbFinGenToAbsOrdMap(domain(maps[i].tame[p]), O, [ g ], maps[i].tame[p].discrete_logarithm)
        else
          push!(wild_generators, g)
        end
      end
    end
    if tame_wild && haskey(maps[i].wild, p)
      wild[p] = GrpAbFinGenToAbsOrdMap(domain(maps[i].wild[p]), O, wild_generators, maps[i].wild[p].discrete_logarithm)
    end
  end

  if length(groups) == 1
    local disc_log2
    let maps = maps
      function disc_log2(x::AbsOrdQuoRingElem)
        xx = codomain(maps[1])(x.elem)
        return maps[1].discrete_logarithm(xx)
      end
    end

    m = GrpAbFinGenToAbsOrdQuoRingMultMap(G, Q, generators, disc_log2)
    if tame_wild
      m.tame = tame
      m.wild = wild
    end
    return G, m
  end

  local disc_log
  let maps = maps
    function disc_log(a::AbsOrdQuoRingElem)
      result = Vector{ZZRingElem}()
      for map in maps
        aa = codomain(map)(a.elem)
        append!(result, map.discrete_logarithm(aa))
      end
      return result
    end
  end


  m = GrpAbFinGenToAbsOrdQuoRingMultMap(G, Q, generators, disc_log)
  if tame_wild
    m.tame = tame
    m.wild = wild
  end
  return G, m
end


function _direct_product!(ideals_and_maps::Vector{Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Vector{GrpAbFinGenToNfAbsOrdMap}}}, Q::AbsSimpleNumFieldOrderQuoRing)
  @assert !isempty(ideals_and_maps)

  groups = Vector{FinGenAbGroup}()
  ideals = [x[1] for x in ideals_and_maps]
  O = base_ring(Q)
  oneO = O(1)
  generators = Vector{AbsSimpleNumFieldOrderQuoRingElem}()
  if length(ideals) != 1
    moduli = _compute_products_for_make_coprime(ideals)
  end
  for i = 1:length(ideals)
    for map in ideals_and_maps[i][2]
      push!(groups, domain(map))
      for j = 1:length(map.generators)
        if length(ideals) == 1
          push!(generators, Q(map.generators[j]))
        else
          g = crt(map.generators[j], ideals[i], oneO, moduli[i])
          push!(generators, Q(g))
          map.generators[j] = g
        end
      end
    end
  end

  @assert !isempty(groups)
  G = direct_product(groups..., task = :none)

  function disc_log(a::AbsSimpleNumFieldOrderQuoRingElem)
    result = Vector{ZZRingElem}()
    for i = 1:length(ideals)
      for map in ideals_and_maps[i][2]
        append!(result, map.discrete_logarithm(a.elem))
      end
    end
    return result
  end

  return G, GrpAbFinGenToAbsOrdQuoRingMultMap(G, Q, generators, disc_log)
end

# This function returns the same as _direct_product called with the values of
# ideals_and_maps as maps and the keys as ideals.
# However, there can be more than one map (or group) for one ideal and the
# generators of the maps are changed IN PLACE.
function _direct_product!(ideals_and_maps::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Vector{GrpAbFinGenToNfAbsOrdMap}}, Q::AbsSimpleNumFieldOrderQuoRing)
  @assert !isempty(ideals_and_maps)

  ideals = collect(keys(ideals_and_maps))

  groups = Vector{FinGenAbGroup}()
  O = base_ring(Q)
  oneO = O(1)
  generators = Vector{AbsSimpleNumFieldOrderQuoRingElem}()
  if length(ideals) != 1
    moduli = _compute_products_for_make_coprime(ideals)
  end
  for i = 1:length(ideals)
    for map in ideals_and_maps[ideals[i]]
      push!(groups, domain(map))
      for j = 1:length(map.generators)
        if length(ideals) == 1
          push!(generators, Q(map.generators[j]))
        else
          g = crt(map.generators[j], ideals[i], oneO, moduli[i])
          push!(generators, Q(g))
          map.generators[j] = g
        end
      end
    end
  end

  @assert !isempty(groups)
  G = direct_product(groups..., task = :none)

  function disc_log(a::AbsSimpleNumFieldOrderQuoRingElem)
    result = Vector{ZZRingElem}()
    for ideal in ideals
      for map in ideals_and_maps[ideal]
        append!(result, map.discrete_logarithm(a.elem))
      end
    end
    return result
  end

  return G, GrpAbFinGenToAbsOrdQuoRingMultMap(G, Q, generators, disc_log)
end
