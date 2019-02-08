################################################################################
#
#  NfOrd/ResidueRingMultGrp.jl : Multiplicative group of Residue Rings
#
################################################################################

export multiplicative_group, multiplicative_group_generators

################################################################################
#
#  High Level Interface
#
################################################################################

@doc Markdown.doc"""
***
    multiplicative_group(Q::NfOrdQuoRing) -> GrpAbFinGen, Map{GrpAbFinGen, NfOrdQuoRing}
    unit_group(Q::NfOrdQuoRing) -> GrpAbFinGen, Map{GrpAbFinGen, NfOrdQuoRing}

> Returns the unit group of $Q$ as an abstract group $A$ and
> an isomorphism map $f \colon A \to Q^\times$.
"""
function multiplicative_group(Q::NfOrdQuoRing)
  if !isdefined(Q, :multiplicative_group)
    if ismaximal_known(base_ring(Q)) && ismaximal(base_ring(Q))
      G, GtoQ = _multgrp(Q)
    else
      G, GtoQ = _multgrp_non_maximal(Q)
    end
    Q.multiplicative_group = GtoQ
  end
  mQ = Q.multiplicative_group
  return domain(mQ), mQ
end

unit_group(Q::NfOrdQuoRing) = multiplicative_group(Q)

@doc Markdown.doc"""
***
    multiplicative_group_generators(Q::NfOrdQuoRing) -> Vector{NfOrdQuoRingElem}

> Return a set of generators for $Q^\times$.
"""
function multiplicative_group_generators(Q::NfOrdQuoRing)
  return multiplicative_group(Q).generators
end

function factor(Q::FacElem{NfOrdIdl, NfOrdIdlSet})
  if !all(isprime, keys(Q.fac))
    S = factor_coprime(Q)
    fac = Dict{NfOrdIdl, Int}()
    for (p, e)=S
      lp = factor(p)
      for q = keys(lp)
        fac[q] = Int(valuation(p, q)*e)
      end
    end
  else
    fac = Dict(p=>Int(e) for (p,e) = Q.fac)
  end
  return fac
end

function FacElem(Q::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}, O::NfOrdIdlSet)
  D = Dict{NfOrdIdl, fmpz}()
  for (I, v) = Q.fac
    if isone(I.den)
      if haskey(D, I.num)
        D[I.num] += v
      else
        D[I.num] = v
      end
    else
      n,d = integral_split(I)
      if haskey(D, n)
        D[n] += v
      else
        D[n] = v
      end
      if haskey(D, d)
        D[d] -= v
      else
        D[d] = -v
      end
    end
  end
  return FacElem(D)
end


@doc Markdown.doc"""
     factor_coprime(Q::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}) -> Dict{NfOrdIdl, Int}
> A coprime factorisation of $Q$: each ideal in $Q$ is split using \code{integral_split} and then
> a coprime basis is computed.
> This does {\bf not} use any factorisation.
"""
function factor_coprime(Q::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  D = FacElem(Q, NfOrdIdlSet(order(base_ring(Q))))
  S = factor_coprime(D)
  return S
end

@doc Markdown.doc"""
     factor(Q::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}) -> Dict{NfOrdIdl, Int}
> The factorisation of $Q$, by refining a coprime factorisation.
"""
function factor(Q::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  S = factor_coprime(Q)
  fac = Dict{NfOrdIdl, Int}()
  for (p, e)=S
    lp = factor(p)
    for q = keys(lp)
      fac[q] = Int(valuation(p, q)*e)
    end
  end
  return fac
end

# Factors Q.ideal, the result is saved in Q.factor
function factor(Q::NfOrdQuoRing)
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

@doc Markdown.doc"""
***
    _multgrp(Q::NfOrdQuoRing) -> (GrpAbFinGen, GrpAbFinGenToAbsOrdQuoRingMultMap)

> Returns the group $Q^\times$ and a map from this group to $Q$.
"""
function _multgrp(Q::NfOrdQuoRing, save_tame_wild::Bool = false; method = nothing)

  fac = factor(Q)

  if isempty(fac)
    disc_log = function(x::NfOrdQuoRingElem)
      return fmpz[]
    end
    GtoQ = GrpAbFinGenToAbsOrdQuoRingMultMap(Q, elem_type(Q)[], fmpz[], disc_log)
    return domain(GtoQ), GtoQ
  end

  prime_powers = Vector{NfOrdIdl}()
  groups = Vector{GrpAbFinGen}()
  maps = Vector{GrpAbFinGenToAbsOrdQuoRingMultMap}()
  for (p, vp) in fac
    pvp = p^vp
    G, mG = _multgrp_mod_pv(p, vp, pvp; method = method)
    push!(prime_powers, pvp)
    push!(groups, G)
    push!(maps, mG)
  end

  G, GtoQ = _direct_product(groups, maps, prime_powers, Q, save_tame_wild)
  S, StoG, StoQ = snf(G, GtoQ)

  return S, StoQ
end

_multgrp_ray(Q::NfOrdQuoRing; method = nothing) = _multgrp(Q, true; method = method)

################################################################################
#
#  Compute Multiplicative Group For Prime Powers
#
################################################################################

@doc Markdown.doc"""
***
    _multgrp_mod_pv(p::NfOrdIdl, v::Int, pv::NfOrdIdl) -> (GrpAbFinGen, GrpAbFinGenToAbsOrdQuoRingMultMap)

> Given a prime ideal $p$ in a maximal order $\mathcal O$, an integer $v > 0$ and
> $pv = p^v$, the function returns the group $(\mathcal O/p^v)^\times$ and a map
> from this group to $O/p^v$.
"""
function _multgrp_mod_pv(p::NfOrdIdl, v::Int, pv::NfOrdIdl; method=nothing)
  @hassert :NfOrdQuoRing 2 isprime(p)
  @assert v >= 1
  pnumv = minimum(p, Val{false})^v # to speed up the exponentiation in the GrpAbFinGenToNfAbsOrdMaps
  G1, G1toO = _multgrp_mod_p(p, pnumv)
  Q, OtoQ = quo(order(p), pv)
  tame_part = Dict{NfAbsOrdIdl, GrpAbFinGenToNfAbsOrdMap}()
  wild_part = Dict{NfAbsOrdIdl, GrpAbFinGenToNfAbsOrdMap}()
  if v == 1
    tame_part[p] = G1toO
    function disc_log(x::NfOrdQuoRingElem)
      return G1toO.discrete_logarithm((OtoQ\x))
    end
    GtoQ = GrpAbFinGenToAbsOrdQuoRingMultMap(G1, Q, map(OtoQ, G1toO.generators), disc_log)
  else
    G2, G2toO = _1_plus_p_mod_1_plus_pv(p, v, pv, pnumv; method = method)
    wild_part[p] = G2toO

    gen1 = G1toO(G1[1])
    @assert issnf(G1) && issnf(G2)
    rel1 = G1.snf[1]
    # G2.snf[end] is the order of the biggest cyclic subgroup of G2
    gen1_obcs = powermod(gen1, G2.snf[end], pnumv)
    gens = map(OtoQ, append!([gen1_obcs], G2toO.generators))

    G1toO.generators[1] = gen1_obcs
    tame_part[p] = G1toO

    G = direct_product(G1, G2)[1]

    obcs_inv = gcdx(G2.snf[end], rel1)[2]
    function disc_log2(x::NfOrdQuoRingElem)
      y = OtoQ\x
      r = mod((G1toO.discrete_logarithm(y))[1]*obcs_inv, rel1)
      y *= gen1_obcs^mod(-r, rel1)
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
function _multgrp_mod_p(p::NfOrdIdl, pnumv::fmpz = fmpz(0))
  @hassert :NfOrdQuoRing 2 isprime(p)
  O = order(p)
  n = norm(p) - 1
  gen = _primitive_element_mod_p(p)
  factor_n = factor(n)
  Q, mQ = ResidueField(O, p)
  gen_quo = mQ(gen)
  discrete_logarithm = function (x::NfOrdElem)
    y=mQ(x)
    if y==Q(1)
      return 0
    elseif y==Q(-1) && mod(n,2)==0
      return divexact(n,2)
    end
    if n<11
      res=1
      el=gen_quo
      while el!=y
        el*=gen_quo
        res+=1
      end
      return res
    else 
      return pohlig_hellman(gen_quo,n,y;factor_n=factor_n)
    end
  end
  disc_log = function(x::NfOrdElem)
    return fmpz[ discrete_logarithm(x) ]
  end
  map = GrpAbFinGenToNfAbsOrdMap(O, [ gen ], [ n ], disc_log, pnumv)
  return domain(map), map
end

function _primitive_element_mod_p(p::NfOrdIdl)
  @hassert :NfOrdQuoRing 2 isprime(p)
  O = order(p)
  Q, Q_map = quo(O,p)
  n = norm(p) - 1
  primefactors_n = collect(keys(factor(n).fac))
  while true
    x = rand(Q)
    x == 0 && continue
    order_too_small = false
    for l in primefactors_n
      if x^div(n, l) == 1
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
function _1_plus_p_mod_1_plus_pv(p::NfOrdIdl, v::Int, pv::NfOrdIdl, pnumv::fmpz = fmpz(0); method=nothing)
  @hassert :NfOrdQuoRing 2 isprime(p)
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
  toO = GrpAbFinGenToNfAbsOrdMap(order(p), gens, rels, disc_log, pnumv)::GrpAbFinGenToAbsOrdMap{NfOrd, NfOrdElem}
  Q, OtoQ = quo(order(p), pv)
  S, mS, StoO = snf(toO, OtoQ)
  return S, StoO::GrpAbFinGenToAbsOrdMap{NfOrd, NfOrdElem}
end

################################################################################
#
#  Iterative Method for (1+p^u)/(1+p^v)
#
################################################################################

function _iterative_method(p::NfOrdIdl, v::Int; base_method=nothing, use_p_adic=true)
  return _iterative_method(p, 1, v ; base_method = base_method, use_p_adic = use_p_adic)
end

function _iterative_method(p::NfOrdIdl, u::Int, v::Int; base_method = nothing, use_p_adic = true)
  @assert v >= u >= 1
  pnum = minimum(p)
  if use_p_adic
    e = ramification_index(p)
    k0 = 1 + Int(div(fmpz(e),(pnum-1)))::Int
  end
  g = Vector{NfOrdElem}()
  M = zero_matrix(FlintZZ, 0, 0)
  dlogs = Vector{Function}()

  l = u
  pl = (p^l)::NfOrdIdl

  while l != v
    k = l
    pk = pl
    if use_p_adic && k>=k0
      l = v
      d = div(l, k)
      if l == d*k
        pl = pk^d
      else
        pl = p^l
      end
      h, N, disc_log = _p_adic_method(p, k, l; pu = pk, pv = pl)::Tuple{Vector{NfOrdElem}, fmpz_mat, Function}
    elseif base_method == :quadratic
      l = min(2*k, v)
      d = div(l, k)
      if l == d*k
        pl = pk^d
      else
        pl = p^l
      end
      h, N, disc_log = _quadratic_method(p, k, l; pu = pk, pv = pl)::Tuple{Vector{NfOrdElem}, fmpz_mat, Function}
    else
      l = Int(min(pnum*k, v))
      d = div(l, k)
      if l == d*k
        pl = pk^d
      else
        pl = p^l
      end
      h, N, disc_log = _artin_hasse_method(p, k, l; pu = pk, pv = pl)::Tuple{Vector{NfOrdElem}, fmpz_mat, Function}
    end
    
    g, M = _expand(g, M, h, N, disc_log, pl)
   
    push!(dlogs, disc_log)
  end

  Q = NfOrdQuoRing(order(pl), pl)
  function discrete_logarithm(b::NfOrdElem)
    b1 = Q(b)
    a = fmpz[]
    k1 = 1
    for i in 1:length(dlogs)
      a_ = dlogs[i](b1.elem)
      prod = Q(1)
      for j in 1:length(a_)
        mul!(prod, prod, Q(g[k1])^a_[j])
        k1 += 1
      end
      append!(a, a_)
      b1 = divexact(b1, prod)
    end
    return a
  end

  return g::Vector{NfOrdElem}, M, discrete_logarithm
end


#
# Given generators and relations for groups of two consecutives steps, this function computes 
# generators and relations for the product
#
function _expand(g::Array{NfOrdElem,1}, M::fmpz_mat, h::Array{NfOrdElem,1}, N::fmpz_mat, disc_log::Function, pl::NfOrdIdl)
  isempty(g) && return h,N
  isempty(h) && return g,M
  # I am assuming that N is a diagonal matrix
  @assert issnf(N)
  O = order(pl)
  Q , mQ = quo(O,pl)
  Z = zero_matrix(FlintZZ,nrows(M)+nrows(N),ncols(M)+ncols(N))
  for i=1:nrows(M)
    for j=1:ncols(M)
      Z[i,j]=M[i,j]
    end
  end
  for i=1:nrows(N)
    Z[i+nrows(M),i+nrows(M)]=N[i,i]
  end
  for i in 1:nrows(M)
    el = Q(1)
    for j = 1:ncols(M)
      if !iszero(M[i, j])
        mul!(el, el, Q(g[j])^M[i, j])
      end
    end
    el1 = el.elem
    alpha = disc_log(el1)
    for j in 1:ncols(N)
      Z[i,j+ncols(M)] = -alpha[j]
    end
  end
  append!(g,h)
  
  return g,Z
end


#
#  This function returns a set of generators with the corresponding relations and disclog
#

function _pu_mod_pv(pu::NfOrdIdl, pv::NfOrdIdl)

  O=order(pu)
  b=basis(pu)
  N = basis_mat(pv, Val{false})*basis_mat_inv(pu, Val{false})
  @assert denominator(N) == 1
  G = AbelianGroup(N.num)
  S, mS=snf(G)
  
  #Generators
  gens=Array{NfOrdElem,1}(undef, ngens(S))
  for i=1:ngens(S)
    x=mS(S[i])
    gens[i]=O(0)
    for j=1:ngens(G)
      add!(gens[i], gens[i], mod(x[j], S.snf[end])*b[j])
    end
  end
  
  #Disclog  
  M=basis_mat_inv(pu, Val{false})*mS.imap
  function disclog(x::NfOrdElem)
    x_fakemat = FakeFmpqMat(matrix(FlintZZ, 1, degree(O), elem_in_basis(x)), fmpz(1))
    mul!(x_fakemat, x_fakemat, M)
    denominator(x_fakemat) != 1 && error("Element is in the ideal")
    return vec(Array(x_fakemat.num))
  end
  
  return gens, rels(S), disclog
  
end

# Let p be a prime ideal above a prime number pnum. Let e = v_p(pnum) be
# its ramification index. If b > a >= e/(pnum-1) this function computes
# the structure of (1+p^a)/(1+p^b) as an abelian group.
function _1_plus_pa_mod_1_plus_pb_structure(p::NfOrdIdl,a,b)
  b > a >= 1 || return false, nothing
  @hassert :NfOrdQuoRing 2 isprime(p)
  O = order(p)
  pnum = minimum(p)
  e = ramification_index(p)
  k0 = 1 + div(fmpz(e),(pnum-1))
  a >= k0 || return false, nothing
  Q = NfOrdQuoRing(O,p^(b-a))
  return true, group_structure(Q)
end

################################################################################
#
# Quadratic Method for (1+p^u)/(1+p^v)
#
################################################################################

# Compute generators, a relation matrix and a function to compute discrete
# logarithms for (1+p^u)/(1+p^v), where 2*u >= v >= u >= 1
function _quadratic_method(p::NfOrdIdl, u::Int, v::Int; pu::NfOrdIdl=p^u, pv::NfOrdIdl=p^v)
  @hassert :NfOrdQuoRing 2 isprime(p)
  @assert 2*u >= v >= u >= 1
  g,M, dlog = _pu_mod_pv(pu,pv)
  map!(x -> x + 1, g, g)
  function discrete_logarithm(x::NfOrdElem)
    return dlog(mod(x-1,pv))
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
function _artin_hasse_method(p::NfOrdIdl, u::Int, v::Int; pu::NfOrdIdl=p^u, pv::NfOrdIdl=p^v)
  @hassert :NfOrdQuoRing 2 isprime(p)
  pnum = minimum(p)
  @assert pnum*u >= v >= u >= 1
  @assert fmpz(v) <= pnum*fmpz(u)
  Q, mQ = quo(order(p), pv)
  g, M, dlog = _pu_mod_pv(pu,pv)
  map!(x->artin_hasse_exp(Q(x),pnum), g, g)
  function discrete_logarithm(x::NfOrdElem)
    return dlog(artin_hasse_log(Q(x), pnum)) 
  end
  return g, M, discrete_logarithm
end

function artin_hasse_exp(x::NfOrdQuoRingElem, pnum::fmpz)
  Q=parent(x)
  s = Q(1)
  fac_i = Q(1)
  t = Q(1)
  for i=1:pnum-1
    mul!(t, t, x)
    if iszero(t)
      break
    end
    mul!(fac_i, fac_i, Q(i))
    add!(s, s, divexact(t, fac_i))
  end
  return s.elem
end

function artin_hasse_log(y::NfOrdQuoRingElem, pnum::fmpz)
  Q = parent(y)
  x = y - Q(1)
  if iszero(x)
    return x.elem
  end
  s = Q(0)
  t = Q(1)
  for i in 1:pnum-1
    mul!(t, t, x)
    if iszero(t)
      break
    end
    if iseven(i)
      sub!(s, s, divexact(t, Q(i)))
    else 
      add!(s, s, divexact(t, Q(i)))
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
function _p_adic_method(p::NfOrdIdl, v::Int; pv=p^v)
  return _p_adic_method(p,1,v)
end

# Compute generators, a relation matrix and a function to compute discrete
# logarithms for (1+p^u)/(1+p^v) if u >= k0, where p is a prime ideal over pnum,
# e the p-adic valuation of pnum, and k0 = 1 + div(e,pnum-1)
function _p_adic_method(p::NfOrdIdl, u::Int, v::Int; pu::NfOrdIdl=p^u, pv::NfOrdIdl=p^v)
  @assert v > u >= 1
  e = ramification_index(p) #ramification index
  k0 = 1 + div(fmpz(e),(minimum(p)-1))
  @assert u >= k0
  g, M, dlog = _pu_mod_pv(pu, pv)
  O = order(p)
  Q = NfOrdQuoRing(O, pv)
  map!(x -> p_adic_exp(Q, p, v, x), g, g)
  function discrete_logarithm(b::NfOrdElem) 
    return dlog(p_adic_log(Q, p, v, b))
  end
  
  return g, M, discrete_logarithm
end


function p_adic_exp(Q::NfOrdQuoRing, p::NfOrdIdl, v::Int, x::NfOrdElem)
  O = parent(x)
  iszero(x) && return O(1)
  pnum = p.minimum
  e = ramification_index(p)
  val_p_x = valuation(x, p)
  max_i = floor(Int, v / (val_p_x - (e/(Float64(pnum)-1)))) + 1
  val_p_maximum = Int(max_i*val_p_x) + 1
  Q_ = NfOrdQuoRing(O, p^val_p_maximum)
  x = Q_(x)
  s = one(Q)
  inc = Q_(1)
  val_p_xi = 0
  val_p_fac_i = 0
  i_old = 0
  for i in 1:max_i
    val_pnum_i = valuation(fmpz(i), pnum)
    val_p_i = val_pnum_i * e
    val_p_fac_i += val_p_i
    val_p_xi += val_p_x
    val_p_xi - val_p_fac_i >= v && continue
    @hassert :NfOrdQuoRing 1 val_p_xi - val_p_fac_i>=0
    @hassert :NfOrdQuoRing 1 val_p_xi< val_p_maximum
    @hassert :NfOrdQuoRing 1 val_p_fac_i< val_p_maximum
    i_prod = prod((i_old+1):i)
    deltax = inc*x^(i-i_old)
    @hassert :NfOrdQuoRing 1 !iszero(deltax)
    @hassert :NfOrdQuoRing 1 !iszero(Q_(i_prod))
    inc = divexact(deltax,Q_(i_prod))
    add!(s, s, Q(inc.elem))
    i_old = i
  end
  return s.elem
end

function p_adic_log(Q::NfOrdQuoRing, p::NfOrdIdl, v::Int, y::NfOrdElem)
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
  leftlim = bound1 + pnum - mod(fmpz(bound1), pnum)
  for i in 1:bound1
    val_pnum_i = valuation(i, pnum)
    val_p_i = val_pnum_i * e
    val_p_xi += val_p_x
    val_p_xi - val_p_i >= v && continue
    mul!(xi, xi, x^(i-i_old))
    el = anti_uni^val_p_i
    numer = O(xi.elem_in_nf*el, false)
    denom = O(i*el, false)
    inc = divexact(Q(numer),Q(denom))
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
    el = anti_uni^val_p_i
    numer = O(xi.elem_in_nf*el, false)
    denom = O(i*el, false)
    inc = divexact(Q(numer),Q(denom))
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

function root(a::T, n::Int) where T <: Integer
  return T(root(fmpz(a), n))
end  

@doc Markdown.doc"""
***
    baby_step_giant_step(g, n, h) -> fmpz
    baby_step_giant_step(g, n, h, cache::Dict) -> fmpz

> Computes the discrete logarithm $x$ such that $h = g^x$.

> $g$ is a generator of order less than or equal to $n$
> and $h$ has to be generated by $g$.
> If a dictionary `cache` is supplied, it will be used to store the result
> of the first step. This allows to speed up subsequent calls with
> the same $g$ and $n$.
"""
function baby_step_giant_step(g, n, h, cache::Dict)
  @assert typeof(g) == typeof(h)
  n = BigInt(n)
  m = root(n, 2)+1
  if isempty(cache)
    it = g^0
    for j in 0:m
      cache[it] = j
      it *= g
    end
  end
  if typeof(g) == fq_nmod || typeof(g) == fq
    b = g^(-fmpz(m))
  else
    b = g^(-m)
  end
  y = h
  for i in 0:m-1
    if haskey(cache, y)
      return fmpz(mod(i*m + cache[y], n))
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

@doc Markdown.doc"""
***
    pohlig_hellman(g, n, h; factor_n=factor(n)) -> fmpz

> Computes the discrete logarithm $x$ such that $h = g^x$.

> $g$ is a generator of order $n$ and $h$ has to be generated by $g$.
> The factorisation of $n$ can be supplied via `factor_n` if
> it is already known.
"""
function pohlig_hellman(g, n, h; factor_n=factor(n))
  @assert typeof(g) == typeof(h)
  n == 1 && return fmpz(0)
  results = Vector{fmpz}()
  prime_powers = Vector{fmpz}()
  for (p,v) in factor_n
    pv = p^v
    r = div(n,pv)
    c = _pohlig_hellman_prime_power(g^r,p,v,h^r)
    push!(results, fmpz(c))
    push!(prime_powers, fmpz(pv))
  end
  if length(results) == 1
    return results[1]
  end
  return crt(results, prime_powers)
end

function _pohlig_hellman_prime_power(g,p,v,h)
  cache = Dict{typeof(g), BigInt}()
  p_i = 1
  p_v_min_i_min_1 = p^(v-1)
  g_ = g^(p^(v-1))
  a = baby_step_giant_step(g_,p,h^(p^(v-1)),cache)
  h *= g^-a
  for i in 1:v-1
    p_i *= p
    p_v_min_i_min_1 = div(p_v_min_i_min_1,p)
    ai = baby_step_giant_step(g_,p,h^p_v_min_i_min_1,cache)
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

function _prime_part_multgrp_mod_p(p::NfOrdIdl, prime::Int)
  @hassert :NfOrdQuoRing 2 isprime(p)
  O = order(p)
  Q, mQ = ResidueField(O,p)
  
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
  inv=gcdx(m,fmpz(powerp))[2]
  
  function disclog(x::NfOrdElem)
    t=mQ(x)^m
    if powerp<10
      w=1
      el=g
      while el!=t
        w+=1
        el*=g
      end
      return fmpz[w*inv]
    else
      return fmpz[_pohlig_hellman_prime_power(g,prime,s,t)*inv]
    end
  end

  map = GrpAbFinGenToNfAbsOrdMap(O, [ mQ\g ], [ fmpz(powerp) ], disclog)
  return domain(map), map
end


function _mult_grp(Q::NfOrdQuoRing, p::Integer)
  O = Q.base_ring
  OtoQ = NfOrdQuoMap(O, Q)

  tame_part = Dict{NfOrdIdl, GrpAbFinGenToNfAbsOrdMap}()
  wild_part = Dict{NfOrdIdl, GrpAbFinGenToNfAbsOrdMap}()

  fac = factor(Q)
  y1 = Dict{NfOrdIdl, Int}()
  y2 = Dict{NfOrdIdl, Int}()
  for (q, e) in fac
    if divisible(norm(q) - 1, p)
      y1[q] = Int(1)
    else
      if divisible(norm(q), p) && e >= 2
        y2[q] = Int(e)
      end
    end
  end

  if isempty(y1) && isempty(y2)
    G = DiagonalGroup(fmpz[])
    disc_log = function(x::NfOrdQuoRingElem)
      return fmpz[]
    end
    return G, GrpAbFinGenToAbsOrdQuoRingMultMap(G, Q, elem_type(Q)[], disc_log), y1
  end

  ideals_and_maps = Dict{NfOrdIdl, Vector{GrpAbFinGenToNfAbsOrdMap}}()
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

      @assert issnf(G2)
      obcs = G2.snf[end] # order of the biggest cyclic subgroup
      obcs_inv = gcdx(nq, obcs)[2]

      disc_log2 = function(x::NfOrdElem)
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

function _find_gen(Q::FqFiniteField, powm::Vector{fmpz}, m::fmpz)
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


function _n_part_multgrp_mod_p(p::NfOrdIdl, n::Int)
  @hassert :NfOrdQuoRing 2 isprime(p)
  O = order(p)
  Q, mQ = ResidueField(O, p)

  np = norm(p) - fmpz(1)
  @assert !isone(gcd(fmpz(n), np))
  npart, m = ppio(np, fmpz(n))
  k = gcd(npart, fmpz(n))::fmpz
  fac = factor(k)::Fac{fmpz}
  powm = fmpz[divexact(npart, x) for x in keys(fac.fac)]
  
  #
  #  We search for a random element with the right order
  #
  g = _find_gen(Q, powm, m)
  inv = gcdx(m, npart)[2]
  quot = divexact(npart, k)

  w=g^quot
  function disclog(x::NfOrdElem)
    t = mQ(x)^(m*quot)
    if iszero(t)
      error("Not coprime!")
    end
    if isone(t)
      return fmpz[fmpz(0)]
    end
    if k < 20
      s = 1
      el = deepcopy(w)
      while el != t
        s += 1
        mul!(el, el, w)
      end
      return fmpz[mod(fmpz(s)*inv, k)]
    else 
      return fmpz[pohlig_hellman(g^quot, k, t)*inv] 
    end
  end
  G = DiagonalGroup([k])
  gens = Vector{NfOrdElem}(undef, 1)
  gens[1] = preimage(mQ, g)
  map = GrpAbFinGenToNfAbsOrdMap(G, O, gens, disclog)::GrpAbFinGenToAbsOrdMap{NfOrd, NfOrdElem}
  return G, map
end

function _mult_grp_mod_n(Q::NfOrdQuoRing, y1::Dict{NfOrdIdl, Int}, y2::Dict{NfOrdIdl, Int}, n::Integer)
  O = Q.base_ring
  OtoQ = NfOrdQuoMap(O, Q)
  fac = factor(Q)

  tame_part = Dict{NfOrdIdl, GrpAbFinGenToNfAbsOrdMap}()
  wild_part = Dict{NfOrdIdl, GrpAbFinGenToNfAbsOrdMap}()

  if isempty(y1) && isempty(y2)
    G = DiagonalGroup(fmpz[])
    disc_log = function(x::NfOrdQuoRingElem)
      return fmpz[]
    end
    return G, GrpAbFinGenToAbsOrdQuoRingMultMap(G, Q, elem_type(Q)[], disc_log), tame_part, wild_part
  end

  ideals_and_maps = Tuple{NfOrdIdl, Vector{GrpAbFinGenToNfAbsOrdMap}}[]
  tame_ind = Tuple{NfOrdIdl, Int}[]
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
      G2, G2toO = _1_plus_p_mod_1_plus_pv(q, y2[q], qe)
      if haskey(y1, q)
        e = Int(exponent(G2))
        com, uncom = ppio(n, e)
        while !isone(mod(e, uncom))
          e *= e
        end
        tame_part[q].generators[1] = tame_part[q].generators[1]^e
      end
      
      i += ngens(G2)
      nq = norm(q) - 1

      @assert issnf(G2)
      obcs = G2.snf[end] # order of the biggest cyclic subgroup
      obcs_inv = gcdx(nq, obcs)[2]

      disc_log2 = function(x::NfOrdElem)
        y = Q(x)^nq
        z = G2toO.discrete_logarithm(y.elem)
        for i = 1:length(z)
          z[i] *= obcs_inv
        end
        return z
      end

      G2toO2 = GrpAbFinGenToNfAbsOrdMap(G2, O, G2toO.generators, disc_log2)::GrpAbFinGenToAbsOrdMap{NfOrd, NfOrdElem}
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
  
  return S, StoQ, tame_part, wild_part
end

################################################################################
#
#  Functions for the non-maximal case
#
################################################################################

# Computes generators and relations for (O_P/AO_P)^\times, where Pm = P^m, Q = O/A.
function _multgrp_Op_aOp(Q::NfOrdQuoRing, P::NfOrdIdl, m::Int, Pm::NfOrdIdl)
  A = ideal(Q)
  O = order(A)

  # Compute generators for (1 + (A + P^m))/(1 + P^m)
  I = A + Pm
  I2 = I^2
  S = Set{NfOrdElem}()
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

function _multgrp_non_maximal(Q::NfOrdQuoRing)
  A = ideal(Q)
  O = order(A)

  # Determine the prime ideals containing A
  OO = maximal_order(nf(O))
  aOO = extend(A, OO)
  fac = factor(aOO)
  S = Set{NfOrdIdl}()
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
    x = valuation(det(basis_mat(A, Val{false})), p)
    y = valuation(det(basis_mat(P, Val{false})), p)
    m[i] = Int(ceil(x/y))
  end

  # Compute the groups (O_P/AO_P)^\times
  Pm = [ prime_ideals[i]^m[i] for i in 1:length(prime_ideals)]
  groups = Vector{GrpAbFinGen}(undef, length(prime_ideals))
  maps = Vector{GrpAbFinGenToAbsOrdQuoRingMultMap}(undef, length(prime_ideals))
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

# Returns the SNF S of G and a map from S to G and one from S to codomain(GtoR).
# If RtoQ is given, then the generators of S are computed modulo codomain(RtoQ).
# It is assumed, that codomain(GtoR) == domain(RtoQ) in this case.
function snf(G::GrpAbFinGen, GtoR::Union{GrpAbFinGenToAbsOrdQuoRingMultMap, GrpAbFinGenToAbsOrdMap}, modulo_map::AbsOrdQuoMap...)
  S, StoG = snf(G)

  R = codomain(GtoR)

  if ngens(G) == 0
    StoR = typeof(GtoR)(S, R, GtoR.generators, GtoR.discrete_logarithm)
    return S, StoG, StoR
  end

  function disclog(x)
    @assert parent(x) == R
    y = GtoR.discrete_logarithm(x)
    a = StoG\(G(y))
    return fmpz[ a[j] for j = 1:ngens(S) ]
  end

  modulo = (length(modulo_map) == 1)
  if modulo
    RtoQ = modulo_map[1]
    @assert domain(RtoQ) == codomain(GtoR)
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
function direct_product(G::GrpAbFinGen, GtoQ::GrpAbFinGenToAbsOrdQuoRingMultMap, H::GrpAbFinGen, HtoQ::GrpAbFinGenToAbsOrdQuoRingMultMap)
  return direct_product([G, H], [GtoQ, GtoH])
end

# Let G_i be the groups and Q_i be the codomains of the maps such that
# Q_i = O/I_i for ideals I_i.
# This function returns the direct product of the G_i, a map from the
# product to O/(\prod_i I_i) and a map from O to this quotient.
# It is assumed that the ideals I_i are coprime.
function direct_product(groups::Vector{GrpAbFinGen}, maps::Vector{GrpAbFinGenToAbsOrdQuoRingMultMap})
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
function direct_product(groups::Vector{GrpAbFinGen}, maps::Vector{GrpAbFinGenToAbsOrdQuoRingMultMap}, Q::AbsOrdQuoRing)
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
function _direct_product(groups::Vector{GrpAbFinGen}, maps::Vector{U}, ideals::Vector{T}, Q::AbsOrdQuoRing{S, T}, tame_wild::Bool = false) where {S, T, U <: GrpAbFinGenToAbsOrdQuoRingMultMap}
  @assert length(groups) == length(maps)
  @assert length(groups) != 0
  @assert length(ideals) >= length(groups)

  if length(groups) == 1 && length(ideals) == 1
    if codomain(maps[1]) == Q
      return groups[1], maps[1]
    end

    gens = map(Q, [ g.elem for g in maps[1].generators ])

    function disc_log1(x::AbsOrdQuoRingElem)
      xx = codomain(maps[1])(x.elem)
      return maps[1].discrete_logarithm(xx)
    end

    m = GrpAbFinGenToAbsOrdQuoRingMultMap(groups[1], Q, gens, disc_log1)
    if tame_wild
      m.tame = maps[1].tame
      m.wild = maps[1].wild
    end
    return groups[1], m
  end

  G = groups[1]
  for i = 2:length(groups)
    G = direct_product(G, groups[i])[1]
  end

  if tame_wild
    tame = Dict{T, GrpAbFinGenToAbsOrdMap{S}}()
    wild = Dict{T, GrpAbFinGenToAbsOrdMap{S}}()
  end

  O = base_ring(Q)
  oneO = one(O)
  generators = Vector{elem_type(Q)}()
  t = [ oneO for i = 1:length(ideals) ]
  for i = 1:length(groups)
    if tame_wild
      @assert length(keys(maps[i].tame)) == 1
      p = first(keys(maps[i].tame))
      wild_generators = Vector{elem_type(O)}()
    end
    for j = 1:ngens(groups[i])
      t[i] = maps[i].generators[j].elem
      g = crt(t, ideals)
      push!(generators, Q(g))
      if tame_wild
        if j == 1
          tame[p] = GrpAbFinGenToAbsOrdMap(domain(maps[i].tame[p]), O, [ g ], maps[i].tame[p].discrete_logarithm)
        else
          push!(wild_generators, g)
        end
      end
      t[i] = oneO
    end
    if tame_wild && haskey(maps[i].wild, p)
      wild[p] = GrpAbFinGenToAbsOrdMap(domain(maps[i].wild[p]), O, wild_generators, maps[i].wild[p].discrete_logarithm)
    end
  end

  if length(groups) == 1
    function disc_log2(x::AbsOrdQuoRingElem)
      xx = codomain(map[1])(x.elem)
      return maps[1].discrete_logarithm(xx)
    end

    m = GrpAbFinGenToAbsOrdQuoRingMultMap(G, Q, generators, disc_log2)
    if tame_wild
      m.tame = tame
      m.wild = wild
    end
    return G, m
  end

  function disc_log(a::AbsOrdQuoRingElem)
    result = Vector{fmpz}()
    for map in maps
      aa = codomain(map)(a.elem)
      append!(result, map.discrete_logarithm(aa))
    end
    return result
  end

  m = GrpAbFinGenToAbsOrdQuoRingMultMap(G, Q, generators, disc_log)
  if tame_wild
    m.tame = tame
    m.wild = wild
  end
  return G, m
end


function _direct_product!(ideals_and_maps::Vector{Tuple{NfOrdIdl, Vector{GrpAbFinGenToNfAbsOrdMap}}}, Q::NfOrdQuoRing)
  @assert !isempty(ideals_and_maps)

  groups = Vector{GrpAbFinGen}()
  ideals = [x[1] for x in ideals_and_maps]
  O = base_ring(Q)
  oneO = O(1)
  generators = Vector{NfOrdQuoRingElem}()
  t = [ oneO for i = 1:length(ideals) ]
  for i = 1:length(ideals)
    for map in ideals_and_maps[i][2]

      push!(groups, domain(map))
      for j = 1:length(map.generators)
        t[i] = map.generators[j]
        g = crt(t, ideals)
        push!(generators, Q(g))
        map.generators[j] = g
        t[i] = oneO
      end
    end
  end

  @assert !isempty(groups)
  G = groups[1]
  for i = 2:length(groups)
    G = direct_product(G, groups[i])[1]
  end

  function disc_log(a::NfOrdQuoRingElem)
    result = Vector{fmpz}()
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
function _direct_product!(ideals_and_maps::Dict{NfOrdIdl, Vector{GrpAbFinGenToNfAbsOrdMap}}, Q::NfOrdQuoRing)
  @assert !isempty(ideals_and_maps)

  ideals = collect(keys(ideals_and_maps))

  groups = Vector{GrpAbFinGen}()
  O = base_ring(Q)
  oneO = O(1)
  generators = Vector{NfOrdQuoRingElem}()
  t = [ oneO for i = 1:length(ideals) ]
  for i = 1:length(ideals)
    for map in ideals_and_maps[ideals[i]]

      push!(groups, domain(map))

      for j = 1:length(map.generators)
        t[i] = map.generators[j]
        g = crt(t, ideals)
        push!(generators, Q(g))
        map.generators[j] = g
        t[i] = oneO
      end
    end
  end

  @assert !isempty(groups)
  G = groups[1]
  for i = 2:length(groups)
    G = direct_product(G, groups[i])[1]
  end

  function disc_log(a::NfOrdQuoRingElem)
    result = Vector{fmpz}()
    for ideal in ideals
      for map in ideals_and_maps[ideal]
        append!(result, map.discrete_logarithm(a.elem))
      end
    end
    return result
  end

  return G, GrpAbFinGenToAbsOrdQuoRingMultMap(G, Q, generators, disc_log)
end
