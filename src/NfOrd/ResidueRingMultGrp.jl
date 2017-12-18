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

doc"""
***
    multiplicative_group(Q::NfOrdQuoRing) -> GrpAbFinGen, Map{GrpAbFinGen, NfOrdQuoRing}
    unit_group(Q::NfOrdQuoRing) -> GrpAbFinGen, Map{GrpAbFinGen, NfOrdQuoRing}

> Returns the unit group of $Q$ as an abstract group $A$ and
> an isomorphism map $f \colon A \to Q^\times$.
"""
function multiplicative_group(Q::NfOrdQuoRing)
  if !isdefined(Q, :multiplicative_group)
    gens , structure , disc_log = _multgrp(Q)
    Q.multiplicative_group = AbToResRingMultGrp(Q,gens,structure,disc_log)
  end
  mQ = Q.multiplicative_group
  return domain(mQ), mQ
end

unit_group(Q::NfOrdQuoRing) = multiplicative_group(Q)

doc"""
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

doc"""
     factor_coprime(Q::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}) -> Dict{NfOrdIdl, Int}
> A coprime factorisation of $Q$: each ideal in $Q$ is split using \code{integral_split} and then
> a coprime basis is computed.
> This does {\bf not} use any factorisation.
"""
function factor_coprime(Q::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
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
  S = factor_coprime(FacElem(D))
  return S
end

doc"""
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


################################################################################
#
#  Internals
#
################################################################################

doc"""
***
    _multgrp(Q::NfOrdQuoRing) -> (Vector{NfOrdQuoRingElem}, Vector{fmpz}, Function)

> Return generators, the snf structure and a discrete logarithm function for $Q^\times$.
"""
function _multgrp(Q::NfOrdQuoRing; method=nothing)

  gens = Vector{NfOrdQuoRingElem}()
  structt = Vector{fmpz}()
  disc_logs = Vector{Function}()
  i = ideal(Q)
  O=order(i)
  fac = factor(i)
  Q.factor = fac
  
  prime_power=Dict{NfOrdIdl, NfOrdIdl}()
  for (p,vp) in fac
    prime_power[p]= p^vp
  end
  
  
  for (p,vp) in fac
    gens_p , struct_p , dlog_p = _multgrp_mod_pv(p,vp;method=method)

    # Make generators coprime to other primes
    if length(fac) > 1
      i_without_p = ideal(O,1)
      for (p2,vp2) in fac
        (p != p2) && (i_without_p *= prime_power[p2])
      end

      alpha, beta = idempotents(prime_power[p],i_without_p)
      for i in 1:length(gens_p)
        g_pi_new = beta*gens_p[i] + alpha
        @hassert :NfOrdQuoRing 2 (g_pi_new - gens_p[i] in prime_power[p])
        @hassert :NfOrdQuoRing 2 (g_pi_new - 1 in i_without_p)
        gens_p[i] = g_pi_new
      end
    end

    gens_p = map(Q,gens_p)
    append!(gens,gens_p)
    append!(structt,struct_p)
    push!(disc_logs,dlog_p)
  end


  discrete_logarithm = function(x::NfOrdQuoRingElem)
    result = Vector{fmpz}()
    for dlog in disc_logs
      append!(result,dlog(x.elem))
    end
    return result
  end

  # Transform to SNF
  rels = matrix(diagm(structt))
  gens_trans, rels_trans, dlog_trans = snf_gens_rels_log(gens,rels,discrete_logarithm)
  return gens_trans, rels_trans, dlog_trans
end

################################################################################
#
#  Compute Multiplicative Group For Prime Powers
#
################################################################################

doc"""
***
    _multgrp_mod_pv(p::NfOrdIdl, v) -> (Vector{NfOrdElem}, Vector{fmpz}, Function)

> Given a prime ideal $p$ in a maximal order $\mathcal O$ and an integer $v > 0$, return generators,
> the group structure and a discrete logarithm function for $(\mathcal O/p^v)^\times$.
"""
function _multgrp_mod_pv(p::NfOrdIdl, v; method=nothing)
  @hassert :NfOrdQuoRing 2 isprime(p)
  @assert v >= 1
  gen_p, n_p, dlog_p = _multgrp_mod_p(p)
  if v == 1
    gens = [gen_p]
    structt = [n_p]
    discrete_logarithm = function(x::NfOrdElem) return [dlog_p(x)] end
  else
    gens_pv, struct_pv , dlog_pv = _1_plus_p_mod_1_plus_pv(p,v;method=method)
    obcs = prod(Set(struct_pv)) # order of biggest cyclic subgroup
    g_p_obcs = powermod(gen_p,obcs,p.gen_one^v)
    gens = [[g_p_obcs] ; gens_pv]

    structt = [[n_p] ; struct_pv]

    obcs_inv = gcdx(obcs,n_p)[2]
    discrete_logarithm = function(x::NfOrdElem)
      r = mod(dlog_p(x)*obcs_inv,n_p)
      x *= g_p_obcs^mod(-r,n_p)
      return [[r] ; dlog_pv(x)]
    end
  end
  return gens, structt, discrete_logarithm
end

################################################################################
#
#  Compute Multiplicative Group For Primes
#
################################################################################

# Compute (O_K/p)*
function _multgrp_mod_p(p::NfOrdIdl)
  @hassert :NfOrdQuoRing 2 isprime(p)
  O = order(p)
  n = norm(p) - 1
  gen = _primitive_element_mod_p(p)
  factor_n = factor(n)
  # TODO:
  # Compute the discrete logarithm in a finite field F with O/p \cong F.
  # Although P is always a prime, but not all of them work at the moment.
  # Make this work for all of them!
  if has_2_elem(p) && isprime_known(p)
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
  else
    Q = NfOrdQuoRing(O,p)
    gen_quo = Q(gen)
    discrete_logarithm= function (x::NfOrdElem)
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
  end
  return gen, n, discrete_logarithm
end

function _primitive_element_mod_p(p::NfOrdIdl)
  @hassert :NfOrdQuoRing 2 isprime(p)
  O = order(p)
  Q , Q_map = quo(O,p)
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
function _1_plus_p_mod_1_plus_pv(p::NfOrdIdl, v::Int; method=nothing)
  @hassert :NfOrdQuoRing 2 isprime(p)
  @assert v >= 1
  if method == :one_unit
    gens = nothing
    rels = nothing
    disc_log = nothing
    try
      gens, structt , disc_log = _one_unit_method(p,v)
      rels = matrix(diagm(structt))
    catch
      warn("Skipped p = <$(p.gen_one),$(p.gen_two)>, v = $(v)")
      gens, rels, disc_log = _iterative_method(p,v)
    end
  elseif method == :quadratic
    gens, rels, disc_log = _iterative_method(p,v;base_method=:quadratic,use_p_adic=false)
  elseif method == :artin_hasse
    gens, rels, disc_log = _iterative_method(p,v;base_method=:artin_hasse,use_p_adic=false)
  elseif method == :p_adic
    gens, rels, disc_log = _iterative_method(p,v;use_p_adic=true)
  else
    gens, rels, disc_log = _iterative_method(p,v)
  end

  @assert size(rels) == (length(gens),length(gens))
  gens_snf , struct_snf , disc_log_snf = snf_gens_rels_log(gens, rels, disc_log, p^v)
  return gens_snf, struct_snf, disc_log_snf
end

################################################################################
#
#  Iterative Method for (1+p^u)/(1+p^v)
#
################################################################################

function _iterative_method(p::NfOrdIdl, v; base_method=nothing, use_p_adic=true)
  return _iterative_method(p,1,v;base_method=base_method,use_p_adic=use_p_adic)
end

function _iterative_method(p::NfOrdIdl, u::Int, v::Int; base_method=nothing, use_p_adic=true)
  @hassert :NfOrdQuoRing 2 isprime(p)
  @assert v >= u >= 1
  pnum = minimum(p)
  if use_p_adic
    e = valuation(pnum,p)
    k0 = 1 + div(fmpz(e),(pnum-1))
  end
  g = Vector{NfOrdElem}()
  M = zero_matrix(FlintZZ,0,0)
  dlogs = Vector{Function}()

  l = u
  pl = p^l

  while l != v
    k = l
    pk = pl

    if use_p_adic && k>=k0
      next_method = _p_adic_method
      l = v
    elseif base_method == :quadratic
      next_method = _quadratic_method
      l = min(2*k,v)
    elseif base_method == :_one_unit
      next_method = _one_unit_method
      if use_p_adic
        l = min(k0,v)
      else
        l = v
      end
    else
      next_method = _artin_hasse_method
      l = min(pnum*k,v)
    end

    d = Int(div(fmpz(l),k))
    pl = l == d*k ? pk^d : p^l
    h, N, disc_log = next_method(p,k,l;pu=pk,pv=pl)
    
    g,M = _expand(g,M,h,N,disc_log,pl)
    
    
    push!(dlogs,disc_log)
  end

  Q = NfOrdQuoRing(order(pl),pl)
  function discrete_logarithm(b::NfOrdElem)
    b = Q(b)
    a = fmpz[]
    k = 1
    for i in 1:length(dlogs)
      a_ = dlogs[i](b.elem)
      prod = Q(1)
      for j in 1:length(a_)
        prod *= Q(g[k])^a_[j]
        k += 1
      end
      a = fmpz[a ; a_]
      b = divexact(b,prod)
    end
    return a
  end

  return g, M, discrete_logarithm
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
  Z = zero_matrix(FlintZZ,rows(M)+rows(N),cols(M)+cols(N))
  for i=1:rows(M)
    for j=1:cols(M)
      Z[i,j]=M[i,j]
    end
  end
  for i=1:rows(N)
    Z[i+rows(M),i+rows(M)]=N[i,i]
  end

  for i in 1:rows(M)
    el = prod([Q(g[j])^M[i,j] for j=1:cols(M) ]).elem
    alpha = disc_log(el)
    for j in 1:cols(N)
      Z[i,j+cols(M)] = -alpha[j]
    end
  end

  append!(g,h)
  
  return g,Z
end


#
#  This function returns a set of generators with the corresponding relations and disclog
#

function _pu_mod_pv(pu::NfOrdIdl,pv::NfOrdIdl)

  O=order(pu)
  b=basis(pu)
  N = basis_mat(pv)*basis_mat_inv(pu)
  @hassert :NfOrdQuoRing 1 denominator(N) == 1
  G=AbelianGroup(numerator(N))
  S,mS=snf(G)
  
  #Generators
  gens=Array{NfOrdElem,1}(ngens(S))
  for i=1:ngens(S)
    x=mS(S[i])
    gens[i]=O(0)
    for j=1:ngens(G)
      gens[i]+=mod(x[j], S.snf[end])*b[j]
    end
  end
  
  #Disclog  
  M=basis_mat_inv(pu)*mS.imap
  function disclog(x::NfOrdElem)
    x_fakemat = FakeFmpqMat(matrix(FlintZZ, 1, degree(parent(x)), elem_in_basis(x)), fmpz(1))
    res_fakemat = x_fakemat * M
    denominator(res_fakemat) != 1 && error("Element is in the ideal")
    return vec(Array(numerator(res_fakemat)))
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
  e = valuation(O(pnum),p)
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
function _quadratic_method(p::NfOrdIdl, u, v; pu::NfOrdIdl=p^u, pv::NfOrdIdl=p^v)
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
function _artin_hasse_method(p::NfOrdIdl, u, v; pu::NfOrdIdl=p^u, pv::NfOrdIdl=p^v)
  @hassert :NfOrdQuoRing 2 isprime(p)
  
  pnum = minimum(p)
  @assert pnum*u >= v >= u >= 1
  Q, mQ=quo(order(p), pv)
  g,M, dlog = _pu_mod_pv(pu,pv)
  map!(x->artin_hasse_exp(Q(x),pnum), g, g)
  
  function discrete_logarithm(x::NfOrdElem)
    return dlog(artin_hasse_log(Q(x), pnum)) 
  end
  return g, M, discrete_logarithm
end

function artin_hasse_exp(x::NfOrdQuoRingElem, pnum::fmpz)
  Q = parent(x)
  s = Q(1)
  fac_i = 1
  t=Q(1)
  for i in 1:pnum-1
    t*=x
    fac_i *= Q(i)
    s += divexact(t,fac_i)
  end
  return s.elem
end

function artin_hasse_log(y::NfOrdQuoRingElem, pnum::fmpz)
  Q = parent(y)
  x = y-1
  s = Q(0)
  t= Q(1)
  for i in 1:pnum-1
    t *=x
    if i % 2 == 0
      s -= divexact(t,Q(i))
    else 
      s += divexact(t,Q(i))
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
function _p_adic_method(p::NfOrdIdl, u, v; pu::NfOrdIdl=p^u, pv::NfOrdIdl=p^v)
  @assert v > u >= 1
  @hassert :NfOrdQuoRing 2 isprime(p)
  pnum = minimum(p)
  e = valuation(pnum,p) #ramification index
  k0 = 1 + div(fmpz(e),(pnum-1))
  @assert u >= k0
  g,M, dlog = _pu_mod_pv(pu,pv)
  Q = NfOrdQuoRing(order(p),pv)
  map!(x->p_adic_exp(Q,p,v,x,e;pv=pv), g, g)
 
  function discrete_logarithm(b::NfOrdElem) 
    return dlog(p_adic_log(Q,p,v,b,e;pv=pv))
  end
  
  return g, M, discrete_logarithm
end

function p_adic_exp(Q::NfOrdQuoRing, p::NfOrdIdl, v, x::NfOrdElem, e::Int; pv::NfOrdIdl=p^v)
  O = parent(x)
  x == 0 && return O(1)
  pnum = minimum(p)
  val_p_x = valuation(x,p)
  max_i = ceil(Int, v / (val_p_x - (e/(Float64(pnum)-1)))) 
  val_p_maximum = Int(max_i*val_p_x) + 1
  Q_ = NfOrdQuoRing(O,p^val_p_maximum)
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
    i_prod = prod((i_old+1):i)
    inc = divexact(inc*x^(i-i_old),i_prod)
    s += Q(inc.elem)
    i_old = i
  end
  return s.elem
end

function p_adic_log(Q::NfOrdQuoRing, p::NfOrdIdl, v, y::NfOrdElem, e::Int; pv::NfOrdIdl=p^v)
  O = parent(y)
  y == 1 && return O(0)
  pnum = Int(minimum(p))
  x = y - 1
  val_p_x = valuation(x, p)
  s = zero(Q)
  xi = one(O)
  i_old = 0
  val_p_xi = 0
  for i in [ 1:v ; (v+pnum-(v%pnum)):pnum:pnum*v ]
    val_pnum_i = valuation(i, pnum)
    val_p_i = val_pnum_i * e
    val_p_xi += val_p_x
    val_p_xi - val_p_i >= v && continue
    xi *= x^(i-i_old)
    fraction = divexact(xi.elem_in_nf,i)
    inc = divexact(Q(O(numerator(fraction))),Q(O(denominator(fraction))))
    isodd(i) ? s+=inc : s-=inc
    i_old = i
  end
  return s.elem
end



################################################################################
#
#  SNF For Multiplicative Groups
#
################################################################################

doc"""
***
    snf_gens_rels_log(gens::Vector,
                      rels::fmpz_mat,
                      dlog::Function) -> (Vector, fmpz_mat, Function)
    snf_gens_rels_log(gens::Vector{NfOrdElem},
                      rels::fmpz_mat,
                      dlog::Function,
                      i::NfOrdIdl) -> (Vector{NfOrdElem}, fmpz_mat, Function)

> Return the smith normal form of a mulitplicative group.

> The group is represented by generators, a relation matrix
> and a function to compute the discrete logarithm with respect to the generators.
> All trivial components of the group will be removed.
> If the generators are of type `NfOrdElem` and an ideal `i` is supplied,
> all transformations of the generators will be computed modulo `i`.
"""
function snf_gens_rels_log(gens::Vector, rels::fmpz_mat, dlog::Function)
  n, m = size(rels)
  @assert length(gens) == m
  (n==0 || m==0) && return gens, fmpz[], dlog
  @assert typeof(gens[1])==NfOrdQuoRingElem
  
  G=GrpAbFinGen(rels)
  S,mS=snf(G)
  
  function disclog(x)
    y=dlog(x)
    z=fmpz[s for s in y]
    a=(mS\(G(z)))
    return fmpz[a[j] for j=1:ngens(S)]
  end
  
  gens_snf=typeof(gens)(ngens(S))
  for i=1:ngens(S)
    x=(mS(S[i])).coeff
    for j=1:ngens(G)
      x[1,j]=mod(x[1,j],S.snf[end])
    end
    y=parent(gens[1])(1)
    for j=1:ngens(G)
      y*=gens[j]^(x[1,j])
    end
    gens_snf[i]= y
  end
  return gens_snf, S.snf, disclog
  
end

function snf_gens_rels_log(gens::Vector{NfOrdElem}, rels::fmpz_mat, dlog::Function, i::NfOrdIdl)
  Q , Qmap = quo(order(i),i)
  gens_quo = map(Q,gens)
  gens_trans, rels_trans, dlog_trans = snf_gens_rels_log(gens_quo,rels,dlog)
  @assert typeof(rels_trans)==Array{fmpz,1}
  return map(x->Qmap\x,gens_trans), rels_trans, dlog_trans
end

################################################################################
#
#  Discrete Logarithm In Cyclic Groups
#
################################################################################
# TODO compare with implementations in UnitsModM.jl

doc"""
***
    baby_step_giant_step(g, n, h) -> fmpz
    baby_step_giant_step(g, n, h, cache::Dict) -> fmpz

> Computes the discrete logarithm $x$ such that $h = g^x$.

> $g$ is a generator of order less than or equal to $n$
> and $h$ has to be generated by $g$.
> If a dictionary `cache` is supplied, it will be used to story the result
> of the first step. This allows to speed up subsequent calls with
> the same $g$ and $n$.
"""
function baby_step_giant_step(g, n, h, cache::Dict)
  @assert typeof(g) == typeof(h)
  n = BigInt(n)
  m = ceil(BigInt, sqrt(n))
  if isempty(cache)
    it = g^0
    for j in 0:m
      cache[it] = j
      it *= g
    end
  end
  if typeof(g) == fq_nmod
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

doc"""
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
  results = Vector{Tuple{fmpz,fmpz}}()
  for (p,v) in factor_n
    pv = p^v
    r = div(n,pv)
    c = _pohlig_hellman_prime_power(g^r,p,v,h^r)
    push!(results,(fmpz(c),fmpz(pv)))
  end
  return crt(results)[1]
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

################################################################################
#
#  Other Things
#
################################################################################

import Nemo.crt

doc"""
***
    crt(l::Vector{(Int,Int})) -> (fmpz, fmpz)
    crt(l::Vector{(fmpz,fmpz})) -> (fmpz, fmpz)

> Find $r$ and $m$ such that $r \equiv r_i (\mod m_i)$ for all $(r_i,m_i) \in l$
> and $m$ is the product of al $m_i$.
"""
function crt(l::Vector{Tuple{T,T}}) where T<:Union{fmpz,Int}
  isempty(l) && error("Input vector mustn't be empty")
  X = fmpz(l[1][1])
  M = fmpz(l[1][2])
  for (x,m) in l[2:end]
    X = crt(X,M,x,m)
    M *= m
  end
  return X, M
end

################################################################################
#
#   Multiplicative group for ray class group
#
################################################################################

function _multgrp_ray(Q::NfOrdQuoRing; method=nothing)

  gens = Vector{NfOrdQuoRingElem}()
  structt = Vector{fmpz}()
  disc_logs = Vector{Function}()
  i = ideal(Q)
  O = order(i)
  fac = factor(i)
  Q.factor = fac
  
  tame_part=Dict{NfOrdIdl, Tuple{NfOrdElem, fmpz, Function}}()
  wild_part=Dict{NfOrdIdl, Tuple{Array{NfOrdElem,1}, Array{fmpz,1}, Function}}()
  
  prime_power=Dict{NfOrdIdl, NfOrdIdl}()
  for (p,vp) in fac
    prime_power[p]= p^vp
  end
  
  
  for (p,vp) in fac
    gen_p, n_p, disclog_p = _multgrp_mod_p(p)
    tame_part[p]=(gen_p,n_p,disclog_p)
    dlog_p=1
    if vp == 1
      gens_p = [gen_p]
      struct_p = [n_p]
      dlog_p = function(x::NfOrdElem) return [disclog_p(x)] end
      
    else
      gens_pv, struct_pv , dlog_pv = _1_plus_p_mod_1_plus_pv(p,vp;method=method)
      obcs = lcm(struct_pv) # order of biggest cyclic subgroup
      g_p_obcs = powermod(gen_p,obcs,p.gen_one^vp)
      gens_p = [[g_p_obcs] ; gens_pv]

      struct_p = [[n_p] ; struct_pv]

      
      obcs_inv = gcdx(obcs,n_p)[2]
      function dlog_p(x::NfOrdElem)
        r = mod(disclog_p(x)*obcs_inv,n_p)
        x *= g_p_obcs^mod(-r,n_p)
        return [[r] ; dlog_pv(x)]
      end
    end
    
    # Make generators coprime to other primes
    if length(fac) > 1
      i_without_p = ideal(O,1)
      for (p2,vp2) in fac
        (p != p2) && (i_without_p *= prime_power[p2])
      end

      alpha, beta = idempotents(prime_power[p],i_without_p)
      for i in 1:length(gens_p)
        g_pi_new = beta*gens_p[i] + alpha
        @hassert :NfOrdQuoRing 2 (g_pi_new - gens_p[i] in prime_power[p])
        @hassert :NfOrdQuoRing 2 (g_pi_new - 1 in i_without_p)
        gens_p[i] = g_pi_new
      end
    end

    gens_new = map(Q,gens_p)
    append!(gens,gens_new)
    append!(structt,struct_p)
    push!(disc_logs,dlog_p)
    
    tame_part[p]=(gens_p[1],struct_p[1], disclog_p)
    if length(gens_p)>1
      wild_part[p]=(gens_p[2:end], struct_p[2:end], dlog_pv)
    end
  end



  function discrete_logarithm(x::NfOrdQuoRingElem)
    result = Vector{fmpz}()
    for dlog in disc_logs
      append!(result,dlog(x.elem))
    end
    return result
  end

  # Transform to SNF
  rels = matrix(diagm(structt))
  gens_trans, rels_trans, dlog_trans = snf_gens_rels_log(gens,rels,discrete_logarithm)

  mG=AbToResRingMultGrp(Q,gens_trans, rels_trans, dlog_trans)
  G=domain(mG)
  mG.tame=tame_part
  mG.wild=wild_part
  return G,mG
  
end

#################################################################################
#
#  p-part of the multiplicative group
#
#################################################################################


function prime_part_multgrp_mod_p(p::NfOrdIdl, prime::Int)
  @hassert :NfOrdQuoRing 2 isprime(p)
  O = order(p)
  Q , mQ = ResidueField(O,p)
  
  n = norm(p) - 1
  s=valuation(n,prime)
  powerp=prime^s
  m=div(n,powerp)
  
  powm=div(powerp,prime)
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
      return [w*inv]
    else
      return [Hecke._pohlig_hellman_prime_power(g,prime,s,t)*inv]
    end
  end
  
  return mQ\g , [powerp], disclog
end


function _mult_grp(Q::NfOrdQuoRing, p::Integer)

  O=Q.base_ring
  K=nf(O)

  
  gens = Vector{}()
  structt = Vector{fmpz}()
  disc_logs = Vector{Function}()
  
  tame=Dict{NfOrdIdl,Tuple{NfOrdElem,fmpz,Function}}() 
  wild=Dict{NfOrdIdl,Tuple{Array{NfOrdElem,1},Array{fmpz,1},Function}}()
  
  fac=factor(Q.ideal)
  Q.factor=fac
  y1=Dict{NfOrdIdl,Int}()
  y2=Dict{NfOrdIdl,Int}()
  for (q,e) in fac
    if divisible(norm(q)-1,p)
      y1[q]=Int(1)
    else 
      if divisible(norm(q),p) && e>=2
        y2[q]=Int(e)
      end
    end
  end
  
  prime_power=Dict{NfOrdIdl, NfOrdIdl}()
  for (q,vq) in fac
    prime_power[q]=q^vq
  end
  
  
  for (q,vq) in y1
    gens_q , struct_q , dlog_q = prime_part_multgrp_mod_p(q,p)
  
    # Make generators coprime to other primes
    if length(fac) > 1
      i_without_q = ideal(O,1)
      for (q2,vq2) in fac
        (q != q2) && (i_without_q *= prime_power[q2])
      end
      alpha, beta = idempotents(prime_power[q] ,i_without_q)
      gens_q = beta*gens_q + alpha
    end
 
    append!(gens,[Q(gens_q)])
    append!(structt,struct_q)
    push!(disc_logs,dlog_q)
    tame[q]=(gens_q, struct_q[1], dlog_q)
  end
  for (q,vq) in y2
    gens_q, snf_q, disclog_q = Hecke._1_plus_p_mod_1_plus_pv(q,vq)

    # Make generators coprime to other primes
    nq=norm(q)-1
    
    if length(fac) > 1
      i_without_q = ideal(O,1)
      for (p2,vp2) in fac
        (q != p2) && (i_without_q *= prime_power[p2])
      end

      alpha, beta = idempotents(prime_power[q],i_without_q)
      for i in 1:length(gens_q)
        gens_q[i] = beta*gens_q[i] + alpha
      end
    end
    
    ciclmax=prod(Set(snf_q))
    inv=gcdx(nq,ciclmax)[2]
    
    function dlog_q_norm(x::NfOrdElem)
      y=Q(x)^Int(nq)
      y=disclog_q(y.elem)
      for i=1:length(y)
        y[i]*=inv
      end
      return y
    end
        
    gensn = map(Q,gens_q)
    append!(gens,gensn)
    append!(structt,snf_q)
    push!(disc_logs,dlog_q_norm)
    wild[q]=(gens_q,snf_q,dlog_q_norm)
  end 
  
  G=DiagonalGroup(structt)
  
  function exp(a::GrpAbFinGenElem)
    
    x=Q(1)
    for i=1:ngens(G)
      if Int(a.coeff[1,i])!= 0
        x=x*(gens[i]^(Int(a.coeff[1,i])))
      end
    end
    return x
  
  end
  
  function dlog(x::NfOrdElem)
    result = Vector{fmpz}()
    for disclog in disc_logs
      append!(result,disclog(x))
    end
    return G(result)
  end
  
  mG=Hecke.AbToResRingMultGrp(G,Q,exp,dlog)
  mG.tame=tame
  mG.wild=wild
  return G, mG, merge(y1, y2)
end

####################################################################################
#
#  multiplicative group mod n
#
####################################################################################

function _n_part_multgrp_mod_p(p::NfOrdIdl, n::Int)
  @hassert :NfOrdQuoRing 2 isprime(p)
  O = order(p)
  Q , mQ = ResidueField(O,p)
  
  f=collect(keys(factor(fmpz(n)).fac))
  np = norm(p) - 1
  @assert gcd(n,np)!=1
  val=Array{Int,1}(length(f))
  for i=1:length(f)
    val[i]=valuation(np,f[i])
  end
  npart=prod([f[i]^(val[i]) for i=1:length(f) if val[i]!=0])
  m=div(np,npart)
  powm=[divexact(npart,f[i]) for i=1:length(f) if val[i]!=0]
  
  #
  #  We search for a random element with the right order
  #
  
  found=false
  g=Q(1)
  while found==false
    g = rand(Q)
    if g != Q(0) 
      g=g^m
      found=true
      for i=1:length(powm)
        if g^powm[i] == Q(1) 
          found=false
          continue
        end
      end     
    end
  end

  k=gcd(npart,n)
  inv=gcdx(m,fmpz(npart))[2]
  quot=divexact(npart, k)


  function disclog(x::NfOrdElem)
    t=mQ(x)^(m*quot)
    if iszero(t)
      error("Not coprime!")
    end
    if t==Q(1)
      return [Int(0)]
    end
    if k<20
      s=1
      w=g^quot
      el=w
      while el!=t
        s+=1
        el*=w
      end
      return [mod(s*inv,k) ]
    else 
      return [pohlig_hellman(g^quot,k,t)*inv] 
    end
  end
  
  return mQ\g , k, disclog
end

function _mult_grp_mod_n(Q::NfOrdQuoRing, y1::Dict{NfOrdIdl,Int}, y2::Dict{NfOrdIdl,Int},n::Integer)

  O=Q.base_ring
  K=nf(O)
 
  gens = Vector{NfOrdQuoRingElem}()
  structt = Vector{fmpz}()
  disc_logs = Vector{Function}()
  
  prime_power=Dict{NfOrdIdl, NfOrdIdl}()
  for (q,vq) in Q.factor
    prime_power[q]=q^vq
  end
 
  tame_mult_grp=Dict{NfOrdIdl,Tuple{NfOrdElem,fmpz,Function}}()
  wild_mult_grp=Dict{NfOrdIdl,Tuple{Array{NfOrdElem,1},Array{fmpz,1},Function}}()
  
  for (q,vq) in y1
    gens_q , struct_q , dlog_q = _n_part_multgrp_mod_p(q,n)
  
    # Make generators coprime to other primes
    if length(Q.factor) > 1
      i_without_q = ideal(O,1)
      for (q2,vq2) in Q.factor
        (q != q2) && (i_without_q *= prime_power[q2])
      end
      alpha, beta = idempotents(prime_power[q], i_without_q)
      gens_q = beta*gens_q + alpha
    end
 
    push!(gens,Q(gens_q))
    push!(structt,struct_q)
    push!(disc_logs,dlog_q)
    tame_mult_grp[q]=(gens_q, struct_q, dlog_q)
  
  end
  for (q,vq) in y2
    @assert vq>=2
    gens_q, snf_q, disclog_q = Hecke._1_plus_p_mod_1_plus_pv(q,vq)
    
    
    # Make generators coprime to other primes
    nq=norm(q)-1  
    if length(Q.factor) > 1
      i_without_q = ideal(O,1)
      for (p2,vp2) in Q.factor
        (q != p2) && (i_without_q *= prime_power[p2])
      end

      alpha, beta = idempotents(prime_power[q],i_without_q)
      for i in 1:length(gens_q)
        gens_q[i] = beta*gens_q[i] + alpha
      end
    end
    
    inv=gcdx(nq,snf_q[end])[2]
       
    function dlog_q_norm(x::NfOrdElem)
      y=Q(x)^Int(nq)
      Y=disclog_q(y.elem)
      for i=1:length(Y)
        Y[i]*=inv
      end
      return Y
    end
        
    gens_new = map(Q,gens_q)
    append!(gens,gens_new)
    append!(structt,snf_q)
    push!(disc_logs,dlog_q_norm)
    wild_mult_grp[q]=(gens_q, snf_q,dlog_q_norm)
  end 
  
  G=DiagonalGroup(structt)
  
  function exp(a::GrpAbFinGenElem)   
    x=Q(1)
    for i=1:ngens(G)
      if Int(a.coeff[1,i])!= 0
        x=x*(gens[i]^(Int(a.coeff[1,i])))
      end
    end
    return x
  end
  
  function dlog(x::NfOrdElem)
    result = Vector{fmpz}()
    for disclog in disc_logs
      append!(result,disclog(x))
    end
    return G(result)
  end
  
  mG=Hecke.AbToResRingMultGrp(G,Q,exp,dlog)
  
  return G, mG , tame_mult_grp, wild_mult_grp
end

