include("IndexCalculus.jl")

function log_dict_rest(F::T, A, TA, idx=1)where T<:Union{Nemo.GaloisField, Nemo.GaloisFmpzField}
  cnt = 0
  if !wiedemann(A, TA)[1]
    @warn "wiedemann failed"
    return F
  end
  z = true 
  while z
    kern = wiedemann(A, TA)[2]
    cnt+=1
    cnt < 5 || return Dict{fmpz, fmpz}([]),Vector{fmpz_mod}([]),FactorBase(fmpz[])
    if !iszero(kern)
      z = false
    end
  end
  kern = inv(kern[idx]).*kern #norm kernelvec
  Q,L = Array{fmpz}([]),Array{fmpz}([])
  FB = get_attribute(F, :FB_array)
  l = get_attribute(F, :fb_length)
  Q = FB[1:l] 
  L = kern[1:l]

  Logdict = Dict(zip(Q,L))

  length(Logdict) == l ? (@info "FB_LOGS: all FB logs found") : (@warn "FB_LOGS: at least $(length(Logdict)-l) logarithms not found") 
  set_attribute!(F, :Logdict=>Logdict, :kern=>kern, :Q=>FactorBase(Q), :idx=>idx)
  return F
end

function log_rest(F, b2) 
  rest = get_attribute(F, :rest)
  RR = get_attribute(F, :RR)
  p_elem = F(2)
  FB = get_attribute(F, :Q)
  FB_logs = get_attribute(F, :Logdict)
  if typeof(FB_logs)==Nothing
    @warn "FB_logs empty"
    return 0
  end
  randomexp = fmpz(rand(1:p))
  while !issmooth(FB,fmpz(lift(b2*p_elem^randomexp)))
    randomexp = fmpz(rand(1:p))
  end  
  factorization = Hecke.factor(FB,lift(b2*p_elem^randomexp))

  logb = -randomexp + sum([exp*FB_logs[prime] for (prime,exp) in factorization])
  return logb
end

function IdxCalc2(a::T, b::T, F=parent(a)) where T<:Union{gfp_elem, gfp_fmpz_elem}
  @assert parent(a) === parent(b)
  b==1 && return fmpz(0)
  b==a && return fmpz(1)
  set_attribute!(F, :a=>a)
  #typeof(get_attribute(F, :Logdict))==Nothing || @goto Logdict
  #typeof(get_attribute(F, :RelMat))==Nothing || @goto RelMat
  if typeof(get_attribute(F, :RelMat))==Nothing
    sieve2(F)
  end
  if typeof(get_attribute(F, :Logdict))==Nothing
    p = get_attribute(F, :p)
    _modulus = div((p-1),2)
    two = fmpz(2)
    #F2 = GF(_modulus)
    F2 = ResidueRing(ZZ, _modulus) #change it when prepro fixed
    set_attribute!(F, :F2=>F2)
    c, u, v = gcdx(two, _modulus)
    c == 1 || (@error "FB_LOGS: 2 ,(p-1)/2 not coprime")
    set_attribute!(F, :u=>u, :v=>v)
    set_attribute!(F, :_modulus=>_modulus)
    #Preprocessing
    A = change_base_ring(F2, get_attribute(F,:RelMat))
    TA = transpose(A)
    A, TA = sp_prepro(A, TA, get_attribute(F, :fb_length))
    #Wiedemann + dict with logs of FB
    log_dict2(F, A, TA)
  end
  logb = log(F, b)
  if logb == 0
    return logb, F
  end
  if a != get_attribute(F, :primitive_elem)
    p = get_attribute(F, :p)
    loga = log(F, a)
    logb = solvemod(loga, logb, p-1)
  end
  return logb, F 
end

function disc_log_rest(a2, b2, F)
  @assert parent(a2) === parent(b2)
  b==1 && return fmpz(0)
  b==a && return fmpz(1)
  p = characteristic(F)
  set_attribute!(F, :a=>F(2))
  if typeof(get_attribute(F, :RelMat))==Nothing
   sieve(F)
  end                     #later sieve2
  small_prod = get_attribute(F, :small_prod)
  rest = get_attribute(F, :rest)
  #Preprocessing
  RR = ResidueRing(ZZ, rest)#falsches p ?
  set_attribute!(F, :RR=>RR)
  A = change_base_ring(RR,get_attribute(F,:RelMat))
  TA = transpose(A)
  A, TA = sp_prepro(A, TA, get_attribute(F, :fb_length))
  #Wiedemann + dict with logs of FB
  log_dict_rest(F, A, TA)
  FB_array = get_attribute(F, :FB_array)
  idx = get_attribute(F, :idx)
  g2 = log_rest(F, b2)
  if lift(a2) != FB_array[idx]
    g2 = solvemod(lift(log_rest(F, a2)), lift(g2), rest)
  end
  return g2
end



function disc_log(a, b, F=parent(a)) #p prime
  @assert parent(a) === parent(b)
  b==1 && return fmpz(0)
  b==a && return fmpz(1)
  p = characteristic(F)
  if log(p)/log(10)<13
    @info "only bsgs used"
    return disc_log_bs_gs(a,b,p-1), F #or ph -> compare time
  end
  d,t = Hecke.factor_trial_range(p-1)
  d = sort(d)
  small_prod = t
  rest = p-1
  for (k,v) in d
    pow_ = k^v
    divexact!(rest, pow_)
    mul!(small_prod, small_prod, pow_)
  end
  h = maximum(keys(d))
  if rest == 1
    rest = h^d[h]
    divexact!(small_prod, rest)
  end
  set_attribute!(F, :small_prod=>small_prod)
  set_attribute!(F, :rest=>rest)
  if small_prod == 2
    return IdxCalc(a, b) 
  end
  @assert log(small_prod)/log(10) < 13
  a1 = a^rest #primitive element for small_prod
  a2 = a^small_prod #primitive element for rest
  b1 = b^rest
  b2 = b^small_prod
  set_attribute!(F, :a1=>a1, :a2=>a2, :b1=>b1, :b2=>b2)
  @assert log(small_prod)/log(10)<13
  g1 = disc_log_bs_gs(a1,b1,small_prod)
  if log(rest)/log(10)<13
    g2 = disc_log_bs_gs(a2,b2,rest)
    @info "bsgs for rest"
    return crt(g1, small_prod, g2, rest), F
  else
    @info "IdxCalc for rest"
    @assert log(rest)/log(10)< 21
    g2 = disc_log_rest(a2, b2, F)
  end
  return crt(g1, small_prod, g2, rest), F
end