add_verbose_scope(:DiscLog)
add_assert_scope(:DiscLog)

function log_dict_rest(F::T, A, TA, idx=1)where T<:Union{Nemo.GaloisField, Nemo.GaloisFmpzField}
  cnt = 0
  if !wiedemann(A, TA)[1]
    @vprint :DiscLog 1 "wiedemann failed"
    return F
  end
  z = true 
  while z
   @vtime :DiscLog 2 kern = wiedemann(A, TA)[2]
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

  length(Logdict) == l ? (@vprint :DiscLog 1 "FB_LOGS: all FB logs found") : (@vprint :DiscLog 2 "FB_LOGS: at least $(l-length(Logdict)) logarithms not found") 
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
    @vprint :DiscLog 1 "FB_logs empty"
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

function disc_log_rest(a2, b2, F)
  @assert parent(a2) === parent(b2)
  b==1 && return fmpz(0)
  b==a && return fmpz(1)
  p = characteristic(F)
  rest = get_attribute(F, :rest)
  set_attribute!(F, :a=>F(2))
  if typeof(get_attribute(F, :RelMat))==Nothing
   SP = sieve_params(rest,0.02,1.01)
   @vtime :DiscLog 2 sieve(F, SP)
   #Base.log(p)/Base.log(10)<16 && @vtime :DiscLog 2 sieve(F, SP)
   #Base.log(p)/Base.log(10)>=16 && @vtime :DiscLog 2 sieve(F, (Int64(ceil(0.5*SP[1])),Int64(ceil(0.5*SP[2])), 1.01, SP[4]))
  end                     #later sieve2
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


@doc Markdown.doc"""
    disc_log(a, b, F = parent(a)) -> fmpz

Returns x such that a^x=b.
"""
function disc_log(a, b, F = parent(a)) #requires a to be primitive
  @assert parent(a) === parent(b)
  b==1 && return fmpz(0)
  b==a && return fmpz(1)
  p = characteristic(F)
  d = Dict(Hecke.factor(p-1))
  G = [] #log(a^(M/m_i), b^(M/m_i))
  M = [] #m_i
  for (k,v) in d
    if Base.log(k)/Base.log(10) < 14
      pot = k^v
      x = div(p-1, pot)
      a1 = a^x
      b1 = b^x
      g = disc_log_ph(a1, b1, k, v)
      push!(G, g) #a^x might be expensive
      push!(M, pot)
      delete!(d, k)
    end
  end
  if isempty(d)
   set_attribute!(F, :G=>G, :M=>M)
   return(crt(G,M))
  end
  for (k,v) in d
    rest = k^v
    set_attribute!(F, :rest=>rest)
    x = div(p-1, rest)
    a1 = a^x
    b1 = b^x
    @hassert :DiscLog 2 Base.log(rest)/Base.log(10)< 20
    @vprint :DiscLog 2 "uses IdxCalc"
    push!(G, disc_log_rest(a1,b1,F))
    push!(M, rest)
  end 
  set_attribute!(F, :G=>G, :M=>M)
  return crt(G,M)
end