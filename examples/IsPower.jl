module IsPower

using Hecke, InteractiveUtils
import Nemo

function ispower_mod_p(a::nf_elem, i::Int)

  p = 2^10
  K = parent(a)
  f = K.pol
  first = true
  cnt = 0
  local opt
  while true
    p = next_prime(p)
    lp = factor(f, GF(p))
    if any(x->x>1, values(lp.fac))
      continue
    end
    if any(x->degree(x) > 60, keys(lp.fac))
      continue
    end
    if first
      opt = (p, length(lp))
      first = false
    else
      if length(lp) < opt[2]
        opt = (p, length(lp))
        cnt = 0
      else
        cnt += 1
      end
    end
    if cnt > 2*i
      break
    end
  end
  println("using ", opt[1], " with ", opt[2], " local factors")

  C = Hecke.qAdicConj(K, opt[1])
  p = opt[1]


  r_pr = 20
  local con_r
  while true
    con_r = map(abs, conjugates(a, r_pr))
    map(contains_zero, con_r)
    if any(x->contains_zero(x), con_r)
      r_pr += 20
    else
      con_r = [root(x, i) for x = con_r]
      break
    end
  end
  function power_sum(l::Int)
    return Hecke.upper_bound(sum(x^l for x = con_r), fmpz)
  end

  @show bd = map(power_sum, 1:15)
  pr = clog(bd[end], p) + 45
  println("using a precision of ", pr)
  con_p = conjugates(a, C, pr,all = false, flat = false)
  #= this might work
    identify primes where the minpoly is the same (in those completions
    the conjugates would be the same, hence the roots are the same)
    work with just one rep there
  =#

  di = Dict{gfp_poly, Array{Int, 1}}()
  st = Int[]
  fpx = PolynomialRing(GF(p), cached = false)[1]
  for i=1:length(con_p)
    fq, mfq = ResidueField(parent(con_p[i]))
    mu = minpoly(fpx, mfq(con_p[i]))
    if haskey(di, mu)
      push!(di[mu], i)
      error("element not primitive, case not supported (yet)")
    else
      if degree(mu) < degree(fq)
        error("element not primitive, case not supported (yet)")
      end
      di[mu] = [i]
      push!(st, i)
    end
  end
  @show di, st

  con_p = con_p[st]
  @show st, collect(values(di))

  con_pr = [roots(x, i) for x = con_p]
  no_fac = sum(map(length, con_pr))
  j = 0
  trafo = identity_matrix(FlintZZ, no_fac)
  no_rt = no_fac
  while true
    j += 1
    if j >= length(bd)
      bd = vcat(bd, map(power_sum, length(bd)+1:length(bd)+5))
    end
    data = matrix([reduce(vcat, [map(x -> lift(trace(x^j)), y) for y = con_pr])])
    data = sub(trafo, 1:no_rt, 1:no_fac)*data
    k = clog(bd[j], p)
    @assert k < pr
    pk = fmpz(p)^(pr-k)
    map_entries!(x->rem(div(x, fmpz(p)^(k)), pk), data, data)
    if iszero(data)
      println("nothing new...")
      continue
    end
    trafo = hcat(trafo, data)
    data = zero_matrix(FlintZZ, 1, ncols(trafo))
    data[1, end] = pk
    trafo = vcat(trafo, data)
    #= roots: products of the local roots that ar small
       corresponds to sums of local power-sums that are small
       the "correct" one will have no_fac ones in the front
         rear  (a+b) < bd => (a+b)/c < bd/c
         round((a+b)/c) - round(a/c) - round(b/c)
    =# 
    no_rt, trafo = lll_with_removal(trafo, fmpz(p)^2*fmpz(2*no_fac)) #THINK
    trafo = sub(trafo, 1:no_rt, 1:ncols(trafo))
    d = Dict{fmpz_mat, Array{Int, 1}}()
    for l=1:no_fac
      k = trafo[:, l]
      if haskey(d, k)
        push!(d[k], l)
      else
        d[k] = [l]
      end
    end
    println("partition: ", values(d))
    if all(x->length(x) >= length(con_pr), values(d))
      # we have a candidate!
      mp = Dict{Int, Int}()
      j = 1
      h = 1
      for z = con_pr
        for k = j:j+length(z)-1
          mp[k] = h
        end
        h += 1
        j += length(z)
      end
      println(mp)
      m = Base.minimum(map(length, values(d)))
      pa = d[findfirst(x->length(x) == m, d)]
      co = reduce(vcat, con_pr)
      @show mp, pa
      mC = completions(C)
      @show [mp[x] for x = pa]
      mo = factors(C)
      va = zeros(K, length(mo))
      for x = pa
        y = Hecke.mod_sym(preimage(mC[mp[x]], co[x]), fmpz(p)^pr)
        h = st[mp[x]]
        j = findfirst(j-> h in j, di)
        @show x, mp[x], h, di[j]
        for k in di[j]
          @assert iszero(va[k])
          va[k] = y
        end
      end
#      va = [Hecke.mod_sym(preimage(mC[mp[x]], co[x]), fmpz(p)^pr) for x = pa]
      @assert length(mo) == length(va)
      return crt(map(Hecke.Globals.Zx, va), mo, C.C.H, fmpz(p)^pr)
      return va, mo, C
    end
    if j > 40 error("") end
  end
end  

function Hecke.crt(A::Array{<:NfAbsOrdElem, 1}, I::Array{<:NfAbsOrdIdl, 1})
  while length(I) > 1
    II = typeof(I[1])[]
    AA = typeof(A[1])[]
    i = 1
    while i< length(I)
      push!(II, I[i]*I[i+1])
      push!(AA, crt(A[i], I[i], A[i+1], I[i+1]))
      i += 2
    end
    if i == length(I)
      push!(II, I[end])
      push!(AA, A[end])
    end
    I = II
    A = AA
  end
end

function Base.lastindex(M::MatElem, i::Int)
  i == 1 && return nrows(M)
  i == 2 && return ncols(M)
  error("illegal dimensino")
end

function Hecke.ispower(a::qadic, i::Int)
  @assert i>0
  if i==1
    return true, a
  end

  k, mk = ResidueField(parent(a))
  v = valuation(a)
  if v % i != 0
    return false, a
  end
  rv = divexact(v, i)
  a = divexact(a, uniformizer(parent(a))^v)

  fl, bp = ispower(mk(a), i)
  if !fl
    return false, a
  end

  b = preimage(mk, bp)

  p = precision(a)
  while p > 0
    b = b - (b^i-a)//(i*b^(i-1))
    p = div(p, 2)
  end
  return true, b*uniformizer(parent(a))^rv
end

function Hecke.roots(a::qadic, i::Int)
  @assert i>0
  if i==1
    return a
  end

  k, mk = ResidueField(parent(a))
  v = valuation(a)
  if v % i != 0
    error("elem not an $i-th power")
  end
  rv = divexact(v, i)
  a = divexact(a, uniformizer(parent(a))^v)

  fl, bp = ispower(mk(a), i)
  if !fl
    error("elem not an $i-th power")
  end

  local zeta
  j = gcd(size(k)-1, i) 
  if j != 1
    while true
      zeta = rand(k)^(divexact(size(k)-1, j))
      if all(l-> !isone(zeta^l), 1:j-1)
        break
      end
    end
  else
    zeta = k(1)
  end

  b = preimage(mk, bp)
  z = preimage(mk, zeta)

  p = precision(a)
  while p > 0
    b = b - (b^i-a)//(i*b^(i-1))
    if !isone(zeta)
      z = z - (z^j-one(parent(z)))//(j*z^(j-1))
    end
    p = div(p, 2)
  end
  b *= uniformizer(parent(a))^rv
  if !isone(zeta)
    return [b*z^l for l=0:Int(j)-1]
  else
    return [b]
  end
end

function completions(C::qAdicConj)
  mC = []
  K = C.K
  a = gen(K)
  z = conjugates(a, C, 5, all = false)
  for t = z
    _, x = completion(K, t)
    push!(mC, x)
  end
  return mC
end

function factors(C::qAdicConj)
  return [x[1] for x = Hecke.factor_mod_pk(Array, C.C.H, Int(C.C.H.N))]
end

function Base.getindex(H::Hecke.HenselCtx, s::Symbol, i::Int)
  r = H.r
  @assert 1<= i<=2*r-2
  if s == :l
    return unsafe_load(H.link, i)
  elseif s == :v
    f = Hecke.Globals.Zx()
    @GC.preserve f H ccall((:fmpz_poly_set, Nemo.libflint), Cvoid, (Ref{fmpz_poly}, Ptr{Hecke.fmpz_poly_raw}), f, H.v+(i-1)*sizeof(Hecke.fmpz_poly_raw))
    return f
  elseif s == :w
    f = Hecke.Globals.Zx()
    @GC.preserve f H ccall((:fmpz_poly_set, Nemo.libflint), Cvoid, (Ref{fmpz_poly}, Ptr{Hecke.fmpz_poly_raw}), f, H.w+(i-1)*sizeof(Hecke.fmpz_poly_raw))
    return f
  end
end

function Hecke.mod_sym!(f::fmpz_poly, n::fmpz)
  for i=degree(f):-1:0
    setcoeff!(f, i, Hecke.mod_sym(coeff(f, i), n))
  end
  return f
end

function Hecke.crt(v::Array{fmpz_poly, 1}, m::Array{fmpz_poly, 1}, H::Hecke.HenselCtx, pk::fmpz = fmpz(H.p)^H.prev)
  if length(v) == 1
    return v[1]
  end
  p = fmpz(H.p)
  r = H.r
  res = fmpz_poly[]
  for i = 1:2*r-2
    @show mu = H[:l, i]
    if mu < 0
      push!(res, divrem(v[-mu], H[:v, -mu])[2])
      mod_sym!(res[end], pk)
      continue
    end
    f = H[:v, mu+1]
    g = H[:v, mu+2]
    t = f*H[:w, mu+1] + g*H[:w, mu+2] - 1
#    @show map(x->valuation(coeff(t, x), p), 0:degree(t))
#    @assert all(x->valuation(coeff(t, x), p) > 1, 0:degree(t))
    push!(res, res[mu+2]*f*H[:w, mu+1] + res[mu+1]*g*H[:w, mu+2])
    mod_sym!(res[end], pk)
    res[end] = divrem(res[end], H[:v, length(res)])[2]
    mod_sym!(res[end], pk)
#    t = divrem(res[end], f)[2] - res[mu+1];
#    @show map(x->valuation(coeff(t, x), p), 0:degree(t))
#
#    t = divrem(res[end], g)[2] - res[mu+2];
#    @show map(x->valuation(coeff(t, x), p), 0:degree(t))
  end
  mu = 2*r-4
  f = H[:v, mu+1]
  g = H[:v, mu+2]
#    t = f*H[:w, mu+1] + g*H[:w, mu+2] - 1
#    @show map(x->valuation(coeff(t, x), p), 0:degree(t))
  push!(res, res[mu+2]*f*H[:w, mu+1] + res[mu+1]*g*H[:w, mu+2])
  mod_sym!(res[end], pk)

  f = deepcopy(H.f)
  f.parent = res[end].parent
  res[end] = divrem(res[end], f)[2]
  mod_sym!(res[end], pk)

  return res[end]
end

function Hecke.degree(R::qadic) #TODO XXXX
  return R.length
end

function Hecke.ideal(R::NfAbsOrd, f::MapFromFunc{AnticNumberField,FlintQadicField})
  K = nf(R)
  Cq = codomain(f)
  if degree(Cq) == degree(K)
    return prime(Cq)^precision(Cq)*R
  end
  p = prime(Cq)
  C = qAdicConj(K, Int(p))
  r = roots(C.C, 5)
  fa = f(gen(K))
  k = precision(fa)
  lf = Hecke.factor_mod_pk(C.C.H, k)
  for fp = keys(lf)
    kfa = fp(setprecision(fa, 2))
    if iszero(kfa)
      s = R(fp(gen(K)))
      if valuation(norm(s), p) > k
        s += p^k
      end
      i = ideal(R, p^k, s)
      i.gens_normal = p
      i.norm = (p^k)^degree(Cq)
      i.minimum = p^k
      return i
    end
  end
end

end

