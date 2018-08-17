export UnitGroup, solvemod, gen_mod_pk, 
       disc_log_bs_gs, disc_log_ph, disc_log_mod

function order(x::Generic.Res{fmpz}, fp::Dict{fmpz, Int64})
  error("missing")
end


Markdown.doc"""
  isprimitive_root(x::Generic.Res{fmpz}, M::fmpz, fM::Dict{fmpz, Int64}) Bool

>  Given x in Z/MZ, the factorisation of M (in fM), decide if x is primitive.
>  Intrinsically, only makes sense if the units of Z/MZ are cyclic.
"""
function isprimitive_root(x::Generic.Res{fmpz}, M::fmpz, fM::Fac{fmpz})
  for (p, l) in fM
    if x^divexact(M, p) == 1
      return false
    end
  end
  return true
end


#=
  for p = 2 this is trivial, as <-1, 5> are generators independently of 
  everything.
  Assume p>2 is odd.
  Then (Z/p^k)^* = <g> with some unknown g, independently of k
  We want
  <g>/<g^m> = <A> for A = g^a, independently of k, depending on m
  (to avoid having to factor p-1, assuming that m is small)
  
  Let G_k = <g+ p^kZ>/<g^m + p^k Z> and ord_k(A) the order of A in G_k

  Then ord_k(A) = |G_k|/gcd(|G_k|, a), 
          |G_k| = gcd(phi(p^k), m) = gcd((p-1)p^(k-1), m)
  
  ord_k    (A) = |G_k|      iff gcd(|G_k|    , a) = 1
  ord_(k+1)(A) = |G_(k+1)|  iff gcd(|G_(k+1)|, a) = 1
  Since either |G_k| = |G_(k+1)| or 
              p|G_k| = |G_(k+1)|
  we get (from the constant gcd) that wither a is coprime to p, hence
  the gcd will be stable for all subsequent k's as well, or
  |G_k| is stable (other gcd) hence will be stable. In either case,
  gcd(|G_(k+l)|, a) = 1 for all l, thus a is a generator
=#
  
Markdown.doc"""
  gen_mod_pk(p::fmpz, mod::fmpz=0) fmpz

>  Find an integer x s.th. x is a primtive root for all powers of the (odd) prime p. If mod is non zero, it finds a generator for Z/p^kZ modulo mod powers only.
"""
function gen_mod_pk(p::fmpz, mod::fmpz=fmpz(0))
  @assert isodd(p)
  @assert isprime(p)
  gc = gcd(p-1, mod)
  mi = divexact(p-1, gc)
  fp = factor(gc)
  Rp = ResidueRing(FlintZZ, p, cached=false)
  Rpp = ResidueRing(FlintZZ, p*p, cached=false)

  g = fmpz(2)
  if isprimitive_root(Rp(g)^mi, gc, fp)
    if Rpp(g)^gc != 1
      return g
    else
      return g+p
    end
  end

  while true
#    g = rand(3:p-2)
    g += 1
    if isprimitive_root(Rp(g)^mi, gc, fp)
      if Rpp(g)^gc != 1
        return g
      else
        return g+p
      end
    end
  end
end

mutable struct MapUnitGroupModMGenRes{T} <: Map{T, Generic.ResRing{fmpz}, HeckeMap, MapUnitGroupModMGenRes}
  header::Hecke.MapHeader

  function MapUnitGroupModMGenRes{T}(G::T, R::Generic.ResRing{fmpz}, dexp::Function, dlog::Function) where {T}
    r = new{T}()
    r.header = Hecke.MapHeader(G, R, dexp, dlog)
    return r
  end
end

mutable struct MapUnitGroupModM{T} <: Map{T, Nemo.NmodRing, HeckeMap, MapUnitGroupModM}
  header::Hecke.MapHeader

  function MapUnitGroupModM{T}(G::T, R::Nemo.NmodRing, dexp::Function, dlog::Function) where {T}
    r = new{T}()
    r.header = Hecke.MapHeader(G, R, dexp, dlog)
    return r
  end
end

Markdown.doc"""
  UnitGroup(R::Generic.ResRing{fmpz}) GrpAbFinGen, Map

>  The unit group of R = Z/nZ together with the apropriate map.
"""
#TO BE FIXED. If mod is non-zero, it is wrong.
function UnitGroup(R::Generic.ResRing{fmpz}, mod::fmpz=fmpz(0))

  m = R.modulus
  fm = factor(m).fac
  
  r = Array{fmpz}(undef, 0)
  g = Array{fmpz}(undef, 0)
  mi = Array{fmpz}(undef, 0)
  for p=keys(fm)
    k = fm[p]
    if gcd(mod, (p-1)*p^(max(0, k-1))) == 1
      continue
    end
    pk = p^k
    if p==2  && iseven(mod)
      if k==1
        continue
      elseif k==2 
        push!(r, 2)
        push!(mi, pk)
        gg = fmpz(-1)
        if m == pk
          push!(g, gg)
        else
          push!(g, crt(fmpz(-1), pk, fmpz(1), divexact(m, pk)))
        end
      else
        mpk = divexact(m, pk)
        push!(r, 2)
        push!(r, gcd(p^(k-2), mod))  # cannot be trivial since mod is even
        push!(mi, fmpz(4))
        push!(mi, pk)
        if mpk == 1
          push!(g, fmpz(-1))
          push!(g, fmpz(5))
        else
          push!(g, crt(fmpz(-1), pk, fmpz(1), mpk))
          push!(g, crt(fmpz(5), pk, fmpz(1), mpk))
        end
      end
    else
      mpk = divexact(m, pk)
      s = gcd((p-1)*p^(fm[p]-1), mod)
      if s==1 
        continue
      end
      push!(r, s)
      push!(mi, pk)
      gg = gen_mod_pk(p, mod)
      gg = powmod(gg, divexact(p-1, gcd(p-1, mod)), m)
      if mpk == 1
        push!(g, gg)
      else
        push!(g, crt(gg, pk, fmpz(1), mpk))
      end
    end
  end

  G = DiagonalGroup(r)
  function dexp(x::GrpAbFinGenElem)
    return prod([R(g[i])^x[i] for i=1:ngens(G)])
  end
  function dlog(x::Generic.Res{fmpz})
    return G([disc_log_mod(g[i], lift(x), mi[i]) for i=1:ngens(G)])
  end
  return G, MapUnitGroupModMGenRes{typeof(G)}(G, R, dexp, dlog)
end

function UnitGroup(R::Nemo.NmodRing, mod::fmpz=fmpz(0))

  m = Int(R.n)
  fm = factor(fmpz(m)).fac
  
  r = Array{fmpz}(undef, 0)
  g = Array{fmpz}(undef, 0)
  mi = Array{fmpz}(undef, 0)
  for p=keys(fm)
    k = fm[p]
    if gcd(mod, (p-1)*p^(max(0, k-1))) == 1
      continue
    end
    pk = p^k
    if p==2  && iseven(mod)
      if k==1
        continue
      elseif k==2 
        push!(r, 2)
        push!(mi, pk)
        gg = fmpz(-1)
        if m == pk
          push!(g, gg)
        else
          push!(g, crt(fmpz(-1), pk, fmpz(1), divexact(m, pk)))
        end
      else
        mpk = divexact(m, pk)
        push!(r, 2)
        push!(r, gcd(p^(k-2), mod))  # cannot be trivial since mod is even
        push!(mi, fmpz(4))
        push!(mi, pk)
        if mpk == 1
          push!(g, fmpz(-1))
          push!(g, fmpz(5))
        else
          push!(g, crt(fmpz(-1), pk, fmpz(1), mpk))
          push!(g, crt(fmpz(5), pk, fmpz(1), mpk))
        end
      end
    else
      mpk = divexact(m, pk)
      s = gcd((p-1)*p^(fm[p]-1), mod)
      if s==1 
        continue
      end
      push!(r, s)
      push!(mi, pk)
      gg = gen_mod_pk(p, mod)
      gg = powmod(gg, divexact(p-1, gcd(p-1, mod)), fmpz(m))
      if mpk == 1
        push!(g, gg)
      else
        push!(g, crt(gg, pk, fmpz(1), mpk))
      end
    end
  end

  G = DiagonalGroup(r)
  function dexp(x::GrpAbFinGenElem)
    return prod([R(g[i])^x[i] for i=1:ngens(G)])
  end
  function dlog(x::nmod)
    return G([disc_log_mod(g[i], lift(x), mi[i]) for i=1:ngens(G)])
  end
  return G, MapUnitGroupModM{typeof(G)}(G, R, dexp, dlog)
end

Markdown.doc"""
  solvemod(a::fmpz, b::fmpz, M::fmpz)

>  Finds x s.th. ax == b mod M.
"""
function solvemod(a::fmpz, b::fmpz, M::fmpz)
  #solve ax = b (mod M)
  g = gcd(a, M)
  if g==1
    return invmod(a, M)*b % M
  end
  a = divexact(a, g)
  @assert b%g == 0
  Mg = divexact(M, g)
  return invmod(a, Mg)* divexact(b, g) %Mg
end


Markdown.doc"""
  disc_log_mod(a::fmpz, b::fmpz, M::fmpz)

>  Computes g s.th. a^g == b mod M. M has to be a power of an odd prime
>  and a a generator for the multiplicative group mod M
"""
#solves a^x = b (mod M) for M a prime power
function disc_log_mod(a::fmpz, b::fmpz, M::fmpz)
  fM = factor(M).fac
  @assert length(keys(fM)) == 1
  p = first(keys(fM))
  if p==2
    if (a+1) % 4 == 0
      if b%4 == 3
        return fmpz(1)
      else
        return fmpz(0)
      end
    elseif a % M ==5
      if b%4 == 3
        b = -b
      end
      g = fmpz(0)
      if (b-5) % 8 == 0
        g += 1
        b = b* invmod(a, M) % M
      end 
      @assert (b-1) % 8 == 0
      @assert (a^2-1) % 8 == 0
      F = FlintPadicField(p, fM[p])
      g += 2*lift(divexact(log(F(b)), log(F(a^2))))
      return g
    else
      error("illegal generator mod 2^$(fM[p])")
    end
  end

  ## we could do the odd priems case using the same p-adic
  #  log approach...
     
  @assert isodd(p)

  Fp = ResidueRing(FlintZZ, p, cached=false)
  g = disc_log_bs_gs(Fp(a), Fp(b), p-1)
#  println("1st level ", g)
  
  #so b*a^-r = 1 mod p, a^(p-1) = 1 mod p
  # in fact, a^(p-1) should be a multiplicative generator for
  # (1+pZ) mod p^k for all k
  #= Plan:
    a^x = b, x = r + (p-1)*y, 0<= r < p-1 and y>=0
    a^(p-1)y = ba^-r and now both a^(p-1) and ba^-r are =1 (p)
    if A, B = 1 mod p and A^y = B, then
    A = 1*px_1, B = 1+pb_1, A^y = 1+pyx_1 + p^2...
    so yx_1 = b_1 mod p, solve this,

    By induction:
    A = 1+p^lx_l, B = 1+p^lb_l, then
    A^y = 1+p^lyx_l + p^(2l)..., thus
    yx_l = b_l mod p^l
  =#
 
  A = powmod(a, p-1, M)
  B = b*powmod(a, -g, M) %M
  @assert B%p == 1
  @assert A%p == 1
  lp = [fM[p]]
  while lp[end] > 1
    push!(lp, div(lp[end]+1, 2))
  end
  push!(lp, 0)
#  println("lp: $lp")
#TODO: too much powering and fiddling. It works and is correct
#      but needs sorting
  #we are in 1+p^lp[i+1]X mod p^lp[i]
  #so X is defined mod p^(lp[i]-lp[i+1])
  #since A=1+p^lp[i+1] = a^(p-1)^lp[i+1], g is adjusted by x*(p-1)*p^lp[i+1]
  for i=length(lp)-2:-1:1
    pim = p^lp[i]
    pim1 = p^lp[i+1]
    pd = p^(lp[i]-lp[i+1])
#    println(typeof(pim1), typeof(g), typeof(p), "pim1=$pim1")
    @assert A %pim1 == 1
    @assert B %pim1 == 1
    Ai = divexact(A-1, pim1) % pd
    Bi = divexact(B-1, pim1) % pd
    #need to solve x Ai = Bi (pd), however Ai might not be coprime
#    println("solve $Ai x X = $Bi mod $pd")
    yi = solvemod(Ai, Bi, pd)
#    println("Ai=$Ai, Bi=$Bi, yi=$yi, pim1 = $pim1")
    g += yi*(p-1)*p^(lp[i+1]-1)
#    println("for pim1=$pim1 yi=$yi g=$g")
#    println(valuation(b*powmod(a, -g, M)-1, p))
    B = B*powmod(A, -yi, M) % M
    A = powmod(a, (p-1)*divexact(pim, p), M)
  end
  return g
end

Markdown.doc"""
  disc_log_bs_gs{T}(a::Generic.Res{T}, b::Generic.Res{T}, o::fmpz)

>  Tries to find g s.th. a^g == b under the assumption that g <= o.
>  Uses Baby-Step-Giant-Step
"""
function disc_log_bs_gs(a::Generic.Res{T}, b::Generic.Res{T}, o::fmpz) where {T <: Union{PolyElem, fmpz, fq_nmod_poly, fq_poly, nmod_poly}}
  b==1 && return fmpz(0)  
  b==a && return fmpz(1)
  if o < 100 
    ai = inv(a)
    for g=1:Int(o)
      b *= ai
      b==1 && return fmpz(g)
    end
    throw("disc_log failed")
  else
    r = root(o, 2)
    r = Int(r)
    baby = Array{typeof(a), 1}(undef, r)
    baby[1] = parent(a)(1)
    baby[2] = a
    for i=3:r
      baby[i] = baby[i-1]*a
      baby[i] == b && return fmpz(i-1)
    end
    giant = baby[end]*a
    @assert giant == a^r
    b == giant && return fmpz(r)
    giant = inv(giant)
    g = fmpz(0)
    for i=1:r
      b *= giant
      g += r
      f = findfirst(baby, b)
      f >0 && return fmpz(g+f-1)
    end
    throw("disc_log failed")
  end
end


Markdown.doc"""
  disc_log_ph{T <:PolyElem}(a::Residue{T}, b::Residue{T}, o::fmpz, r::Int)
  disc_log_ph(a::Residue{fmpz}, b::Residue{fmpz}, o::fmpz, r::Int)
  disc_log_ph(a::Residue{fq_nmod_poly}, b::Residue{fq_nmod_poly}, o::fmpz, r::Int)
  disc_log_ph(a::Residue{fq_poly}, b::Residue{fq_poly}, o::fmpz, r::Int)
  disc_log_ph(a::Residue{nmod_poly}, b::Residue{nmod_poly}, o::fmpz, r::Int)

>  Tries to find g s.th. a^g == b under the assumption that ord(a) | o^r
>  Uses Pohlig-Hellmann and Baby-Step-Giant-Step for the size(o) steps.
  """
function disc_log_ph(a::Generic.Res{T}, b::Generic.Res{T}, o::fmpz, r::Int) where {T <: Union{PolyElem, fmpz, fq_nmod_poly, fq_poly, nmod_poly}}
  #searches for g sth. a^g = b
  # a is of order o^r
  # Pohlig-Hellmann a^g = b => (a^o)^g = b^g
  g = 0
  aa = a^(o^(r-1))
  for s=r:-1:1
    bb = b*inv(a)^g
    gg = disc_log_bs_gs(aa, bb^(o^(s-1)), o)
    g = g+o^(r-s)*gg
  end
  return g
end


function unit_group_mod(R::Nemo.NmodRing, n::Int)

  fm = factor(fmpz(R.n)).fac
  gens = Array{Int,1}(undef, 0)
  structt = Int[]
  disclogs = Function[]

  for (p,v) in fm
    gensp, structp, disclog_p = _unit_pk_mod_n(Int(p), v, n)
    if length(fm)>1
      e=Int(p)^v
      f=div(Int(R.n), e)
      d,a,b=gcdx(e,f)
      for i=1:length(gensp)
        gensp[i]=Int((R(gensp[i])*b*f).data)+a*e
      end
    end
    append!(gens, gensp)
    append!(structt, structp)
    push!(disclogs, disclog_p)
  end

  G=DiagonalGroup(structt)
  
  function disclog(x::nmod)
    res=Int[]
    for i=1:length(disclogs)
      append!(res, disclogs[i](Int(x.data)))
    end
    return G(res)
  end
  
  function expon(a::GrpAbFinGenElem)
    res=R(1)
    for i=1:ngens(G)
      if a[i]!=0
        res*=R(gens[i])^Int(a[i])
      end
    end
    return res
  end

  return G, MapUnitGroupModM{typeof(G)}(G, R, expon, disclog)

end


function _unit_pk_mod_n(p::Int, v::Int, n::Int)

  #First, multiplicative group mod p
  if isodd(p)
    g,ord, disclog=_unit_grp_residue_field_mod_n(p,n)
    if v>=2 && n % p==0
      #We know that (1+p)^(p-1) generates the p-Sylow of Z/p^vZ
      #We only need the quotient by p^valuation(n,p)
      R=ResidueRing(FlintZZ, p^v, cached=false)
      gen=R(1+p)^(p-1)
      ord1=gcd(p^(v-1), n)
      aux1=div(p^(v-1),ord1)
      expg=(p-1)*aux1
      z=gen^aux1
      inv=invmod(p-1,ord1)
      function disc_log(x::Int)
        y=R(x)^expg
        if aux1<100
          c=1
          el=z
          while el!=y
            c+=1
            el*=z
          end
          return mod(c*inv, ord1)
        else
          error("Not yet implemented")
        end
      end
      if iszero(g)
        function disc_log2(x::Int)
          return Int[disc_log(x)]
        end
        return [Int(gen.data)], [ord1], disc_log
      else
        g=Int((R(g)^(p^v)).data)
        inv1=invmod(p^v, ord)
        function disc_log1(x::Int)
          return [inv1*disclog(x), disc_log(x)]
        end
      end
      return [g, Int(gen.data)], Int[ord, ord1], disc_log1
    else 
      function disc_log3(x::Int)
        return [disclog(x)]
      end
      return [g], [ord], disc_log3
    end
  else
    # p=2
    # It works differently
    if n %2 !=0 || v==1
      function disclog4(x::Int)
        return Int[]
      end
      return Int[], Int[], disclog4
    end 
    if v==2
      R=ResidueRing(FlintZZ, 4, cached=false)
      function disclog5(x::Int)
        y=R(x)
        if isone(y)
          return 0
        else
          return 1
        end
      end
      return [-1], [2], disclog5
    else 
      R=ResidueRing(FlintZZ, 2^v, cached=false)
      ord=gcd(2^(v-2), n)
      gens=[-1,5]
      exps=divexact(2^(v-2), ord)
      z=5^exps
      function disc_log6(x::Int)
        if x%4 ==1
          y=R(x)^exps
          if ord<100
            c=1
            el=z
            while el!=y
              c+=1
              el*=z
            end
            return [0,c]
          else
            error("Not yet implemented")
          end
        elseif x%4==3
          y=R(-x)^exps
          if ord<100
            c=1
            el=z
            while el!=y
              c+=1
              el*=z
            end
            return [1,c]
          else
            error("Not yet implemented")
          end
        else 
          error("Not coprime")
        end
      end
      return gens, [2,ord], disc_log6
    end
  end


end  

function _unit_grp_residue_field_mod_n(p::Int, n::Int)
  
  m=gcd(p-1,n)
  if m!=1
    R=ResidueRing(FlintZZ, p, cached=false)
    s=factor(m).fac
    lp=Int[Int(q)^Int(valuation(p-1,q)) for q in keys(s)]
    npart=prod(lp)
    lp1=Int[div(npart, Int(q)) for q in keys(s)]
    
    s1=div(p-1, npart)
    
    g=R(1)
    found=true
    while true
      g=rand(R)
      if iszero(g)
        continue
      else
        g=g^s1
      end
      for a in lp1
        if isone(g^a)
          found=false
          break
        end
      end
      if found
        break
      else
        found=true
      end
    end
    
    k=gcd(npart,n)
    inv=Int(invmod(s1,npart))
    quot=divexact(npart, k)
    
    function disc_log(x::Int)
      y=R(x)^(s1*quot)
      if iszero(y)
        error("Not coprime!")
      end
      if isone(y)
        return 0
      end
      if k<100
        c=1
        w=g^quot
        el=w
        while el!=y
          c+=1
          el*=w
        end
        return mod(c*inv,k)
      else
        error("To be implemented!")
      end
    end     
    return (Int(g.data), k, disc_log)::Tuple{Int,Int,Function}

  else
    function disclog1(x::Int)
      return 0
    end
    return (0, 0, disclog1)::Tuple{Int,Int,Function}
  
  end
  
end


unit_group(A::Generic.ResRing{fmpz}) = UnitGroup(A)
unit_group(A::Nemo.NmodRing) = UnitGroup(A)




