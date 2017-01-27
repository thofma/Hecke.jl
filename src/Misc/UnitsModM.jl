export UnitGroup, solvemod, gen_mod_pk, 
       disc_log_bs_gs, disc_log_ph, disc_log_mod

function order(x::GenRes{fmpz}, fp::Dict{fmpz, Int64})
  error("missing")
end


@doc """
  is_primitive_root(x::GenRes{fmpz}, M::fmpz, fM::Dict{fmpz, Int64}) -> Bool

>  Given x in Z/MZ, the factorisation of M (in fM), decide if x is primitive.
>  Intrinsically, only makes sense if the units of Z/MZ are cyclic.
""" ->
function is_primitive_root(x::GenRes{fmpz}, M::fmpz, fM::Fac{fmpz})
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
  
@doc """
  gen_mod_pk(p::fmpz, mod::fmpz=0) -> fmpz

>  Find an integer x s.th. x is a primtive root for all powers of the (odd) prime p. If mod is non zero, it finds a generator for Z/p^kZ modulo mod powers only.
""" ->
function gen_mod_pk(p::fmpz, mod::fmpz=fmpz(0))
  @assert isodd(p)
  @assert isprime(p)
  gc = gcd(p-1, mod)
  mi = divexact(p-1, gc)
  fp = factor(gc)
  Rp = ResidueRing(FlintZZ, p)
  Rpp = ResidueRing(FlintZZ, p*p)

  g = fmpz(2)
  if is_primitive_root(Rp(g)^mi, gc, fp)
    if Rpp(g)^gc != 1
      return g
    else
      return g+p
    end
  end

  while true
#    g = rand(3:p-2)
    g += 1
    if is_primitive_root(Rp(g)^mi, gc, fp)
      if Rpp(g)^gc != 1
        return g
      else
        return g+p
      end
    end
  end
end

type MapUnitGroupModM{T} <: Map{T, GenResRing{fmpz}}
  header::Hecke.MapHeader

  function MapUnitGroupModM(G::T, R::GenResRing{fmpz}, dexp::Function, dlog::Function)
    r = new()
    r.header = Hecke.MapHeader(G, R, dexp, dlog)
    return r
  end
end

@doc """
  UnitGroup(R::GenResRing{fmpz}) -> FinGenGrpAb, Map

>  The unit group of R = Z/nZ together with the apropriate map.
""" ->
function UnitGroup(R::GenResRing{fmpz}, mod::fmpz=fmpz(0))
  m = R.modulus
  fm = factor(m)
  
  r = Array(fmpz, 0)
  g = Array(fmpz, 0)
  mi = Array(fmpz, 0)
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
          push(g, gg)
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
  function dexp(x::FinGenGrpAbElem)
    return prod([R(g[i])^x[i] for i=1:ngens(G)])
  end
  function dlog(x::GenRes{fmpz})
    return G([disc_log_mod(g[i], lift(x), mi[i]) for i=1:ngens(G)])
  end
  return G, MapUnitGroupModM{typeof(G)}(G, R, dexp, dlog)
end

@doc """
  solvemod(a::fmpz, b::fmpz, M::fmpz)

>  Finds x s.th. ax == b mod M.
""" ->
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


@doc """
  disc_log_mod(a::fmpz, b::fmpz, M::fmpz)

>  Computes g s.th. a^g == b mod M. M has to be a power of an odd prime
>  and a a generator for the multiplicative group mod M
""" ->
#solves a^x = b (mod M) for M a prime power
function disc_log_mod(a::fmpz, b::fmpz, M::fmpz)
  fM = factor(M)
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

  Fp = ResidueRing(FlintZZ, p)
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

@doc """
  disc_log_bs_gs{T}(a::GenRes{T}, b::GenRes{T}, o::fmpz)

>  Tries to find g s.th. a^g == b under the assumption that g <= o.
>  Uses Baby-Step-Giant-Step
""" ->
function disc_log_bs_gs{T <: Union{PolyElem, fmpz, fq_nmod_poly, fq_poly, nmod_poly}}(a::GenRes{T}, b::GenRes{T}, o::fmpz)
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
    baby = Array{typeof(a), 1}(r)
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


@doc """
  disc_log_ph{T <:PolyElem}(a::Residue{T}, b::Residue{T}, o::fmpz, r::Int)
  disc_log_ph(a::Residue{fmpz}, b::Residue{fmpz}, o::fmpz, r::Int)
  disc_log_ph(a::Residue{fq_nmod_poly}, b::Residue{fq_nmod_poly}, o::fmpz, r::Int)
  disc_log_ph(a::Residue{fq_poly}, b::Residue{fq_poly}, o::fmpz, r::Int)
  disc_log_ph(a::Residue{nmod_poly}, b::Residue{nmod_poly}, o::fmpz, r::Int)

>  Tries to find g s.th. a^g == b under the assumption that ord(a) | o^r
>  Uses Pohlig-Hellmann and Baby-Step-Giant-Step for the size(o) steps.
  """ ->
function disc_log_ph{T <: Union{PolyElem, fmpz, fq_nmod_poly, fq_poly, nmod_poly}}(a::GenRes{T}, b::GenRes{T}, o::fmpz, r::Int)
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


