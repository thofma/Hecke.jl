@doc raw"""
    is_primitive_root(x::EuclideanRingResidueRingElem{ZZRingElem}, M::ZZRingElem, fM::Dict{ZZRingElem, Int64}) -> Bool

Given $x$ in $Z/MZ$, the factorisation of $M$ (in `fM`), decide if $x$ is primitive.
Intrinsically, only makes sense if the units of $Z/MZ$ are cyclic.
"""
function is_primitive_root(x::EuclideanRingResidueRingElem{ZZRingElem}, M::ZZRingElem, fM::Fac{ZZRingElem})
  for (p, l) in fM
    if x^divexact(M, p) == 1
      return false
    end
  end
  return true
end

function is_primitive_root(x::Nemo.ZZModRingElem, M::ZZRingElem, fM::Fac{ZZRingElem})
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
  we get (from the constant gcd) that either a is coprime to p, hence
  the gcd will be stable for all subsequent k's as well, or
  |G_k| is stable (other gcd) hence will be stable. In either case,
  gcd(|G_(k+l)|, a) = 1 for all l, thus a is a generator
=#

@doc raw"""
    gen_mod_pk(p::ZZRingElem, mod::ZZRingElem=0) ZZRingElem

Find an integer $x$ s.th. $x$ is a primtive root for all powers of the (odd) prime $p$. If `mod` is non zero, it finds a generator for $Z/p^kZ$ modulo `mod` powers only.
"""
function gen_mod_pk(p::ZZRingElem, mod::ZZRingElem=ZZRingElem(0))
  @assert isodd(p)
  @assert is_prime(p)
  gc = gcd(p-1, mod)
  mi = divexact(p-1, gc)
  fp = factor(gc)
  Rp = residue_ring(FlintZZ, p, cached=false)[1]
  Rpp = residue_ring(FlintZZ, p*p, cached=false)[1]

  g = ZZRingElem(2)
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

mutable struct MapUnitGroupModM{T} <: Map{FinGenAbGroup, T, HeckeMap, MapUnitGroupModM}
 header::Hecke.MapHeader{FinGenAbGroup, T}

  function MapUnitGroupModM{T}(G::FinGenAbGroup, R::T, dexp::Function, dlog::Function) where {T}
    r = new{T}()
    r.header = Hecke.MapHeader(G, R, dexp, dlog)
    return r
  end
end

#TO BE FIXED. If mod is non-zero, it is wrong.
@doc raw"""
    UnitGroup(R::EuclideanRingResidueRing{ZZRingElem}) -> FinGenAbGroup, Map

The unit group of $R = Z/nZ$ together with the appropriate map.
"""
function UnitGroup(R::Nemo.ZZModRing, mod::ZZRingElem=ZZRingElem(0))
  m = modulus(R)
  fm = factor(m).fac

  r = Array{ZZRingElem}(undef, 0)
  g = Array{ZZRingElem}(undef, 0)
  mi = Array{ZZRingElem}(undef, 0)
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
        gg = ZZRingElem(-1)
        if m == pk
          push!(g, gg)
        else
          push!(g, crt(ZZRingElem(-1), pk, ZZRingElem(1), divexact(m, pk)))
        end
      else
        mpk = divexact(m, pk)
        push!(r, 2)
        push!(r, gcd(p^(k-2), mod))  # cannot be trivial since mod is even
        push!(mi, ZZRingElem(4))
        push!(mi, pk)
        if mpk == 1
          push!(g, ZZRingElem(-1))
          push!(g, ZZRingElem(5))
        else
          push!(g, crt(ZZRingElem(-1), pk, ZZRingElem(1), mpk))
          push!(g, crt(ZZRingElem(5), pk, ZZRingElem(1), mpk))
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
      gg = powermod(gg, divexact(p-1, gcd(p-1, mod)), m)
      if mpk == 1
        push!(g, gg)
      else
        push!(g, crt(gg, pk, ZZRingElem(1), mpk))
      end
    end
  end

  G = abelian_group(r)
  function dexp(x::FinGenAbGroupElem)
   return prod(Nemo.ZZModRingElem[R(g[i])^x[i] for i=1:ngens(G)])
  end
  function dlog(x::Nemo.ZZModRingElem)
    return G(ZZRingElem[disc_log_mod(g[i], lift(x), mi[i]) for i=1:ngens(G)])
  end
  return G, MapUnitGroupModM{typeof(R)}(G, R, dexp, dlog)
end

function UnitGroup(R::Nemo.zzModRing, mod::ZZRingElem=ZZRingElem(0))

  m = Int(R.n)
  fm = factor(ZZRingElem(m)).fac

  r = Array{ZZRingElem}(undef, 0)
  g = Array{ZZRingElem}(undef, 0)
  mi = Array{ZZRingElem}(undef, 0)
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
        gg = ZZRingElem(-1)
        if m == pk
          push!(g, gg)
        else
          push!(g, crt(ZZRingElem(-1), pk, ZZRingElem(1), divexact(m, pk)))
        end
      else
        mpk = divexact(m, pk)
        push!(r, 2)
        push!(r, gcd(p^(k-2), mod))  # cannot be trivial since mod is even
        push!(mi, ZZRingElem(4))
        push!(mi, pk)
        if mpk == 1
          push!(g, ZZRingElem(-1))
          push!(g, ZZRingElem(5))
        else
          push!(g, crt(ZZRingElem(-1), pk, ZZRingElem(1), mpk))
          push!(g, crt(ZZRingElem(5), pk, ZZRingElem(1), mpk))
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
      gg = powermod(gg, divexact(p-1, gcd(p-1, mod)), ZZRingElem(m))
      if mpk == 1
        push!(g, gg)
      else
        push!(g, crt(gg, pk, ZZRingElem(1), mpk))
      end
    end
  end

  G = abelian_group(r)
  function dexp(x::FinGenAbGroupElem)
    return prod([R(g[i])^x[i] for i=1:ngens(G)])
  end
  function dlog(x::zzModRingElem)
    return G([disc_log_mod(g[i], lift(x), mi[i]) for i=1:ngens(G)])
  end
  return G, MapUnitGroupModM{typeof(R)}(G, R, dexp, dlog)
end

@doc raw"""
    solvemod(a::ZZRingElem, b::ZZRingElem, M::ZZRingElem)

Finds $x$ s.th. $ax == b mod M$.
"""
function solvemod(a::ZZRingElem, b::ZZRingElem, M::ZZRingElem)
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

#solves a^x = b (mod M) for M a prime power
@doc raw"""
    disc_log_mod(a::ZZRingElem, b::ZZRingElem, M::ZZRingElem)

Computes $g$ s.th. $a^g == b mod M$. $M$ has to be a power of an odd prime
and $a$ a generator for the multiplicative group mod $M$.
"""
function disc_log_mod(a::ZZRingElem, b::ZZRingElem, M::ZZRingElem)
  fM = factor(M).fac
  @assert length(keys(fM)) == 1
  p = first(keys(fM))
  if p==2
    if (a+1) % 4 == 0
      if b%4 == 3
        return ZZRingElem(1)
      else
        return ZZRingElem(0)
      end
    elseif a % M ==5
      if b%4 == 3
        b = -b
      end
      g = ZZRingElem(0)
      if (b-5) % 8 == 0
        g += 1
        b = b* invmod(a, M) % M
      end
      @assert (b-1) % 8 == 0
      @assert (a^2-1) % 8 == 0
      if fM[p] > 3
        F = PadicField(p, fM[p], cached = false)
        g += 2*lift(divexact(log(F(b)), log(F(a^2))))
      end
      return g
    else
      error("illegal generator mod 2^$(fM[p])")
    end
  end

  ## we could do the odd priems case using the same p-adic
  #  log approach...

  @assert isodd(p)

  Fp = GF(p, cached=false)
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

  A = powermod(a, p-1, M)
  B = b*powermod(a, -g, M) %M
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
#    println(valuation(b*powermod(a, -g, M)-1, p))
    B = B*powermod(A, -yi, M) % M
    A = powermod(a, (p-1)*divexact(pim, p), M)
  end
  return g
end

#TODO: a version that caches the baby-steps between calls
@doc raw"""
    disc_log_bs_gs{T}(a::T, b::T, o::ZZRingElem)

Tries to find $g$ s.th. $a^g == b$ under the assumption that $g \leq o$.
Uses Baby-Step-Giant-Step, requires $a$ to be invertible.
"""
function disc_log_bs_gs(a::T, b::T, o::Integer) where {T <: RingElem}
  return disc_log_bs_gs(a, b, ZZRingElem(o))
end

function disc_log_bs_gs(a::T, b::T, o::ZZRingElem) where {T <: RingElem}
  b==1 && return ZZRingElem(0)
  b==a && return ZZRingElem(1)
  @assert parent(a) === parent(b)
  if o < 100 #TODO: benchmark
    ai = inv(a)
    for g=1:Int(o)
      b *= ai
      b==1 && return ZZRingElem(g)
    end
    throw("disc_log failed")
  end
  r = isqrt(o) + 1
  baby = Dict{typeof(a), Int}()
  baby[parent(a)(1)] = (0)
  baby[a] = 1
  ba = a
  for i=2:r-1
    ba *= a
    baby[ba] = i
    ba == b && return ZZRingElem(i)
  end
  giant = ba*a
  @assert giant == a^r
  b == giant && return ZZRingElem(r)
  giant = inv(giant)
  g = ZZRingElem(0)
  for i=1:r+1
    b *= giant
    g += r
    if haskey(baby, b)
      return ZZRingElem(baby[b]+g)
    end
  end
  throw("disc_log failed")
end

@doc raw"""
    disc_log_ph(a::T, b::T, o::ZZRingElem, r::Int)

Tries to find $g$ s.th. $a^g == b$ under the assumption that $ord(a) | o^r$
Uses Pohlig-Hellmann and Baby-Step-Giant-Step for the size($o$) steps.
Requires $a$ to be invertible.
"""
function disc_log_ph(a::T, b::T, o::ZZRingElem, r::Int) where {T <: RingElem}
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


function unit_group_mod(R::Nemo.zzModRing, n::Int)

  fm = factor(ZZRingElem(R.n))
  gens = Vector{Int}(undef, 0)
  structt = Int[]
  disclogs = Function[]

  for (p, v) in fm
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

  G = abelian_group(structt)
  local disclog
  let G = G, disclogs = disclogs
    function disclog(x::zzModRingElem)
      res = Vector{Int}(undef, ngens(G))
      ind = 1
      for i = 1:length(disclogs)
        res1 = disclogs[i](Int(x.data))
        for j = 1:length(res1)
          res[ind] = res1[j]
          ind += 1
        end
      end
      return G(res)
    end
  end

  local expon
  let G = G, R = R
    function expon(a::FinGenAbGroupElem)
      res = one(R)
      for i=1:ngens(G)
        if !iszero(a[i])
          res *= R(gens[i])^Int(a[i])
        end
      end
      return res
    end
  end

  return G, MapUnitGroupModM{typeof(R)}(G, R, expon, disclog)

end


function _unit_pk_mod_n(p::Int, v::Int, n::Int)

  #First, multiplicative group mod p
  if isodd(p)
    g, ord, disclog = _unit_grp_residue_field_mod_n(p,n)
    if v>=2 && n % p==0
      #We know that (1+p)^(p-1) generates the p-Sylow of Z/p^vZ
      #We only need the quotient by p^valuation(n,p)
      R = residue_ring(FlintZZ, p^v, cached=false)[1]
      gen = R(1+p)^(p-1)
      ord1 = gcd(p^(v-1), n)
      aux1 = div(p^(v-1), ord1)
      expg = (p-1)*aux1
      z = gen^aux1
      inv = invmod(p-1,ord1)
      local disc_log
      let R = R, aux1 = aux1, z = z, inv = inv, ord1 = ord1
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
            return mod(inv*disc_log_bs_gs(z, y, ZZRingElem(aux1)), ord1)
          end
        end
      end
      if iszero(g)
        local disclog2
        let disc_log = disc_log
          function disc_log2(x::Int)
            return Int[disc_log(x)]
          end
        end
        return Int[Int(gen.data)], Int[ord1], disc_log
      else
        g = Int((R(g)^(p^v)).data)
        inv1 = invmod(p^v, ord)
        local disc_log1
        let inv1 = inv1, disclog = disclog, disc_log = disc_log
          function disc_log1(x::Int)
            return Int[inv1*disclog(x), disc_log(x)]
          end
        end
      end
      return [g, Int(gen.data)], Int[ord, ord1], disc_log1
    else
      local disc_log3
      let disclog = disclog
        function disc_log3(x::Int)
          return Int[disclog(x)]
        end
      end
      return Int[g], Int[ord], disc_log3
    end
  else
    # p=2
    # It works differently
    if n % 2 != 0 || v == 1
      function disclog4(x::Int)
        return Int[]
      end
      return Int[], Int[], disclog4
    end
    if v==2
      R = residue_ring(FlintZZ, 4, cached=false)[1]
      local disclog5
      let R = R
        function disclog5(x::Int)
          y = R(x)
          if isone(y)
            return Int[0]
          else
            return Int[1]
          end
        end
      end
      return Int[-1], Int[2], disclog5
    else
      R = residue_ring(FlintZZ, 2^v, cached=false)[1]
      ord = gcd(2^(v-2), n)
      gens = Int[-1,5]
      exps = divexact(2^(v-2), ord)
      z = R(5)^exps
      local disc_log6
      let R = R, exps = exps, ord = ord, z = z
      function disc_log6(x::Int)
        if x % 4 ==1
          y=R(x)^exps
          if ord<100
            c=1
            el=z
            while el!=y
              c+=1
              el*=z
            end
            return Int[0, c]
          else
            return Int[0, disc_log_bs_gs(z, y, ord)]
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
            return Int[1,c]
          else
            return Int[1, disc_log_bs_gs(z, y, ord)]
          end
        else
          error("Not coprime")
        end
      end
      end
      return gens, Int[2,ord], disc_log6
    end
  end


end

function _unit_grp_residue_field_mod_n(p::Int, n::Int)

  npart = ppio(p-1, n)[1]
  if isone(npart)
    function disclog1(x::Int)
      return 0
    end
    return 1, 1, disclog1
  end
  R = Native.GF(p, cached = false)
  s = factor(npart)
  lp1 = Int[div(npart, Int(q)) for (q, v) in s]
  s1 = div(p-1, npart)

  g = one(R)
  found = true
  while found
    g = rand(R)
    iszero(g) && continue
    g = g^s1
    for a in lp1
      if isone(g^a)
        found = false
        break
      end
    end
    found = !found
  end

  k = gcd(npart, n)
  inv = invmod(s1, npart)
  quot = divexact(npart, k)
  w = g^quot

  local disc_log
  let R = R, s1 = s1, quot = quot, w = w, inv = inv, k = k, npart = npart
    function disc_log(x::Int)
      y = R(x)^(s1*quot)
      iszero(y) && error("Not coprime!")
      isone(y) && return 0
      if k < 100
        c = 1
        el = w
        while el != y
          c += 1
          el *= w
        end
        return mod(c*inv,k)
      else
        return mod(inv*disc_log_bs_gs(w, y, npart), k)
      end
     end
  end
  return Int(g.data), k, disc_log

end

unit_group(A::Nemo.ZZModRing) = UnitGroup(A)
unit_group(A::Nemo.zzModRing) = UnitGroup(A)
