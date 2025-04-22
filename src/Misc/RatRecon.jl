## given some r/s = a mod b and deg(r) = n, deg(s) <= m find r,s
## a and b better be polynomials in the same poly ring.
## seems to work for Q (Qx) and Fp experimentally
#
# possibly should be rewritten to use an asymptotically (and practically)
# faster algorithm. For Q possibly using CRT and fast Fp techniques
# Algorithm copies from the bad-primes paper


@doc raw"""
    rational_reconstruction(a::PolyRingElem{S}, b::PolyRingElem{S}, n::Int, m::Int)

 Returns `true` and $x, y$ s.th. $ay = x mod b$ and $degree(x) <= n$, $degree(y) <= m$
   or `false` (and garbage) if this is not possible.
"""
function rational_reconstruction(a::PolyRingElem{S}, b::PolyRingElem{S}, n::Int, m::Int) where S
  R = a.parent
  if degree(a) <= n return true, a, R(1); end

  M = zero_matrix(R, 2, 2)
  M[1,1] = b
  M[2,1] = a
  M[2,2] = R(1)

  T = zero_matrix(R, 2, 2)
  T[1,2] = R(1)
  T[2,1] = R(1)
  while degree(M[2,1]) > n
    q, r = divrem(M[1,1], M[2,1])
    T[2,2] = -q
    M = T*M
  end
  if degree(M[2,2]) <= m
    return true, M[2,1], M[2,2]
  end

  return false, M[2,1], M[2,2]
end

@doc raw"""
    rational_reconstruction{S}(a::PolyRingElem{S}, b::PolyRingElem{S})

 Returns `true` and $x/y$ s.th. $ay = x mod b$ and $degree(x), degree(y) <= degree(b)/2$
   or `false` (and garbage) if this is not possible. Shortcut to the more general function.
"""
function rational_reconstruction(a::PolyRingElem{T}, b::PolyRingElem{T}; error_tolerant::Bool = false, ErrorTolerant::Bool = false) where T
  return rational_reconstruction_subres(a, b, error_tolerant = error_tolerant || ErrorTolerant)
end

function rational_reconstruction(a::QQPolyRingElem, b::QQPolyRingElem; error_tolerant::Bool = false, ErrorTolerant::Bool = false)
  return rational_reconstruction_mod(a, b, error_tolerant = error_tolerant || ErrorTolerant)
end


function rational_reconstruction(a::ZZRingElem, b::ZZRingElem; error_tolerant::Bool = false, ErrorTolerant::Bool = false, kw...)
  return Nemo._rational_reconstruction(a, b; error_tolerant = error_tolerant || ErrorTolerant , kw...)
end

function rational_reconstruction(a::Integer, b::Integer; error_tolerant::Bool = false, kw...)
  return rational_reconstruction(ZZRingElem(a), ZZRingElem(b), error_tolerant, kw...)
end

function rational_reconstruction(a::ZZRingElem, b::ZZRingElem, N::ZZRingElem, D::ZZRingElem)
  return Nemo._rational_reconstruction(a, b, N, D)
end

#Note: the vector version might be useful - or the mult by previous den version
#Note: missing reconstruction modulo a true ideal. W/o denominators

@doc raw"""
    rational_reconstruction(a::AbsSimpleNumFieldElem, b::ZZRingElem)

Applies the `rational_reconstruction` function to each coefficient.
"""
function rational_reconstruction(a::AbsSimpleNumFieldElem, b::ZZRingElem; error_tolerant::Bool = false)
  K= parent(a)
  Qx = parent(K.pol)
  res = Qx(0)
  for i=0:degree(K)-1
    c = coeff(a, i)
    if iszero(c)
      continue
    end
    @assert denominator(c) == 1
    fl, x, y = rational_reconstruction(numerator(c), b, error_tolerant = error_tolerant)
    if !fl
      return false, K(res)
    end
    setcoeff!(res, i, x//y)
  end
  return true, K(res)
end

# to appease the Singular crowd...
farey_lift = rational_reconstruction

# in at least 2 examples produces the same result as Magma
# can do experiments to see if dedicated Berlekamp Massey would be
# faster as well as experiments if Berlekamp Massey yields faster
# rational_reconstruction as well.
# Idea of using the same algorithm due to E. Thome
#

function berlekamp_massey_recon(a::Vector{T}; ErrorTolerant::Bool = false, error_tolerant::Bool = false, parent = polynomial_ring(parent(a[1]), "x", cached = false)[1]) where T
  Rx = parent
  f = Rx(a)
  x = gen(Rx)
  xn= x^length(a)

  fl, n, d = rational_reconstruction(f, xn, error_tolerant = error_tolerant || ErrorTolerant)
  if fl
    d = reverse(d)
    return true, d*(inv(leading_coefficient(d)))
  else
    return false, Rx(0)
  end
end

###############################################################################
#                 univariate farey lift Michael Monagan algorithm             #
# from Dereje
###############################################################################

function rational_reconstruction_subres(g::PolyRingElem{T}, f::PolyRingElem{T}, bnd::Int = -1; error_tolerant::Bool = false) where T
    # the denominator is normalized
    R_2 = g.parent
    r_1 = R_2(1); t_1 = R_2(0)
    r_m = r_1;t_m = r_1
    q1 = t_1; q_m = r_1

    if g==t_1
       return true, t_1,r_1
    end

    if 2*degree(g) < degree(f)
        return true, g, r_1
    end

    N1 = R_2(inv(leading_coefficient(g))); r2 = g*N1
    r1 = f* R_2(inv(leading_coefficient(f))); t1 = t_1;
    t2 = N1; i = 0
    l_rt = []
    deg_f = degree(f)
    while r2!=0
        i += 1
        q1,r = divrem(r1,r2); r3=r2
        if r==0
           N1 = R_2(1)
        else
           N1 = R_2(inv(leading_coefficient(r)))
        end
        r2=r*N1; r1=r3
        r3=t2; t2=(t1-q1*t2)*N1; t1=r3

        if bnd>-1 && degree(r1) == bnd
          return true, r1, t1
        end

        if i == div(deg_f,2)
           l_rt = [r1, t1]
        end
        if degree(q1) > degree(q_m)
           (q_m, r_m, t_m) = (q1,r1,t1)
        end
    end

    if(degree(q_m)==1)
       g = gcd(l_rt[1], l_rt[2])
       if error_tolerant
          if 2*degree(g) + degree(l_rt[1]) + degree(l_rt[2]) >= degree(f) -1
            return false, l_rt[1], l_rt[2]
          else
            return true, divexact(l_rt[1], g), divexact(l_rt[2], g)
          end
       elseif !isone(g)
          return false, l_rt[1], l_rt[2]
       else
          return  true, l_rt[1], l_rt[2]
       end
    else
        g = gcd(r_m, t_m)
        if error_tolerant
           if 2*degree(g) + degree(r_m) + degree(t_m) >= degree(f) -1
              return false, r_m, t_m
           else
              return true, divexact(r_m, g), divexact(t_m, g)
           end
        elseif gcd(r_m, t_m) == 1
           return true, r_m, t_m
        else
           return false, r_m, t_m
        end
    end
end
###############################################################################
#                 modular univariate farey lift                               #
###############################################################################

function rational_reconstruction_mod(g::QQPolyRingElem, f::QQPolyRingElem, bnd::Int = -1; error_tolerant ::Bool = false)
  p = next_prime(ZZRingElem(p_start))
  local n, p
  try
    n, p = _inner_modp_results(g, f, p, bnd, error_tolerant)  # mainly used to find the correct
  catch e
    if e == ErrorException("Reconstruction probably not possible. illegal inputs")
      if error_tolerant
        return false, g, f
      end
      rethrow(e)
    end
  end
                                       # bound n and a starting p
  kp = 10
  L =[]
  pp = ZZ(1)
  j = 0
  local N, D
  while true
    kp = 2*kp
    L = _modp_results(g,f,p,kp, n, error_tolerant)
    p = L[4]
    if j==0
       N = L[1]; D = L[2]; pp = L[3]
       j=1
    else
       N,_ = induce_crt(N, pp, L[1], L[3])
       D,pp = induce_crt(D, pp, L[2], L[3])
    end
    fl, nu_rat_f = induce_rational_reconstruction(N, ZZ(pp), parent = parent(g))
    if fl
      fl, de_rat_f = induce_rational_reconstruction(D, ZZ(pp), parent = parent(g))
      if fl
        t = de_rat_f *g - nu_rat_f
        if error_tolerant
           gc = divexact(f, gcd(t, f))
           if iszero((t*gc) % f)
              return true, nu_rat_f, de_rat_f
           end
        elseif iszero(t % f)
           return true,  nu_rat_f, de_rat_f
        end
      end
    end
    p = next_prime(p)
  end
end

################################################################################

function _modp_results(g::QQPolyRingElem,f::QQPolyRingElem, p::ZZRingElem, M::Int, n::Int, error_tolerant::Bool)
   l1 = fpPolyRingElem[]; l2 = fpPolyRingElem[];l3 = ZZRingElem[]
   L = listprimes([f,g], p, M)
   for j in 1:length(L)
     Rp, t = polynomial_ring(Native.GF(Int(L[j]), cached=false), cached=false)
     gp = Rp(g)
     fp = Rp(f)
     fl, nu_p, de_p = rational_reconstruction_subres(gp, fp, -1, error_tolerant = error_tolerant)
     if fl
        ut = Rp(inv(leading_coefficient(de_p)))
        push!(l1, ut*nu_p)
        push!(l2, ut*de_p)
        push!(l3, L[j])
     end
   end
   c = crt_env(l3)
   nu = induce_crt(l1, c)
   du = induce_crt(l2, c)
   return nu, du, c.pr[end], L[end]
end

function _inner_modp_results(g::QQPolyRingElem,f::QQPolyRingElem, p::ZZRingElem, bnd::Int = -1, error_tolerant::Bool = false)
   np = 0
   while true
     np += 1
     if testPrime_jl(f,p) == true && testPrime_jl(g,p) == true
         Rp, t = polynomial_ring(residue_ring(ZZ, p, cached=false)[1], cached=false)
         gp = Rp(g)
         fp = Rp(f)
         fl, nu_p, de_p = rational_reconstruction_subres(gp, fp, bnd, error_tolerant = error_tolerant)
         if fl
             return degree(nu_p), p
         end
     end
     p = next_prime(p)
     if np > 100
       error("Reconstruction probably not possible. illegal inputs")
     end
   end
end

###############################################################################

function berlekamp_massey(L::Vector{T}; parent = polynomial_ring(parent(L[1]), "x", cached = false)[1]) where T
  return berlekamp_massey_naive(L, parent = parent)
end
function berlekamp_massey(L::Vector{QQFieldElem}; error_tolerant::Bool = false, ErrorTolerant::Bool = false, parent = Globals.Qx)
  if ErrorTolerant || error_tolerant
    return berlekamp_massey_recon(L, error_tolerant = true, parent = parent)
  end
  return berlekamp_massey_mod(L, parent = parent)
end

################################################################################
#                         Berlekamp Massey Algorithm                           #
################################################################################
function berlekamp_massey_naive(L::Vector{T}; parent = polynomial_ring(parent(L[1]), "x", cached = false)[1]) where T
     R_s = Nemo.parent(L[1])
     lg = length(L)
     L = [R_s(L[lg-i]) for i in 0:lg-1]
     Ry = parent
     Y = gen(Ry)
     g = Ry(L)
     if iszero(g)
       return true, g
     end
     f = Y^lg
     N = R_s(inv(leading_coefficient(g))); g1 = g*N
     v0 = Ry(); v1 = Ry(1)
     while lg <= 2*degree(g1)
       q,r = divrem(f,g1)
       if r==0
          N = R_s(1)
       else
          N = R_s(inv(leading_coefficient(r)))
       end
       v = (v0-q*v1)*N
       v0 = v1; v1 = v; f = g1; g1= r*N
     end
     return true, divexact(v1, leading_coefficient(v1))
end

###############################################################################
#                 modular Berlekamp algorithm                                 #
###############################################################################

function berlekamp_massey_mod(L::Vector{QQFieldElem}; parent = Globals.Qx)
  Rf = Nemo.parent(L[1])
#  L = [Rf(L[i]) for i in 1:length(L)]
  Rc = parent
  Y = gen(Rc)
  f = Rc(L)
  if iszero(f)
    return true, f
  end
  p = next_prime(ZZRingElem(p_start))
  kp = 10
  pp = ZZ(1)
  j = 0
  local N
  while true
    kp = 2*kp
    L = _modpResults(f,p,kp)
    p = L[3]
    if j==0
       N = L[1]; pp = L[2]
    else
       N, pp = induce_crt(N, pp, L[1], L[2])
      j=1
    end
    fl, nu_rat_f = induce_rational_reconstruction(N, ZZ(pp), parent = Rc)
    if fl
      return true, nu_rat_f
      #the check for roots is ONLY useful in multivariate interpolation
      #in general, the poly can be anything of course
      if length(factor(nu_rat_f)) == degree(nu_rat_f) #TODO write and use roots
          return true,  nu_rat_f
      end
    end
    p = next_prime(p)
  end
end

################################################################################

function _modpResults(f, p::ZZRingElem, M::Int)
   Rc = f.parent
   l1 = fpPolyRingElem[]; l3 = ZZRingElem[]
   Np = listprimes([f], p, M)
   Zx, Y = polynomial_ring(ZZ, "Y", cached=false)
   for j in 1:length(Np)
     RNp = Native.GF(Int(Np[j]), cached=false)
     Rp, t = polynomial_ring(RNp, "t", cached=false)
     fp = Rp(f)
     if degree(fp) != degree(f)
       continue #bad prime...
     end
     L1 = fpFieldElem[]
     for i in 0:degree(fp)
        push!(L1, coeff(fp, i))
     end
     ff = berlekamp_massey_naive(L1)
     @assert ff[1]
     push!(l1, ff[2])
     push!(l3, Np[j])
   end
   c = crt_env(l3)
   nu = induce_crt(l1, c)
   return nu, c.pr[end], Np[end]
end

################################################################################

function testPrime_jl(f::QQPolyRingElem, p::ZZRingElem)
    # BAD!!! missing: num_coeff(f, i)
    nd = denominator(f)
    fg = nd*f
    return !(divides(nd, p)[1]) || !(divides(numerator(leading_coefficient(fg)), p)[1])
end

################################################################################

function listprimes(f::Vector{QQPolyRingElem}, p::ZZRingElem, M::Int)
   # static
   i=0; L = ZZRingElem[]
   while true
    i += 1
    if all(x-> testPrime_jl(x,p), f)
       push!(L, p)
    end
    if i == M
      return L
    end
    p = next_prime(p)
  end
end

################################################################################

function induce_crt(L::Vector{fpPolyRingElem}, c::crt_env{ZZRingElem}; parent=Globals.Zx)
  res = parent()
  m = maximum(degree(x) for x = L)

  for i=0:m
    setcoeff!(res, i, crt([lift(coeff(x, i)) for x =L], c))
  end
  return res
end
