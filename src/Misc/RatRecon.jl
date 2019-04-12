export rational_reconstruction, farey_lift, berlekamp_massey

## given some r/s = a mod b and deg(r) = n, deg(s) <= m find r,s
## a and b better be polynomials in the same poly ring.
## seems to work for Q (Qx) and Fp experimentally
#
# possibly should be rewritten to use an asymptotically (and practically)
# faster algorithm. For Q possibly using CRT and fast Fp techniques
# Algorithm copies from the bad-primes paper


@doc Markdown.doc"""
    rational_reconstruction(a::PolyElem{S}, b::PolyElem{S}, n::Int, m::Int)

 Returns true and x, y s.th. ay = x mod b and degree(x) <= n, degree(y) <= m
   or false (and garbage) if this is not possible.
"""
function rational_reconstruction(a::PolyElem{S}, b::PolyElem{S}, n::Int, m::Int) where S
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

@doc Markdown.doc"""
  rational_reconstruction{S}(a::PolyElem{S}, b::PolyElem{S})

 Returns true and x/y s.th. ay = x mod b and degree(x), degree(y) <= degree(b)/2
   or false (and garbage) if this is not possible. Shortcut to the more general function.
"""
function rational_reconstruction(a::PolyElem{T}, b::PolyElem{T}) where T
  return rational_reconstruction_subres(a, b)
end
function rational_reconstruction(a::fmpq_poly, b::fmpq_poly)
  return rational_reconstruction_mod(a, b)
end


#Note: this is not the best (fastest) algorithm, not the most general
#      signature, not the best (fastest) interface, ....
#However: for now it works.

@doc Markdown.doc"""
    rational_reconstruction(a::fmpz, b::fmpz)
    rational_reconstruction(a::Integer, b::Integer)

Tries to solve ay=x mod b for x,y < sqrt(M/2). If possible, returns
  (true, x, y) or (false, garbage) if not possible.
"""
function rational_reconstruction(a::fmpz, b::fmpz)
  res = fmpq()
  a = mod(a, b)
  fl = ccall((:fmpq_reconstruct_fmpz, :libflint), Int, (Ref{fmpq}, Ref{fmpz}, Ref{fmpz}), res, a, b)
  return fl!=0, numerator(res), denominator(res)
end

function rational_reconstruction(a::Integer, b::Integer)
  return rational_reconstruction(fmpz(a), fmpz(b))
end

@doc Markdown.doc"""
    rational_reconstruction(a::fmpz, b::fmpz, N::fmpz, D::fmpz) -> Bool, fmpz, fmpz
Given $a$ modulo $b$ and $N>0$, $D>0$ such that $2ND<b$, find $|x|\le N$, $0<y\le D$
satisfying $x/y \equiv a \bmod b$ or $a \equiv ya \bmod b$.
"""
function rational_reconstruction(a::fmpz, b::fmpz, N::fmpz, D::fmpz)
  res = fmpq()
  a = mod(a, b)
  fl = ccall((:fmpq_reconstruct_fmpz_2, :libflint), Int, (Ref{fmpq}, Ref{fmpz}, Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), res, a, b, N, D)
  return fl!=0, numerator(res), denominator(res)
end

#Note: the vector version might be useful - or the mult be previous den version
#Note: missing reconstruction modulo a true ideal. W/o denominators

@doc Markdown.doc"""
    rational_reconstruction(a::nf_elem, b::fmpz)

Applies the rational_reconstruction function to each coefficient.
"""
function rational_reconstruction(a::nf_elem, b::fmpz)
  K= parent(a)
  Qx = parent(K.pol)
  res = Qx(0)
  for i=0:degree(K)-1
    c = coeff(a, i)
    if iszero(c)
      continue
    end
    @assert denominator(c) == 1
    fl, x, y = rational_reconstruction(numerator(c), b)
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
# Idea of using the same agorithm due to E. Thome
#

function berlekamp_massey_recon(a::Array{T, 1}) where T
  Rx,x = PolynomialRing(parent(a[1]), cached=false)
  f = Rx(a)
  xn= x^length(a)

  fl, n, d = rational_reconstruction(f, xn)
  if fl
    return true, d*(inv(trailing_coefficient(d)))
  else
    return false, Rx(0)
  end
end

###############################################################################
#                 univariate farey lift Michael Monagan algorithm             #
# from Dereje
###############################################################################

function rational_reconstruction_subres(g::PolyElem{T}, f::PolyElem{T}, bnd::Int = -1) where T
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

    N1 = R_2(inv(lead(g))); r2 = g*N1 
    r1 = f* R_2(inv(lead(f))); t1 = t_1;
    t2 = N1; i = 0
    l_rt = []
    deg_f = degree(f)
    while r2!=0
        i += 1 
        q1,r = divrem(r1,r2); r3=r2
        if r==0
           N1 = R_2(1)
        else
           N1 = R_2(inv(lead(r)))
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
         if gcd(l_rt[1], l_rt[2])!=1
              return false, l_rt[1], l_rt[2]
         else
              return  true, l_rt[1], l_rt[2] 
         end
    else
        if gcd(r_m, t_m) == 1
           return true, r_m, t_m
        else
           return false, r_m, t_m
        end
    end
end
###############################################################################
#                 modular univariate farey lift                               #
###############################################################################

function rational_reconstruction_mod(g::fmpq_poly, f::fmpq_poly)
  p = next_prime(fmpz(p_start))
  n, p = _inner_modp_results(g, f, p)  # mainly used to find the correct
                                       # bound n and a starting p 
  kp = 10  
  L =[]
  pp = FlintZZ(1)
  j = 0
  while true
    kp = 2*kp
    L = _modp_results(g,f,p,kp, n)
    p = L[4]
    if j==0
       N = L[1]; D = L[2]; pp = L[3]
    else
       N,_ = induce_crt(N, pp, L[1], L[3])
       D,pp = induce_crt(D, pp, L[2], L[3])
    end
    j=1
    fl, nu_rat_f = induce_rational_reconstruction(N, FlintZZ(pp))
    if fl
      fl, de_rat_f = induce_rational_reconstruction(D, FlintZZ(pp))
      if fl
        if (de_rat_f*g) % f == nu_rat_f
          return true,  nu_rat_f, de_rat_f
        end
      end
    end
    p = next_prime(p)
  end
end

################################################################################

function _modp_results(g::fmpq_poly,f::fmpq_poly, p::fmpz, M::Int, n::Int)
   l1 = nmod_poly[]; l2 = nmod_poly[];l3 = fmpz[]
   L = listprimes([f,g], p, M)
   for j in 1:length(L)
     Rp, t = PolynomialRing(ResidueRing(FlintZZ, L[j], cached=false), cached=false)
     gp = Rp(g)
     fp = Rp(f)
     fl, nu_p, de_p = rational_reconstruction_subres(gp, fp, n)
     if fl 
        ut = Rp(inv(lead(de_p)))
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

function _inner_modp_results(g::fmpq_poly,f::fmpq_poly, p::fmpz)
   while true
     if testPrime_jl(f,p) == true && testPrime_jl(g,p) == true
         Rp, t = PolynomialRing(ResidueRing(FlintZZ, p, cached=false), cached=false)
         gp = Rp(g)
         fp = Rp(f)
         fl, nu_p, de_p = rational_reconstruction_subres(gp, fp)
         if fl
             return degree(nu_p), p 
         end
     end
     p = next_prime(p)
   end
end

###############################################################################

function berlekamp_massey(L::Array{T, 1}) where T
  return berlekamp_massey_naive(L)
end
function berlekamp_massey(L::Array{fmpq, 1})
  return berlekamp_massey_mod(L)
end

################################################################################
#                         Berlekamp Massey Algorithm                           #
################################################################################
function berlekamp_massey_naive(L::Array{T, 1}) where T
     R_s = parent(L[1])
     lg = length(L)
     L = [R_s(L[lg-i]) for i in 0:lg-1]
     Ry, Y = PolynomialRing(R_s, "Y", cached=false)
     g = Ry(L)
     if iszero(g)
       return g
     end
     f = Y^lg
     N = R_s(inv(lead(g))); g1 = g*N
     v0 = Ry(); v1 = Ry(1)
     while lg <= 2*degree(g1)
       q,r = divrem(f,g1)
       if r==0
          N = R_s(1)
       else
          N = R_s(inv(lead(r)))
       end
       v = (v0-q*v1)*N
       v0 = v1; v1 = v; f = g1; g1= r*N
     end
     return divexact(v1, lead(v1))
end

###############################################################################
#                 modular Berlekamp algorithm                                 #
###############################################################################

function berlekamp_massey_mod(L::Array{fmpq, 1})
  Rf = parent(L[1])
#  L = [Rf(L[i]) for i in 1:length(L)]
  Rc, Y = PolynomialRing(Rf, "Y", cached=false)
  f = Rc(L)
  if iszero(f)
    return f
  end
  p = next_prime(fmpz(p_start))
  kp = 10  
  pp = FlintZZ(1)
  j = 0
  while true
    kp = 2*kp
    L = _modpResults(f,p,kp)
    p = L[3]
    if j==0
       N = L[1]; pp = L[2]
    else
       N, pp = induce_crt(N, pp, L[1], L[2])
    end
    j=1
    fl, nu_rat_f = induce_rational_reconstruction(N, FlintZZ(pp))
    if fl
      if length(factor(nu_rat_f)) == degree(nu_rat_f) #TODO write and use roots
          return true,  nu_rat_f
      end
    end
    p = next_prime(p)
  end
end

################################################################################

function _modpResults(f, p::fmpz, M::Int)
   Rc = f.parent
   l1 = nmod_poly[]; l3 = fmpz[]
   Np = listprimes([f], p, M)
   Zx, Y = PolynomialRing(FlintZZ, "Y", cached=false)
   L2 = []
   for j in 1:length(Np)
     RNp = ResidueRing(FlintZZ, Np[j], cached=false)
     Rp, t = PolynomialRing(RNp, "t", cached=false)
     fp = Rp(f)
     L1 = []
     for i in 0:degree(fp)
        push!(L1, coeff(fp, i))
     end
     ff = berlekamp_massey_naive(L1)
     push!(l1, ff)
     push!(l3, Np[j])
   end
   c = crt_env(l3)
   nu = induce_crt(l1, c)
   return nu, c.pr[end], Np[end]
end

################################################################################

function testPrime_jl(f::fmpq_poly, p::fmpz)
    # BAD!!! missing: num_coeff(f, i)
    nd = denominator(f)
    fg = nd*f
    return !(divides(nd, p)[1]) || !(divides(numerator(lead(fg)), p)[1])
end

################################################################################

function listprimes(f::Array{fmpq_poly, 1}, p::fmpz, M::Int)
   # static 
   i=0; L = []
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

function induce_crt(L::Array{nmod_poly, 1}, c::crt_env{fmpz})
  Zx, x = FlintZZ["x"]
  res = Zx()
  m = maximum(degree(x) for x = L)

  for i=0:m
    setcoeff!(res, i, crt([lift(coeff(x, i)) for x =L], c))
  end
  return res
end


