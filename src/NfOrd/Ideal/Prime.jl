################################################################################
#
#   NfOrd/Ideal/Prime.jl : Prime ideals in orders of absolute number fields
#
# This file is part of Hecke.
#
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
#
#  Copyright (C) 2015, 2016, 2017 Tommy Hofmann
#  Copyright (C) 2015, 2016, 2017 Claus Fieker
#
################################################################################

export PrimeIdealsSet

doc"""
***
    isramified(O::NfOrd, p::Int) -> Bool

> Returns whether the integer $p$ is ramified in $\mathcal O$.
> It is assumed that $p$ is prime.
"""
function isramified(O::NfOrd, p::Union{Int, fmpz})
  @assert ismaximal_known(O) && ismaximal(O)

  return mod(discriminant(O), p) == 0
end

doc"""
***
    degree(P::NfOrdIdl) -> Int
> The inertia degree of the prime-ideal $P$.
"""
function degree(A::NfOrdIdl)
  @assert isprime(A)
  return A.splitting_type[2]
end

doc"""
***
    ramification_index(P::NfOrdIdl) -> Int
> The ramification index of the prime-ideal $P$.
"""
function ramification_index(A::NfOrdIdl)
  @assert isprime(A)
  return A.splitting_type[1]
end

doc"""
***
    splitting_type(P::NfOrdIdl) -> Int, Int
> The ramification index and inertia degree of the prime ideal $P$.
> First value is the ramificatio index, the second the degree of $P$.
"""
function splitting_type(A::NfOrdIdl)
  @assert isprime(A)
  return A.splitting_type
end

################################################################################
#
#  Prime decomposition
#
################################################################################
doc"""
    intersect(f::Map, P::NfOrdIdl) -> NfOrdIdl
> Given a prime ideal $P$ in $K$ and the inclusion map $f:k \to K$ 
> of number fields, find the unique prime $p$ in $k$ below.
"""

function intersect_prime(f::Map, P::NfOrdIdl)
  
  p = minimum(P)
  k = domain(f)
  Ok = maximal_order(k)
  if index(Ok) % p != 0
    return intersect_nonindex(f, P)
  end
  d = degree(P)
  lp = prime_decomposition(Ok, p, d, 1)
  for (Q, v) in lp
    el = Q.gen_two
    if f(K(el)) in P
      return Q
    end
  end
  error("Restriction not found!")

end

function intersect_nonindex(f::Map, P::NfOrdIdl)
  @assert P.is_prime == 1
  #let g be minpoly of k, G minpoly of K and h in Qt the primitive
  #element of k in K (image of gen(k))
  #then
  #  g(h) = 0 mod G
  k = domain(f)
  K = codomain(f)
  G = K.pol
  Qx = parent(G)
  g = k.pol(gen(Qx))
  h = Qx(f(gen(k)))

  Fp, xp = PolynomialRing(ResidueRing(FlintZZ, Int(minimum(P)), cached=false), cached=false)
  gp = factor(Fp(g))
  hp = Fp(h)
  Gp = gcd(Fp(K(P.gen_two)), Fp(G))
  for (f, e) = gp.fac
    if f(hp) % Gp == 0
      Zk = maximal_order(k)
      p = ideal_from_poly(Zk, Int(minimum(P)), f, 1)
      return p
    end
  end
end


doc"""
    prime_decomposition_nonindex(f::Map, p::NfOrdIdl) -> Array{Tuple{NfOrdIdl, Int}, 1}
> Given a map $f: k\to K$ of number fields defined over $\mathbb Q$ and
> a prime ideal in the maximal order of $k$, find all prime ideals in
> the maximal order of $K$ above.
"""
function prime_decomposition_nonindex(f::Map, p::NfOrdIdl)
  @assert p.is_prime == 1
  k = domain(f)
  K = codomain(f)
  ZK = maximal_order(K)
  G = K.pol
  Qx = parent(G)

  Fp, xp = PolynomialRing(ResidueRing(FlintZZ, Int(minimum(p)), cached=false), cached=false)
  Gp = factor(gcd(Fp(f(K(p.gen_two))), Fp(G)))
  res = Tuple{NfOrdIdl, Int}[]
  Zk = maximal_order(k)
  for (f, e) = Gp.fac
    P = ideal_from_poly(ZK, Int(minimum(p)), f, 1)
    push!(res, (P, e))
  end
  return res
end

doc"""
    lift(K::AnticNumberField, f::nmod_poly) -> nf_elem
> Given a polynomial $f$ over a finite field, lift it to an element of the
> number field $K$. The lift if given by the eleemnt represented by the
> canonical lift of $f$ to a polynomial over the integers.
"""
function lift(K::AnticNumberField, f::nmod_poly)
  if degree(f)>=degree(K)
    f = mod(f, parent(f)(K.pol))
  end
  r = K()
  for i=0:f.length-1
    u = ccall((:nmod_poly_get_coeff_ui, :libflint), UInt, (Ptr{nmod_poly}, Int), &f, i)
    _num_setcoeff!(r, i, u)
  end
  return r
end

##TODO: make fmpz-safe!!!!
#return <p, lift(O, fi> in 2-element normal presentation given the data
function ideal_from_poly(O::NfOrd, p::Int, fi::nmod_poly, ei::Int)
  b = lift(nf(O), fi)
  idl = ideal(O, fmpz(p), O(b, false))
  idl.is_prime = 1
  idl.splitting_type = ei, degree(fi)
  idl.norm = FlintZZ(p)^degree(fi)
  idl.minimum = FlintZZ(p)

  # We have to do something to get 2-normal presentation:
  # if ramified or valuation val(b,P) == 1, (p,b)
  # is a P(p)-normal presentation
  # otherwise we need to take p+b
  # I SHOULD CHECK THAT THIS WORKS

  if !((mod(norm(b),(idl.norm)^2) != 0) || (ei > 1))
    idl.gen_two = idl.gen_two + O(p)
  end

  idl.gens_normal = p
  idl.gens_weakly_normal = true

  # Find an "anti-uniformizer" in case P is unramified
  # We don't call it anti-unfiformizer anymore

  #if ideal.splitting_type[1] == 1
  #  t = parent(f)(lift(Zx, divexact(fmodp, fi)))
  #  ideal.anti_uniformizer = O(K(t), false)
  #end

  if idl.splitting_type[2] == degree(O)
    # Prime number is inert, in particular principal
    idl.is_principal = 1
    idl.princ_gen = O(p)
  end
  return idl
end

doc"""
***
    prime_decomposition(O::NfOrd,
                        p::Integer,
                        degree_limit::Int = 0,
                        lower_limit::Int = 0) -> Array{Tuple{NfOrdIdl, Int}, 1}

> Returns an array of tuples $(\mathfrak p_i,e_i)$ such that $p \mathcal O$ is the product of
> the $\mathfrak p_i^{e_i}$ and $\mathfrak p_i \neq \mathfrak p_j$ for $i \neq j$.
>
> If `degree_limit` is a nonzero integer $k > 0$, then only those prime ideals
> $\mathfrak p$ with $\deg(\mathfrak p) \leq k$ will be returned.
> Similarly if `\lower_limit` is a nonzero integer $l > 0$, then only those prime ideals
> $\mathfrak p$ with $l \leq \deg(\mathfrak p)$ will be returned.
> Note that in this case it may happen that $p\mathcal O$ is not the product of the
> $\mathfrak p_i^{e_i}$.
"""
function prime_decomposition(O::NfAbsOrd{S, T}, p::Union{Integer, fmpz}, degree_limit::Int = 0, lower_limit::Int = 0, cached::Bool = true) where {S, T}
  if typeof(p) == fmpz && nbits(p) < 64
    return prime_decomposition(O, Int(p), degree_limit, lower_limit)
  end

  if mod(index(O),fmpz(p)) == 0 || !issimple(nf(O))
    if cached
      if haskey(O.index_div, fmpz(p))
        lp = O.index_div[fmpz(p)]
        z = Tuple{NfAbsOrdIdl{S, T}, Int}[]
        for (Q, e) in lp
          if degree_limit == 0 || degree(Q) <= degree_limit
            push!(z, (Q, e))
          end
        end
        return z
      end
    end
    @assert O.ismaximal ==1 || p in O.primesofmaximality
    lp = prime_decomposition_polygons(O, fmpz(p), degree_limit, lower_limit)
    if degree_limit == 0 && lower_limit == 0
      O.index_div[fmpz(p)] = lp
    end
    return lp
  end
  return prime_dec_nonindex(O, p, degree_limit, lower_limit)
end

function _fac_and_lift(f::fmpz_poly, p, degree_limit, lower_limit)
  Zx = parent(f)
  Zmodpx = PolynomialRing(ResidueRing(FlintZZ, p, cached = false), "y", cached = false)[1]
  fmodp = Zmodpx(f)
  fac = factor(fmodp)
  lifted_fac = Array{Tuple{fmpz_poly, Int}, 1}()
  for (k, v) in fac
    if degree(k) <= degree_limit && degree(k) >= lower_limit
      push!(lifted_fac, (lift(Zx, k), v))
    end
  end
  return lifted_fac
end

function prime_dec_nonindex(O::NfOrd, p::Union{Integer, fmpz}, degree_limit::Int = 0, lower_limit::Int = 0)

  K = nf(O)
  f = K.pol
  R = parent(f)
  Zx, x = PolynomialRing(FlintIntegerRing(),"x")
  Zf = Zx(f)

  if degree_limit == 0
    degree_limit = degree(K)
  end

  fac = _fac_and_lift(Zf, p, degree_limit, lower_limit)

  result = Array{Tuple{ideal_type(O),Int}}(length(fac))

  for k in 1:length(fac)
    fi = fac[k][1]
    ei = fac[k][2]
    #ideal = ideal_from_poly(O, p, fi, ei)
    t = parent(f)(fi)
    b = K(t)
    ideal = NfAbsOrdIdl(O)
    ideal.gen_one = p
    ideal.gen_two = O(b, false)
    ideal.is_prime = 1
    ideal.splitting_type = ei, degree(fi)
    ideal.norm = FlintZZ(p)^degree(fi)
    ideal.minimum = FlintZZ(p)

    # We have to do something to get 2-normal presentation:
    # if ramified or valuation val(b,P) == 1, (p,b)
    # is a P(p)-normal presentation
    # otherwise we need to take p+b
    # I SHOULD CHECK THAT THIS WORKS

    if !((mod(norm(b),(ideal.norm)^2) != 0) || (ei > 1))
      ideal.gen_two = ideal.gen_two + O(p)
    end

    ideal.gens_normal = p
    ideal.gens_weakly_normal = true

    # Find an "anti-uniformizer" in case P is unramified
    # We don't call it anti-unfiformizer anymore

    #if ideal.splitting_type[1] == 1
    #  t = parent(f)(lift(Zx, divexact(fmodp, fi)))
    #  ideal.anti_uniformizer = O(K(t), false)
    #end

    if length(fac) == 1 && ideal.splitting_type[2] == degree(f)
      # Prime number is inert, in particular principal
      ideal.is_principal = 1
      ideal.princ_gen = O(p)
    end
    result[k] =  (ideal, ei)
    k += 1
  end
  return result
end

function uniformizer(P::NfOrdIdl)
  p = minimum(P)
  if P.gens_normal == p
    return P.gen_two
  else
    if p > 250
      r = 500  # should still have enough elements...
    else
      r = Int(div(p, 2))
    end
    z = rand(P, r)
    while true     
      if !iszero(z) && valuation(z, P) == 1
        break
      end
      z = rand(P, r)
    end
    return z
  end
end

function _lift(T::Array{Generic.Res{fmpz}, 1})
  return [ z.data for z in T ]
end

function _lift(T::Array{Nemo.nmod, 1})
  return [ fmpz(z.data) for z in T ]
end

# Belabas p. 40
function anti_uniformizer(P::NfOrdIdl)
  if isdefined(P, :anti_uniformizer)
    return P.anti_uniformizer
  else
    p = minimum(P)
    M = representation_matrix(uniformizer(P))
    Mp = MatrixSpace(ResidueRing(FlintZZ, p, cached=false), rows(M), cols(M), false)(M)
    K = kernel(Mp)
    @assert length(K) > 0
    P.anti_uniformizer = elem_in_nf(order(P)(_lift(K[1])))//p
    return P.anti_uniformizer
  end
end

function prime_decomposition_type(O::NfOrd, p::Integer)
  if (mod(discriminant(O), p)) != 0 && (mod(fmpz(index(O)), p) != 0)
    K = nf(O)
    f = K.pol
    R = parent(f)
    Zx, x = PolynomialRing(FlintZZ,"x", cached = false)
    Zf = Zx(f)
    fmodp = PolynomialRing(ResidueRing(FlintZZ, p, cached = false), "y", cached = false)[1](Zf)
    fac = factor_shape(fmodp)
    g = sum([ x for x in values(fac)])
    res = Array{Tuple{Int, Int}}(g)
    k = 1
    for (fi, ei) in fac
      for j in 1:ei
        res[k] = (fi, 1)
        k = k + 1
      end
    end
  else
    @assert O.ismaximal ==1 || p in O.primesofmaximality
    return decomposition_type_polygon(O, fmpz(p))
  end
  return res
end

doc"""
***
    prime_ideals_up_to(O::NfOrd,
                       B::Int;
                       degree_limit::Int = 0) -> Array{NfOrdIdl, 1}

> Computes the prime ideals $\mathcal O$ with norm up to $B$.
>
> If `degree_limit` is a nonzero integer $k$, then prime ideals $\mathfrak p$
> with $\deg(\mathfrak p) > k$ will be discarded.
"""
function prime_ideals_up_to(O::NfOrd, B::Int;
                            complete::Bool = false,
                            degree_limit::Int = 0)
  p = 1
  r = NfOrdIdl[]
  while p < B
    p = next_prime(p)
    if p > B
      return r
    end
    if !complete
      deg_lim = Int(floor(log(B)/log(p)))
      if degree_limit >0
        deg_lim = min(deg_lim, degree_limit)
      end
    else
      deg_lim = 0
    end
    @vprint :ClassGroup 2 "decomposing $p ... (bound is $B, deg_lim $deg_lim)\n"
    li = prime_decomposition(O, p, deg_lim)
    for P in li
      push!(r, P[1])
    end
  end
  return r
end

doc"""
***
    prime_ideals_over(O::NfOrd,
                       lp::AbstractArray{Int, 1};
                       degree_limit::Int = 0) -> Array{NfOrdIdl, 1}

> Computes the prime ideals $\mathcal O$ over prime numbers in $lp$.
>
> If `degree_limit` is a nonzero integer $k$, then prime ideals $\mathfrak p$
> with $\deg(\mathfrak p) > k$ will be discarded.
"""
function prime_ideals_over(O::NfOrd,
                           lp::AbstractArray{T};
                           degree_limit::Int = 0) where T <: Union{fmpz, Integer}
  p = 1
  r = NfOrdIdl[]
  for p in lp
    @vprint :ClassGroup 2 "decomposing $p ... (deg_lim $deg_lim)"
    li = prime_decomposition(O, p, degree_limit)
    for P in li
      push!(r, P[1])
    end
  end
  return r
end


doc"""
***
    prime_ideals_up_to(O::NfOrd,
                       B::Int;
                       complete::Bool = false,
                       degree_limit::Int = 0,
                       F::Function,
                       bad::fmpz)

> Computes the prime ideals $\mathcal O$ with norm up to $B$.
>
> If `degree_limit` is a nonzero integer $k$, then prime ideals $\mathfrak p$
> with $\deg(\mathfrak p) > k$ will be discarded.
>
> The function $F$ must be a function on prime numbers not dividing `bad` such that
> $F(p) = \deg(\mathfrak p)$ for all prime ideals $\mathfrak p$ lying above $p$.
"""
function prime_ideals_up_to(O::NfOrd, B::Int, F::Function, bad::fmpz = discriminant(O);
                            complete::Bool = false,
                            degree_limit::Int = 0)
  p = 1
  r = NfOrdIdl[]
  while p < B
    p = next_prime(p)
    if p > B
      return r
    end
    if !complete
      deg_lim = flog(fmpz(B), p) # Int(floor(log(B)/log(p)))
      if degree_limit > 0
        deg_lim = min(deg_lim, degree_limit)
      end
    else
      deg_lim = 0
    end
    @vprint :ClassGroup 2 "decomposing $p ... (bound is $B)"
    if mod(bad, p) == 0
      li = prime_decomposition(O, p, deg_lim)
      for P in li
        push!(r, P[1])
      end
    else
      if F(p) <= deg_lim
        li = prime_decomposition(O, p, deg_lim)
        for P in li
          push!(r, P[1])
        end
      end
    end
  end
  return r
end

################################################################################
#
#  Coprime
#
################################################################################

#TODO: do sth. useful here!!!
function divides(A::NfOrdIdl, B::NfOrdIdl)
  minimum(A) % minimum(B) == 0 || return false
  return valuation(A, B) > 0
end

function coprime_base(A::Array{NfOrdIdl, 1}, p::fmpz)
  #consider A^2 B and A B: if we do gcd with the minimum, we get twice AB
  #so the coprime base is AB
  #however using the p-part of the norm, the coprime basis becomes A, B...
  if iseven(p)
    lp = prime_decomposition(order(A[1]), 2)
    Ap = [x[1] for x = lp if any(y->divides(y, x[1]) > 0, A)]
    a = remove(p, 2)[2]
    if !isone(a)
      Bp = coprime_base(A, a)
      return vcat(Ap, Bp)  
    else
      return Ap
    end
  else
    Ap = [gcd(x, p^valuation(norm(x), p)) for x = A if minimum(x) % p == 0]
  end
  return coprime_base_steel(Ap)
end

doc"""
***
    coprime_base(A::Array{NfOrdIdl, 1}) -> Array{NfOrdIdl, 1}
    coprime_base(A::Array{NfOrdElem, 1}) -> Array{NfOrdIdl, 1}
> A coprime base for the (principal) ideals in $A$, ie. the returned array
> generated multiplicatively the same ideals as the input and are pairwise
> coprime.
"""
function coprime_base(A::Array{NfOrdIdl, 1})
  a = collect(Set(map(minimum, A)))
  a = coprime_base(a)
  C = Array{NfOrdIdl, 1}()

  for p = a
    if p == 1
      continue
    end
    cp = coprime_base(A, p)
    append!(C, cp)
  end
  return C
end

function coprime_base(A::Array{NfOrdElem, 1})
  O = parent(A[1])
  return coprime_base([ideal(O, x) for x = A])
end

function integral_split(A::NfOrdIdl)
  return A, ideal(Order(A), fmpz(1))
end

################################################################################
#
#  Factorization into prime ideals
#
################################################################################

#TODO: factoring type??? (with unit)
doc"""
***
    factor(A::NfOrdIdl) -> Dict{NfOrdIdl, Int}

> Computes the prime ideal factorization $A$ as a dictionary, the keys being
> the prime ideal divisors:
> If `lp = factor_dict(A)`, then `keys(lp)` are the prime ideal divisors of A
> and `lp[P]` is the `P`-adic valuation of `A` for all `P` in `keys(lp)`.
"""
factor(A::NfOrdIdl) = factor_dict(A)

function factor_dict(A::NfOrdIdl)
  ## this should be fixed
  lf = factor(minimum(A))
  lF = Dict{NfOrdIdl, Int}()
  n = norm(A)
  O = order(A)
  for (i, (p, v)) in enumerate(lf)
    lP = prime_decomposition(O, p)
    for P in lP
      v = valuation(A, P[1])
      if v != 0
        lF[P[1]] = v
        n = n//norm(P[1])^v
      end
      if n == 1
        return lF
      end
    end
  end
  return lF
end

################################################################################
#
#  Primality testing
#
################################################################################

doc"""
***
    isprime_known(A::NfOrdIdl) -> Bool

> Returns whether $A$ knows if it is prime.
"""
function isprime_known(A::NfOrdIdl)
  return A.is_prime != 0
end

doc"""
***
    isprime(A::NfOrdIdl) -> Bool

> Returns whether $A$ is a prime ideal.
"""
function isprime(A::NfOrdIdl)
  if isprime_known(A)
    return A.is_prime == 1
  elseif minimum(A) == 0
    A.is_prime = 2
    return false
  end

  (n, p) = ispower(norm(A, Val{false}))

  if !isprime(p)
    A.is_prime = 2
    return false
  end

  p > 2^62 && error("Not implemented (yet)")

  lp = prime_decomposition(order(A), Int(p))

  for (P, f) in lp
    e = valuation(A, P)
    if e == 1 && n == degree(P)
      A.is_prime = 1
      return true
    elseif e == 0
      continue
    else
      A.is_prime = 2
      return false
    end
  end

  error("Something wrong in isprime")
end

################################################################################
#
#  Valuation
#
################################################################################

# CF:
# Classical algorithm of Cohen, but take a valuation element with smaller (?)
# coefficients. Core idea is that the valuation elementt is, originally, den*gen_two(p)^-1
# where gen_two(p) is "small". Actually, we don't care about gen_two, we
# need gen_two^-1 to be small, hence this version.
function val_func_no_index(p::NfOrdIdl)
  P = p.gen_one
  K = nf(order(p))
  pi = inv(p)
  d = denominator(K(pi.num.gen_two))
  @assert gcd(d, P) == 1
  e = K(pi.num.gen_two)*d
  M = zero_matrix(FlintZZ, 1, degree(K))
  elem_to_mat_row!(M, 1, d, e)
  @assert d == 1
  P2 = P^2
  P22 = div(P2, 2)
  for i=1:degree(K)
    x = M[1,i] % P2
    if x>P22
      x -= P2
    end
    M[1,i] = x
  end
  e = elem_from_mat_row(K, M, 1, P)
  # e is still a valuation element, but with smaller coefficients.
  return function(x::nf_elem)
    v = 0
    d = denominator(x)
    x *= d
    x = x*e
    while denominator(x) % P != 0
      v += 1
      mul!(x, x, e)
    end
    return v-valuation(d, P)*p.splitting_type[1]
  end
end

# CF:
# The idea is that valuations are mostly small, eg. in the class group
# algorithm. So this version computes the completion and the embedding into it
# at small precision and can thus compute (small) valuation at the effective
# cost of an mod(nmod_poly, nmod_poly) operation.
# Isn't it nice?
function valuation(a::UInt, b::UInt)
  return ccall((:n_remove, :libflint), Int, (Ref{UInt}, UInt), a, b)
end

#=
function valuation(a::UInt, b::UInt, bi::Cdouble)
  return ccall((:n_remove2_precomp, :libflint), Int, (Ref{UInt}, UInt, Cdouble), a, b, bi)
end
=#

function val_func_no_index_small(p::NfOrdIdl)
  P = p.gen_one
  @assert P <= typemax(UInt)
  K = nf(order(p))
  Rx = PolynomialRing(ResidueRing(FlintZZ, UInt(P), cached=false), cached=false)[1]
  Zx = PolynomialRing(FlintZZ)[1]
  g = Rx(p.gen_two.elem_in_nf)
  f = Rx(K.pol)
  g = gcd!(g, g, f)
  g = lift(Zx, g)
  k = flog(fmpz(typemax(UInt)), P)
  g = hensel_lift(Zx(K.pol), g, P, k)
  Sx = PolynomialRing(ResidueRing(FlintZZ, UInt(P)^k, cached=false), cached=false)[1]
  g = Sx(g)
  h = Sx()
  uP = UInt(P)
  return function(x::nf_elem)
    d = denominator(x)
    nf_elem_to_nmod_poly!(h, x, false) # ignores the denominator
    h = rem!(h, h, g)
    c = Nemo.coeff_raw(h, 0)
    v = c==0 ? typemax(Int) : valuation(c, uP)
    for i=1:degree(h)
      c = Nemo.coeff_raw(h, i)
      v = min(v, c==0 ? typemax(Int) : valuation(c, uP))
    end
    return v-valuation(d, P)
  end
end

function val_func_index(p::NfOrdIdl)
  # We are in the index divisor case. In larger examples, a lot of
  # time is spent computing denominators of order elements.
  # By using the representation matrix to multiply, we can stay in the order
  # and still be fast (faster even than in field).

  pi = inv(p)
  M = representation_matrix(pi.num.gen_two)
  O = order(p)
  P = p.gen_one
  return function(x::nf_elem)
    v = 0
    d, x_mat = integral_split(x, O)
    Nemo.mul!(x_mat, x_mat, M)
    while gcd(content(x_mat), P) == P  # should divide and test in place
      divexact!(x_mat, x_mat, P)
      Nemo.mul!(x_mat, x_mat, M)
      v += 1
    end
    return v-valuation(d, P)*p.splitting_type[1]
  end
end

doc"""
***
    valuation(a::nf_elem, p::NfOrdIdl) -> fmpz
    valuation(a::NfOrdElem, p::NfOrdIdl) -> fmpz
    valuation(a::fmpz, p::NfOrdIdl) -> fmpz

> Computes the $\mathfrak p$-adic valuation of $a$, that is, the largest $i$
> such that $a$ is contained in $\mathfrak p^i$.
"""
function valuation(a::nf_elem, p::NfOrdIdl)
  @hassert :NfOrd 0 !iszero(a)
  #assert(a !=0) # can't handle infinity yet
  if isdefined(p, :valuation)
    return p.valuation(a)::Int
  end
  O = order(p)
  P = p.gen_one

  # for generic ideals
  if p.splitting_type[2] == 0
    #global bad_ideal = p
    p.valuation = function(a::nf_elem)
      d = denominator(a, O)
      x = O(d*a)
      return valuation_naive(O(x), p)::Int - valuation_naive(O(d), p)::Int
    end
    return p.valuation(a)::Int
  end

  if p.splitting_type[1]*p.splitting_type[2] == degree(O)
    p.valuation = function(a::nf_elem)
      return divexact(valuation(norm(a), P)[1], p.splitting_type[2])::Int
    end
  elseif mod(index(O),P) != 0 && p.splitting_type[1] == 1
    if p.gen_one^2 <= typemax(UInt) 
      f1 = val_func_no_index_small(p)
      f2 = val_func_no_index(p)
      p.valuation = function(x::nf_elem)
        v = f1(x)
        if v > 100  # can happen ONLY if the precision in the .._small function
                    # was too small.
          return f2(x)::Int
        else
          return v::Int
        end
      end
    else
      p.valuation = val_func_no_index(p)
    end
  else
    p.valuation = val_func_index(p)
  end

  return p.valuation(a)::Int
end

doc"""
***
    valuation(a::nf_elem, p::NfOrdIdl) -> fmpz
    valuation(a::NfOrdElem, p::NfOrdIdl) -> fmpz
    valuation(a::fmpz, p::NfOrdIdl) -> fmpz

> Computes the $\mathfrak p$-adic valuation of $a$, that is, the largest $i$
> such that $a$ is contained in $\mathfrak p^i$.
"""
valuation(a::NfOrdElem, p::NfOrdIdl) = valuation(a.elem_in_nf, p)

doc"""
***
    valuation(a::nf_elem, p::NfOrdIdl) -> fmpz
    valuation(a::NfOrdElem, p::NfOrdIdl) -> fmpz
    valuation(a::fmpz, p::NfOrdIdl) -> fmpz

> Computes the $\mathfrak p$-adic valuation of $a$, that is, the largest $i$
> such that $a$ is contained in $\mathfrak p^i$.
"""
function valuation(a::fmpz, p::NfOrdIdl)
  if p.splitting_type[1] == 0
    return valuation_naive(order(p)(a), p)
  end
  P = p.gen_one
  return valuation(a, P)* p.splitting_type[1]
end
valuation(a::Integer, p::NfOrdIdl) = valuation(fmpz(a), p)

#TODO: some more intelligence here...
function valuation_naive(A::NfOrdIdl, B::NfOrdIdl)
  @assert !isone(B)
  Bi = inv(B)
  i = 0
  C = simplify(A* Bi)
  while denominator(C) == 1
    C = simplify(Bi*C)
    i += 1
  end
  return i
end

#TODO: some more intelligence here...
#      in non-maximal orders, interesting ideals cannot be inverted
#      maybe this needs to be checked...
function valuation_naive(x::NfOrdElem, B::NfOrdIdl)
  @assert !isone(B)
  i = 0
  C = B
  while x in C
    i += 1
    C *= B
  end
  return i
end


doc"""
***
    valuation(A::NfOrdIdl, p::NfOrdIdl) -> fmpz

> Computes the $\mathfrak p$-adic valuation of $A$, that is, the largest $i$
> such that $A$ is contained in $\mathfrak p^i$.
"""
function valuation(A::NfOrdIdl, p::NfOrdIdl)
  _assure_weakly_normal_presentation(A)
  if !isdefined(p, :splitting_type) || p.splitting_type[1] == 0 #ie. if p is non-prime...
    return valuation_naive(A, p)
  end
  return min(valuation(A.gen_one, p), valuation(elem_in_nf(A.gen_two), p))
end

################################################################################
#
#   Prime ideals iterator
#
################################################################################

mutable struct PrimeIdealsSet
  order::NfOrd
  from::fmpz
  to::fmpz
  primes::PrimesSet{fmpz}
  currentprime::fmpz
  currentindex::Int
  decomposition::Array{Tuple{NfOrdIdl, Int}, 1}
  proof::Bool
  indexdivisors::Bool
  ramified::Bool
  iscoprimeto::Bool
  coprimeto::NfOrdIdl
  degreebound::Int
  unbound::Bool

  function PrimeIdealsSet(O::NfOrd)
    z = new()
    z.order = O
    z.proof = false
    z.indexdivisors = true
    z.ramified = true
    z.unbound = false
    z.degreebound =  degree(O)
    z.iscoprimeto = false
    return z
  end
end

doc"""
***
    PrimeIdealsSet(O::NfOrd, f, t; proof = false,
                                   indexdivisors = true,
                                   ramified = true,
                                   degreebound = degree(O),
                                   coprimeto = false)  

Returns an iterable object $S$ representing the prime ideals $\mathfrak p$
of $\mathcal O$ with $f \leq \min(\mathfrak p) \leq t$. 

The optional arguments can be used to exclude index divisors, ramified prime
ideals and to include only prime ideals with degree less or equal than
`degreebound` and which are coprime to `coprimeto`.

If $t=-1$, then the upper bound is infinite.

If `coprimeto` is supplied, it must be either an integer, an element of $\mathcal O$,
or a non-zero ideal of $\mathcal O$.
"""  
function PrimeIdealsSet(O::NfOrd, from::T, to::S;
                       proof::Bool = false,
                       indexdivisors::Bool = true,
                       ramified::Bool = true,
                       degreebound::Int = degree(O),
                       coprimeto = false) where {T <: Union{fmpz, Integer},
                                                 S <: Union{fmpz, Integer}}
  from < 0 && error("Lower bound must be non-negative")
  to < -1 && error("Upper bound must be non-negative or -1")

  z = PrimeIdealsSet(O)
  z.from = fmpz(from)
  z.to = fmpz(to)
  z.primes = PrimesSet(z.from, z.to)
  if to == -1
    z.unbound = true
  end
  z.proof = proof
  z.indexdivisors = indexdivisors
  z.ramified = ramified
  z.degreebound = degreebound
  if !(coprimeto isa Bool)
    if coprimeto isa NfOrdIdl
      z.coprimeto = coprimeto
    elseif coprimeto isa Union{Integer, fmpz, NfOrdElem}
      z.coprimeto = ideal(O, coprimeto)
    else
      error("Coprime argument of wrong type ($(typeof(coprimeto)))")
    end
    z.iscoprimeto = true
  end
  return z
end

function Base.start(S::PrimeIdealsSet)
  O = S.order
  pstate = start(S.primes)
  found_prime = false
  while !found_prime
    (p, pstate) = next(S.primes, pstate)
    if !S.indexdivisors && isindex_divisor(O, p)
      continue
    end
    lP = prime_decomposition(O, p)
    j = -1
    for i in 1:length(lP)
      e = lP[i][2]
      if !S.ramified && e > 1
        continue
      end
      P = lP[i][1]
      if P.splitting_type[2] > S.degreebound
        continue
      end
      if S.iscoprimeto && !iscoprime(P, S.coprimeto)
        continue
      end
      j = i
      break
    end
    if j != -1
      S.decomposition = lP
      S.currentprime = p
      S.currentindex = j
      return (p, j)
    end
  end
end

function Base.next(S::PrimeIdealsSet, x)
  pstate = x[1]
  j = x[2]
  Q = S.decomposition[j][1] # This we want to return
  newindex = -1
  lP = S.decomposition
  O = S.order

  # Find the next prime ideal in the current decomposition
  for i in (j + 1):length(S.decomposition)
    e = lP[i][2]
    if !S.ramified && e > 1
      continue
    end
    P = lP[i][1]
    if P.splitting_type[2] > S.degreebound
      continue
    end
    newindex = i
    break
  end

  if newindex != -1
    return Q, (pstate, newindex)
  else
    # We have to change the prime
    found_prime = false
    while !found_prime
      (p, pstate) = next(S.primes, pstate)
      if !S.indexdivisors && isindex_divisor(O, pstate)
        continue
      end
      lP = prime_decomposition(O, pstate)
      j = -1
      for i in 1:length(lP)
        e = lP[i][2]
        if !S.ramified && e > 1
          continue
        end
        P = lP[i][1]
        if P.splitting_type[2] > S.degreebound
          continue
        end
        if S.iscoprimeto && !iscoprime(P, S.coprimeto)
          continue
        end
        j = i
        break
      end
      if j != -1
        S.decomposition = lP
        S.currentprime = p
        S.currentindex = j
        return Q, (pstate, j)
      end
    end
  end
end

function Base.done(S::PrimeIdealsSet, x)
  pstate = x[1]
  index = x[2]
  return !S.unbound && pstate > S.to
end

Base.eltype(::PrimeIdealsSet) = NfOrdIdl

Base.iteratorsize(::Type{PrimeIdealsSet}) = Base.SizeUnknown()
