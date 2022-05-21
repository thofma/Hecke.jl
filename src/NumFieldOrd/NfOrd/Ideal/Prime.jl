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

export PrimeIdealsSet, prime_ideals_over, ramification_index,
       prime_ideals_up_to, decomposition_group, inertia_subgroup,
       ramification_group, is_ramified, is_tamely_ramified, is_weakly_ramified,
       approximate

@doc Markdown.doc"""
    is_ramified(O::NfOrd, p::Int) -> Bool

Returns whether the integer $p$ is ramified in $\mathcal O$.
It is assumed that $p$ is prime.
"""
function is_ramified(O::NfAbsOrd, p::Union{Int, fmpz})
  @assert is_maximal_known_and_maximal(O)
  return mod(discriminant(O), p) == 0
end

@doc Markdown.doc"""
    is_tamely_ramified(O::NfOrd, p::Union{Int, fmpz}) -> Bool

Returns whether the integer $p$ is tamely ramified in $\mathcal O$.
It is assumed that $p$ is prime.
"""
function is_tamely_ramified(K::AnticNumberField, p::Union{Int, fmpz})
  lp = prime_decomposition(maximal_order(K), p)
  for (_, q) in lp
    if gcd(q, p) != 1
      return false
    end
  end
  return true
end

@doc Markdown.doc"""
    is_tamely_ramified(K::AnticNumberField) -> Bool

Returns whether the number field $K$ is tamely ramified.
"""
function is_tamely_ramified(K::AnticNumberField)
  p = fmpz(2)
  while p <= degree(K)
    if !is_tamely_ramified(K, p)
      return false
    end
    p = next_prime(p)
  end
  return true
end

@doc Markdown.doc"""
    is_weakly_ramified(K::AnticNumberField, P::NfOrdIdl) -> Bool

Given a prime ideal $P$ of a number field $K$, return whether $P$
is weakly ramified, that is, whether the second ramification group
is trivial.
"""
function is_weakly_ramified(K::AnticNumberField, P::NfOrdIdl)
  return length(ramification_group(P, 2)) == 1
end

@doc Markdown.doc"""
    degree(P::NfOrdIdl) -> Int

The inertia degree of the prime-ideal $P$.
"""
function degree(A::NfAbsOrdIdl)
  @assert is_prime(A)
  return A.splitting_type[2]
end

inertia_degree(A::NfAbsOrdIdl) = degree(A)

@doc Markdown.doc"""
    ramification_index(P::NfOrdIdl) -> Int

The ramification index of the prime-ideal $P$.
"""
function ramification_index(A::NfAbsOrdIdl)
  @assert is_prime(A)
  return A.splitting_type[1]
end

################################################################################
#
#  Prime decomposition
#
################################################################################

@doc Markdown.doc"""
    lift(K::AnticNumberField, f::nmod_poly) -> nf_elem

Given a polynomial $f$ over a finite field, lift it to an element of the
number field $K$. The lift is given by the element represented by the
canonical lift of $f$ to a polynomial over the integers.
"""
function lift(K::AnticNumberField, f::T) where {T <: Zmodn_poly}
  if degree(f)>=degree(K)
    f = mod(f, parent(f)(K.pol))
  end
  r = K()
  for i=0:f.length-1
    u = ccall((:nmod_poly_get_coeff_ui, libflint), UInt, (Ref{T}, Int), f, i)
    _num_setcoeff!(r, i, u)
  end
  return r
end

function lift(K::AnticNumberField, f::gfp_fmpz_poly)
  if degree(f)>=degree(K)
    f = mod(f, parent(f)(K.pol))
  end
  r = K()
  for i=0:f.length-1
    u = fmpz()
    ccall((:fmpz_mod_poly_get_coeff_fmpz, libflint), Nothing, (Ref{fmpz}, Ref{gfp_fmpz_poly}, Int, Ref{fmpz_mod_ctx_struct}), u, f, i, f.parent.base_ring.ninv)
    _num_setcoeff!(r, i, u)
  end
  return r
end

##TODO: make fmpz-safe!!!!
#return <p, lift(O, fi> in 2-element normal presentation given the data
function ideal_from_poly(O::NfOrd, p::Int, fi::Zmodn_poly, ei::Int)
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

  if idl.splitting_type[2] == degree(O)
    # Prime number is inert, in particular principal
    idl.is_principal = 1
    idl.princ_gen = O(p)
  end
  return idl
end

function ideal_from_poly(O::NfOrd, p::fmpz, fi::gfp_fmpz_poly, ei::Int)
  b = lift(nf(O), fi)
  idl = ideal(O, p, O(b, false))
  idl.is_prime = 1
  idl.splitting_type = ei, degree(fi)
  idl.norm = p^degree(fi)
  idl.minimum = p

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

  if idl.splitting_type[2] == degree(O)
    # Prime number is inert, in particular principal
    idl.is_principal = 1
    idl.princ_gen = O(p)
  end
  return idl
end

@doc Markdown.doc"""
    prime_decomposition(O::NfAbsOrd,
                        p::Integer,
                        degree_limit::Int = 0,
                        lower_limit::Int = 0) -> Vector{Tuple{NfOrdIdl, Int}}

Returns an array of tuples $(\mathfrak p_i,e_i)$ such that $p \mathcal O$ is the product of
the $\mathfrak p_i^{e_i}$ and $\mathfrak p_i \neq \mathfrak p_j$ for $i \neq j$.

If `degree_limit` is a nonzero integer $k > 0$, then only those prime ideals
$\mathfrak p$ with $\deg(\mathfrak p) \leq k$ will be returned.
Similarly if `lower_limit` is a nonzero integer $l > 0$, then only those prime ideals
$\mathfrak p$ with $l \leq \deg(\mathfrak p)$ will be returned.
Note that in this case it may happen that $p\mathcal O$ is not the product of the
$\mathfrak p_i^{e_i}$.
"""
function prime_decomposition(O::NfAbsOrd{NfAbsNS, NfAbsNSElem}, p::IntegerUnion, degree_limit::Int = degree(O), lower_limit::Int = 0; cached::Bool = true)
  if typeof(p) != Int && fits(Int, p)
    return prime_decomposition(O, Int(p), degree_limit, lower_limit, cached = cached)
  end
  if typeof(p) != fmpz && typeof(p) != Int
    return prime_decomposition(O, fmpz(p), degree_limit, lower_limit, cached = cached)
  end

  if !divisible(numerator(discriminant(nf(O))), p)
    return prime_dec_nonindex(O, p, degree_limit, lower_limit)
  else
    return prime_dec_gen(O, p, degree_limit, lower_limit)
  end
end

Nemo.fits(::Type{Int}, a::Int) = true
function Nemo.fits(::Type{Int}, a::Integer)
  #TODO: possibly not optimal?
  return a % Int == a
end

function prime_decomposition(O::NfOrd, p::IntegerUnion, degree_limit::Int = degree(O), lower_limit::Int = 0; cached::Bool = false)
  if typeof(p) != Int && fits(Int, p)
    return prime_decomposition(O, Int(p), degree_limit, lower_limit, cached = cached)
  end
  if typeof(p) != fmpz && typeof(p) != Int
    return prime_decomposition(O, fmpz(p), degree_limit, lower_limit, cached = cached)
  end

  if is_defining_polynomial_nice(nf(O))
    if cached || is_index_divisor(O, p)
      if haskey(O.index_div, fmpz(p))
        lp = O.index_div[fmpz(p)]::Vector{Tuple{NfOrdIdl, Int}}
        z = Tuple{NfOrdIdl, Int}[]
        for (Q, e) in lp
          if degree_limit == 0 || degree(Q) <= degree_limit
            push!(z, (Q, e))
          end
        end
        return z
      end
    end
    if is_index_divisor(O, p)
      @assert O.is_maximal == 1 || p in O.primesofmaximality
      lp = prime_decomposition_polygons(O, p, degree_limit, lower_limit)
      if degree_limit == degree(O) && lower_limit == 0
        O.index_div[fmpz(p)] = lp
        return copy(lp)
      else
        return lp
      end
    else
      @assert O.is_maximal == 1 || p in O.primesofmaximality || !divisible(discriminant(O), p)
      lp = prime_dec_nonindex(O, p, degree_limit, lower_limit)
      if cached && degree_limit == degree(O) && lower_limit == 0
        O.index_div[fmpz(p)] = lp
        return copy(lp)
      else
        return lp
      end
    end
  end
  return prime_dec_gen(O, p, degree_limit, lower_limit)
end

function prime_dec_gen(O::NfAbsOrd, p::Union{fmpz, Int}, degree_limit::Int = degree(O), lower_limit::Int = 0)
  Ip = pradical(O, p)
  lp = Hecke._decomposition(O, ideal(O, p), Ip, ideal(O, 1), fmpz(p))
  z = Tuple{ideal_type(O), Int}[]
  for (Q, e) in lp
    if degree(Q) <= degree_limit && degree(Q) >= lower_limit
      push!(z, (Q, e))
    end
  end
  return z
end

function _fac_and_lift(f::fmpz_poly, p, degree_limit, lower_limit)
  if p > 2 && isone(degree_limit)
    return _fac_and_lift_deg1(f, p)
  end
  Zx = parent(f)
  Zmodpx, x = PolynomialRing(GF(p, cached = false), "y", cached = false)
  fmodp = Zmodpx(f)
  if isone(degree_limit)
    fmodp = ppio(fmodp, powermod(x, p, fmodp)-x)[1]
  end
  fac = factor(fmodp)
  lifted_fac = Vector{Tuple{fmpz_poly, Int}}()
  for (k, v) in fac
    if degree(k) <= degree_limit && degree(k) >= lower_limit
      push!(lifted_fac, (lift(Zx, k), v))
    end
  end
  return lifted_fac
end

function _fac_and_lift_deg1(f::fmpz_poly, p)
  lifted_fac = Vector{Tuple{fmpz_poly, Int}}()
  Zx = parent(f)
  Zmodpx, x = PolynomialRing(GF(p, cached = false), "y", cached = false)
  fmodp = Zmodpx(f)
  fsq = factor_squarefree(fmodp)
  pw = powermod(x, div(p-1, 2), fmodp)
  for (g, v) in fsq
    gcd1 = gcd(g, pw-1)
    gcd2 = gcd(g, pw+1)
    divisible_by_x = iszero(coeff(g, 0))
    if divisible_by_x
      push!(lifted_fac, (gen(Zx), v))
    end
    if !isone(gcd1)
      fac1 = factor_equal_deg(gcd1, 1)
      for k in fac1
        push!(lifted_fac, (lift(Zx, k), v))
      end
    end
    if !isone(gcd2)
      fac2 = factor_equal_deg(gcd2, 1)
      for k in fac2
        push!(lifted_fac, (lift(Zx, k), v))
      end
    end
  end
  return lifted_fac
end


function prime_dec_nonindex(O::NfOrd, p::IntegerUnion, degree_limit::Int = 0, lower_limit::Int = 0)

  K = nf(O)
  f = K.pol
  R = parent(f)
  Zx, x = PolynomialRing(FlintZZ, "x", cached = false)
  Zf = Zx(f)

  if degree_limit == 0
    degree_limit = degree(K)
  end

  fac = _fac_and_lift(Zf, p, degree_limit, lower_limit)

  result = Array{Tuple{ideal_type(O),Int}}(undef, length(fac))

  for k in 1:length(fac)
    fi = fac[k][1]
    ei = fac[k][2]
    #ideal = ideal_from_poly(O, p, fi, ei)
    t = parent(f)(fi)
    b = K(t)
    I = NfAbsOrdIdl(O)
    I.gen_one = p
    I.gen_two = O(b, false)
    I.is_prime = 1
    I.splitting_type = ei, degree(fi)
    I.norm = FlintZZ(p)^degree(fi)
    I.minimum = FlintZZ(p)

    # We have to do something to get 2-normal presentation:
    # if ramified or valuation val(b,P) == 1, (p,b)
    # is a P(p)-normal presentation
    # otherwise we need to take p+b
    # I SHOULD CHECK THAT THIS WORKS

    if ei == 1 && is_norm_divisible_pp(b, p*I.norm)
      I.gen_two = I.gen_two + O(p)
    end

    I.gens_normal = fmpz(p)
    I.gens_weakly_normal = true

    if length(fac) == 1 && I.splitting_type[2] == degree(f)
      # Prime number is inert, in particular principal
      I.is_principal = 1
      I.princ_gen = O(p)
    end
    result[k] = (I, ei)
  end
  return result
end

function _lift(T::Vector{Generic.Res{fmpz}})
  return fmpz[ z.data for z in T ]
end

function _lift(T::Vector{Generic.ResF{fmpz}})
  return fmpz[ z.data for z in T ]
end

function _lift(T::Vector{Nemo.nmod})
  return [ fmpz(z.data) for z in T ]
end

function _lift(T::Vector{Nemo.gfp_elem})
  return [ fmpz(z.data) for z in T ]
end

# Belabas p. 40
# Facts on normal presentation, Algorithmic Algebraic Number theory, Pohst-Zassenhaus
function anti_uniformizer(P::NfAbsOrdIdl)
  if isdefined(P, :anti_uniformizer)
    return P.anti_uniformizer
  end
  if has_2_elem_normal(P)
    Pinv = inv(P)
    P.anti_uniformizer = mod(divexact(Pinv.num.gen_two.elem_in_nf, Pinv.den), minimum(P))
    return P.anti_uniformizer
  end
  p = minimum(P)
  M = representation_matrix(uniformizer(P))
  #Mp = MatrixSpace(ResidueField(FlintZZ, p, cached=false), nrows(M), ncols(M), false)(M)
  Mp = change_base_ring(GF(p, cached = false), M)
  K = left_kernel_basis(Mp)
  @assert length(K) > 0
  P.anti_uniformizer = elem_in_nf(order(P)(lift.(K[1])))//p
  return P.anti_uniformizer
end

function _factor_distinct_deg(x::gfp_poly)
  degs = Vector{Int}(undef, degree(x))
  degss = [ pointer(degs) ]
  fac = Nemo.gfp_poly_factor(x.mod_n)
  ccall((:nmod_poly_factor_distinct_deg, libflint), UInt,
          (Ref{Nemo.gfp_poly_factor}, Ref{gfp_poly}, Ptr{Ptr{Int}}),
          fac, x, degss)
  res = Dict{Int, Int}()
  f = parent(x)()
  for i in 1:fac.num
    ccall((:nmod_poly_factor_get_nmod_poly, libflint), Nothing,
            (Ref{gfp_poly}, Ref{Nemo.gfp_poly_factor}, Int), f, fac, i-1)
    res[degs[i]] = divexact(degree(f), degs[i])
  end
  return res
end

function _factor_distinct_deg(x::gfp_fmpz_poly)
  degs = Vector{Int}(undef, degree(x))
  degss = [ pointer(degs) ]
  n = x.parent.base_ring.ninv
  fac = Nemo.gfp_fmpz_poly_factor(n)
  ccall((:fmpz_mod_poly_factor_distinct_deg, libflint), UInt,
          (Ref{Nemo.gfp_fmpz_poly_factor}, Ref{gfp_fmpz_poly}, Ptr{Ptr{Int}}, Ref{fmpz_mod_ctx_struct}),
          fac, x, degss, n)
  res = Dict{Int, Int}()
  f = parent(x)()
  for i in 1:fac.num
    ccall((:fmpz_mod_poly_factor_get_fmpz_mod_poly, libflint), Nothing,
            (Ref{gfp_fmpz_poly}, Ref{Nemo.gfp_fmpz_poly_factor}, Int, Ref{fmpz_mod_ctx_struct}), f, fac, i-1, n)
    res[degs[i]] = divexact(degree(f), degs[i])
  end
  return res
end

function _prime_decomposition_type(fmodp)
  discdeg = _factor_distinct_deg(fmodp)
  nfacts = sum(x for x in values(discdeg))
  res = Array{Tuple{Int, Int}}(undef, nfacts)
  s = 1
  for (k, v) in discdeg
    for j in 1:v
      res[s] = (k, 1)
      s = s + 1
    end
  end
  return res
end

@doc Markdown.doc"""
    prime_decomposition_type(O::NfOrd, p::Integer) -> Vector{Tuple{Int, Int}}

Returns an array of tuples whose length is the number of primes lying over $p$ and the $i$-th tuple
gives the splitting type of the corresponding prime, ordered as inertia degree and ramification index.
"""
function prime_decomposition_type(O::NfOrd, p::T) where T <: IntegerUnion
  if !is_defining_polynomial_nice(nf(O))
    return Tuple{Int, Int}[(degree(x[1]), x[2]) for x = prime_decomposition(O, p)]
  end
  if (mod(discriminant(O), p)) != 0 && (mod(fmpz(index(O)), p) != 0)
    K = nf(O)
    f = K.pol
    R = parent(f)
    Zx, x = PolynomialRing(FlintZZ,"x", cached = false)
    Zf = Zx(f)
    fmodp = PolynomialRing(GF(p, cached = false), "y", cached = false)[1](Zf)
    return _prime_decomposition_type(fmodp)
  else
    @assert O.is_maximal == 1 || p in O.primesofmaximality
    return decomposition_type_polygon(O, p)
  end

end

@doc Markdown.doc"""
    prime_ideals_up_to(O::NfOrd,
                       B::Int;
                       degree_limit::Int = 0, index_divisors::Bool = true) -> Vector{NfOrdIdl}

Computes the prime ideals $\mathcal O$ with norm up to $B$.

If `degree_limit` is a nonzero integer $k$, then prime ideals $\mathfrak p$
with $\deg(\mathfrak p) > k$ will be discarded.
If 'index_divisors' is set to false, only primes not dividing the index of the order will be computed.
"""
function prime_ideals_up_to(O::NfOrd, B::Int;
                            complete::Bool = false,
                            degree_limit::Int = 0, index_divisors::Bool = true)

  p = 1
  r = NfOrdIdl[]
  while p < B
    p = next_prime(p)
    if p > B
      return r
    end
    if !index_divisors && divisible(index(O), p)
      continue
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

@doc Markdown.doc"""
    prime_ideals_over(O::NfOrd,
                       lp::AbstractVector{Int};
                       degree_limit::Int = 0) -> Vector{NfOrdIdl}

Computes the prime ideals $\mathcal O$ over prime numbers in $lp$.

If `degree_limit` is a nonzero integer $k$, then prime ideals $\mathfrak p$
with $\deg(\mathfrak p) > k$ will be discarded.
"""
function prime_ideals_over(O::NfOrd,
                           lp::AbstractArray{T};
                           degree_limit::Int = 0) where T <: IntegerUnion
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


@doc Markdown.doc"""
    prime_ideals_up_to(O::NfOrd,
                       B::Int;
                       complete::Bool = false,
                       degree_limit::Int = 0,
                       F::Function,
                       bad::fmpz)

Computes the prime ideals $\mathcal O$ with norm up to $B$.

If `degree_limit` is a nonzero integer $k$, then prime ideals $\mathfrak p$
with $\deg(\mathfrak p) > k$ will be discarded.

The function $F$ must be a function on prime numbers not dividing `bad` such that
$F(p) = \deg(\mathfrak p)$ for all prime ideals $\mathfrak p$ lying above $p$.
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
@doc Markdown.doc"""
    divides(A::NfOrdIdl, B::NfOrdIdl)

Checks if $B$ divides $A$.
"""
function divides(A::NfOrdIdl, B::NfOrdIdl)
  @assert order(A) === order(B)
  minimum(A, copy = false) % minimum(B, copy = false) == 0 || return false
  if B.is_prime == 1 && has_2_elem(A) && !is_index_divisor(order(A), minimum(B, copy = false))
    #I can just test the polynomials!
    K = nf(order(A))
    Qx = parent(K.pol)
    if !fits(Int, minimum(B))
      R = ResidueRing(FlintZZ, minimum(B), cached = false)
      Rx = PolynomialRing(R, "t", cached = false)[1]
      f1 = Rx(Qx(A.gen_two.elem_in_nf))
      f2 = Rx(Qx(B.gen_two.elem_in_nf))
      if iszero(f2)
        res = iszero(f1)
      else
        res = iszero(mod(f1, f2))
      end
    else
      R1 = ResidueRing(FlintZZ, Int(minimum(B)), cached = false)
      R1x = PolynomialRing(R1, "t", cached = false)[1]
      f11 = R1x(Qx(A.gen_two.elem_in_nf))
      f21 = R1x(Qx(B.gen_two.elem_in_nf))
      if iszero(f21)
        res = iszero(f11)
      else
        res = iszero(mod(f11, f21))
      end
    end
    #@assert res == (valuation(A, B) > 0)
    return res
  end
  if has_2_elem(A)
    OK = order(A)
    el = anti_uniformizer(B)
    d = denominator(el)
    el1 = mod(A.gen_two.elem_in_nf, d)
    return el*el1 in OK
  end
  return (valuation(A, B) > 0)::Bool
end

function coprime_base(A::Vector{NfOrdIdl}, p::fmpz)
  #consider A^2 B and A B: if we do gcd with the minimum, we get twice AB
  #so the coprime base is AB
  #however using the p-part of the norm, the coprime basis becomes A, B...
  if iseven(p)
    lp = prime_decomposition(order(A[1]), 2)
    Ap = NfOrdIdl[x[1] for x = lp if any(y-> divides(y, x[1]), A)]
    a = remove(p, 2)[2]
    if !isone(a)
      Bp = coprime_base(A, a)
      return vcat(Ap, Bp)
    else
      return Ap
    end
  else
    Ap = NfOrdIdl[]
    for x in A
      if minimum(x) % p == 0
        push!(Ap, gcd(x, p^valuation(norm(x), p)))
      end
    end
  end
  return coprime_base_steel(Ap)
end


function _get_integer_in_ideal(I::NfOrdIdl)
  if has_minimum(I)
    return minimum(I)
  end
  if has_2_elem(I)
    return I.gen_one
  end
  if has_norm(I)
    return norm(I)
  end
  return minimum(I)
end

@doc Markdown.doc"""
    coprime_base(A::Vector{NfOrdIdl}) -> Vector{NfOrdIdl}
    coprime_base(A::Vector{NfOrdElem}) -> Vector{NfOrdIdl}

A coprime base for the (principal) ideals in $A$, i.e. the returned array
generated multiplicatively the same ideals as the input and are pairwise
coprime.
"""
function coprime_base(A::Vector{NfOrdIdl}; refine::Bool = false)
  if isempty(A)
    return NfOrdIdl[]
  end
  OK = order(A[1])
  if refine
    pf = prefactorization(A[1])
    for i = 2:length(A)
      append!(pf, prefactorization(A[i]))
    end
    a1 = fmpz[x.gen_one for x in pf if !isone(x.gen_one)]
    if !isempty(a1)
      a1 = coprime_base(a1)
    end
    for I in pf
      if !(I.gen_one in a1) && !isone(minimum(I, copy = false))
        push!(a1, minimum(I))
        push!(a1, norm(I))
      end
    end
  else
    pf = A
    a2 = Set{fmpz}()
    for x in pf
      if !isone(minimum(x, copy = false))
        push!(a2, minimum(x), norm(x))
      end
    end
    a1 = collect(a2)
  end
  if isempty(a1)
    return NfOrdIdl[]
  end
  a = coprime_base(a1)
  C = Vector{NfOrdIdl}()
  for p = a
    if isone(p)
      continue
    end
    @vprint :CompactPresentation :3 "Doing $p, is_prime: $(is_prime(p)), is index divisor: $(is_index_divisor(OK, p))\n"
    if is_prime(p)
      lp = prime_decomposition(OK, p)
      for (P, v) in lp
        found = false
        for i = 1:length(pf)
          if divisible(_get_integer_in_ideal(pf[i]), p) && divisible(norm(pf[i], copy = false), p) && divides(pf[i], P)
            found = true
            break
          end
        end
        if found
          push!(C, P)
        end
      end
    else
      cp = coprime_base(pf, p)
      append!(C, cp)
    end
  end
  return C
end

function coprime_base(A::Vector{NfOrdElem})
  O = parent(A[1])
  return coprime_base(NfOrdIdl[ideal(O, x) for x = A])
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
@doc Markdown.doc"""
    factor(A::NfOrdIdl) -> Dict{NfOrdIdl, Int}

Computes the prime ideal factorization $A$ as a dictionary, the keys being
the prime ideal divisors:
If `lp = factor_dict(A)`, then `keys(lp)` are the prime ideal divisors of $A$
and `lp[P]` is the $P$-adic valuation of $A$ for all $P$ in `keys(lp)`.
"""
factor(A::NfAbsOrdIdl) = factor_dict(A)

function factor_dict(A::NfAbsOrdIdl)
  ## this should be fixed
  #TODO:Test first if the ideal is a power.
  lF = Dict{typeof(A), Int}()
  O = order(A)
  if has_princ_gen_special(A)
    g = A.princ_gen_special[2] + A.princ_gen_special[3]
    fg = factor(g)
    for (p, v) in fg
      lP = prime_decomposition(O, p)
      for (P, vv) in lP
        lF[P] = vv*v
      end
    end
    return lF
  end
  n = norm(A)
  if isone(n)
    return lF
  end
  if has_2_elem(A)
    lf_pre = _prefactorization(A)
  else
    lf_pre = fmpz[minimum(A)]
  end
  O = order(A)
  for i = 1:length(lf_pre)
    lf = factor(lf_pre[i])
    for (p, v) in lf
      lP = prime_decomposition(O, p)
      for P in lP
        v = valuation(A, P[1])
        if v != 0
          lF[P[1]] = v
          n = divexact(n, norm(P[1])^v)
        end
        if is_coprime(n, p)
          break
        end
      end
    end
  end
  return lF
end

function factor_easy(I::NfOrdIdl)
  OK = order(I)
  _assure_weakly_normal_presentation(I)
  factors = _prefactorization(I)
  ideals = Dict{NfOrdIdl, Int}()
  for q in factors
    pp, r = Hecke._factors_trial_division(q)
    for p in pp
      lp = prime_decomposition(OK, p)
      for (P, vP) in lp
        ideals[P] = valuation(I, P)
      end
    end
    r = is_power(r)[2]
    if !isone(r)
      J = gcd(I, r)
      ideals[J] = valuation(I, J)
    end
  end
  return ideals
end

function _prefactorization(I::NfOrdIdl)
  @assert has_2_elem(I)
  n = I.gen_one
  if has_minimum(I)
    n = minimum(I)
  elseif has_norm(I)
    n = gcd(norm(I), n)
  end
  K = nf(I)
  el = I.gen_two.elem_in_nf
  Zx = PolynomialRing(FlintZZ, "x")[1]
  f = Zx(K.pol)
  f1 = Zx(denominator(el)*el)
  return prefactorization(f, n, f1)
end

function _prefactorization(I::NfAbsOrdIdl)
  return coprime_base(fmpz[I.gen_one, norm(I), minimum(I)])
end

function prefactorization(I::NfAbsOrdIdl)
  OK = order(I)
  _assure_weakly_normal_presentation(I)
  factors = _prefactorization(I)
  ideals = typeof(I)[]
  for q in factors
    pp, r = Hecke._factors_trial_division(q)
    for p in pp
      push!(ideals, gcd(I, p))
    end
    r = is_power(r)[2]
    if !isone(r)
      push!(ideals, gcd(I, r))
    end
  end
  return ideals
end

################################################################################
#
#  Primality testing
#
################################################################################

@doc Markdown.doc"""
    is_prime_known(A::NfOrdIdl) -> Bool

Returns whether $A$ knows if it is prime.
"""
function is_prime_known(A::NfAbsOrdIdl)
  return A.is_prime != 0
end

@doc Markdown.doc"""
    is_prime(A::NfOrdIdl) -> Bool

Returns whether $A$ is a prime ideal.
"""
function is_prime(A::NfAbsOrdIdl)
  if is_prime_known(A)
    return A.is_prime == 1
  elseif minimum(A) == 0
    A.is_prime = 1
    return true
  end

  K = nf(order(A))

  (n, p) = is_power(norm(A, copy = false))

  if !is_prime(p)
    A.is_prime = 2
    return false
  end
  if n == 1
    A.is_prime = 1
    A.splitting_type = (valuation(p, A), 1)
    return true
  end
  OK = order(A)

  #maximal order case
  if OK.is_maximal == 1 || (is_simple(K) && !iszero(mod(discriminant(OK), p)) || p in OK.primesofmaximality)
    lp = prime_decomposition(OK, p)
    for (P, e) in lp
      if norm(A) != norm(P)
        continue
      end
      if P.gen_two in A
        A.is_prime = 1
        A.splitting_type = P.splitting_type
        return true
      end
    end
    A.is_prime = 2
    return false
  end

  #non-maximal order
  lp = prime_ideals_over(order(A), p)
  for P in lp
    if norm(A) != norm(P)
      continue
    end
    if A == P
      A.is_prime = 1
      return true
    end
  end
  A.is_prime = 2
  return false
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
  decomposition::Vector{Tuple{NfOrdIdl, Int}}
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

@doc Markdown.doc"""
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
                       coprimeto = false) where {T <: IntegerUnion,
                                                 S <: IntegerUnion}
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

function Base.iterate(S::PrimeIdealsSet)
  O = S.order
  found_prime = false
  start = true
  p, pstate = iterate(S.primes)
  while !found_prime
    if !start
      p, pstate = iterate(S.primes, pstate)
    else
      start = false
    end
    if !S.indexdivisors && is_index_divisor(O, p)
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
      if S.iscoprimeto && !is_coprime(P, S.coprimeto)
        continue
      end
      j = i
      break
    end
    if j != -1
      S.decomposition = lP
      S.currentprime = p
      S.currentindex = j
      Q = S.decomposition[j][1]
      return Q, (pstate, j + 1)
    end
      end
end

function Base.iterate(S::PrimeIdealsSet, x)
  j = x[2]
  pstate = x[1]
  newindex = -1
  lP = S.decomposition
  O = S.order

  # Find the next prime ideal in the current decomposition
  for i in j:length(S.decomposition)
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
    return lP[newindex][1], (pstate, newindex + 1)
  else
    # We have to change the prime
    found_prime = false
    while !found_prime
      it =  iterate(S.primes, pstate)
      if it === nothing
        return nothing
      else
        (p, pstate) = it
      end
      if !S.indexdivisors && is_index_divisor(O, pstate)
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
        if S.iscoprimeto && !is_coprime(P, S.coprimeto)
          continue
        end
        j = i
        break
      end
      if j != -1
        S.decomposition = lP
        S.currentprime = p
        S.currentindex = j
        return lP[j][1], (pstate, j + 1)
      end
    end
  end
end

#function Base.done(S::PrimeIdealsSet, x)
#  pstate = x[1]
#  index = x[2]
#  return !S.unbound && pstate > S.to
#end

Base.eltype(::PrimeIdealsSet) = NfOrdIdl

Base.IteratorSize(::Type{PrimeIdealsSet}) = Base.SizeUnknown()

#      iterator for residue rings/ fields
#      check is unit_group(quo(R, A)) for non-maximal R is correct (well intended to be correct)
#      saturation in the Singular sense

################################################################################
#
#  Primary decomposition
#
################################################################################

#TODO: move to Arithmetic?
function radical(A::NfOrdIdl)
  a = minimum(A)
  lp = factor(a).fac
  R = 1*order(A)
  for p = keys(lp)
    R = intersect(R, A + pradical(order(A), p))
  end
  return R
end

#Algo:
# primary -> radical is prime, so this is neccessary
# in orders: prime -> maximal (or 0)
# in general: radical is maximal -> primary
function is_primary(A::NfOrdIdl)
  return is_prime(radical(A))
end
is_maximal(A::NfOrdIdl) = (!iszero(A)) && is_prime(A)

function primary_decomposition(A::NfOrdIdl)
  a = minimum(A)
  lp = factor(a).fac
  P = NfOrdIdl[]
  for p = keys(lp)
    pp = prime_ideals_over(order(A), p)
    for x = pp
      y = x + A
      if !isone(y)
        #TODO: what is the correct exponent here?
        push!(P, x^(div(degree(order(A)), flog(norm(x), p))*lp[p]) + A)
      end
    end
  end
  return P
end

################################################################################
#
#  Prime ideals over an integer (for non-maximal orders)
#
################################################################################

prime_ideals_over(O::NfAbsOrd, p::Integer) = prime_ideals_over(O, fmpz(p))

function prime_ideals_over(O::NfAbsOrd, p::fmpz)
  if is_maximal_known_and_maximal(O)
    lp = prime_decomposition(O, p)
    return NfOrdIdl[x[1] for x in lp]
  end
  M = maximal_order(O)
  lp = prime_decomposition(M, p)
  p_critical_primes = Vector{ideal_type(O)}()
  for (P, e) in lp
    c = contract(P, O)
    c.is_prime = 1
    if !(c in p_critical_primes)
      push!(p_critical_primes, c)
    end
  end
  return p_critical_primes
end

#P is a prime ideal in a order contained in O
#Computes the set of prime ideals lying over P
function prime_ideals_over(O::NfOrd, P::NfOrdIdl)
  @assert is_prime(P)
  O1 = order(P)
  if O1 == O
    return ideal_type(O)[P]
  end
  M = maximal_order(O)
  lp = prime_decomposition(M, minimum(P))
  p_critical_primes = Vector{ideal_type(O)}()
  for (Q, e) in lp
    c = contract(Q, O1)
    if c == P
      c1 = contract(Q, O)
      c1.is_prime = 1
      if !(c1 in p_critical_primes)
        push!(p_critical_primes, c1)
      end
    end
  end
  return p_critical_primes
end


function _fac_and_lift(f::fmpq_mpoly, p, degree_limit, lower_limit)
  Zx, x = PolynomialRing(FlintZZ, cached = false)
  Zmodpx = PolynomialRing(GF(p, cached = false), "y", cached = false)[1]
  fmodp = Zmodpx(f)
  fac = factor(fmodp)
  lifted_fac = Vector{Tuple{fmpz_poly, Int}}()
  for (k, v) in fac
    if degree(k) <= degree_limit && degree(k) >= lower_limit
      push!(lifted_fac, (lift(Zx, k), v))
    end
  end
  return lifted_fac
end

function is_pairwise_coprime(A::Vector{T}) where {T <: PolyElem}
  return is_squarefree(prod(A))
end

function _lift_p2(q, f::fmpz_poly, a::fq_nmod)
  Rx = base_ring(q)
  o = inv(derivative(f)(a))
  op = Rx()
  ap = Rx()
  for i=0:degree(parent(a))-1
    setcoeff!(op, i, coeff(o, i))
    setcoeff!(ap, i, coeff(a, i))
  end
  A = q(ap) - q(f(ap))*q(op)
  return A
end

function prime_dec_nonindex(O::NfAbsOrd{NfAbsNS,NfAbsNSElem}, p::IntegerUnion, degree_limit::Int = 0, lower_limit::Int = 0)

  K = nf(O)
  all_f = K.pol
  R = parent(all_f[1]) #we're non-simple, probably fmpq_mpoly

  if degree_limit == 0
    degree_limit = degree(K)
  end

  Fpx = PolynomialRing(GF(p, cached = false), cached = false)[1]
  R = ResidueRing(FlintZZ, p^2, cached = false)
  Rx = PolynomialRing(R, cached = false)[1]
  Zx = PolynomialRing(FlintZZ, cached = false)[1]

  fac = [_fac_and_lift(f, p, degree_limit, lower_limit) for f in all_f]
  all_c = [1 for f = all_f]
  re = elem_type(Fpx)[]
  rt = Vector{Vector{fq_nmod}}()
  RT = []
  RE = []
  while true
    re = elem_type(Fpx)[]
    RE = []
    #= TODO: this is suboptimal...
      k = Q[t]/(t^2-2, t^2-3, t^3-5), p = 11
      then splitting is [2], [1,1], [1,2]
      and I need 6 ideals of degree 2
      taking ony one root of the deg 2 factors gives a total of 4 ideals only
      I'd need 1 for the 1st factor, and 2 for the subsequent deg 2 factors.
      Why, I am not quite sure
      So I do all roots (which are too many) and sieve later.
    =#
    for x = Base.Iterators.product(fac...)
      k = lcm([degree(t[1]) for t = x])
      Fq = FiniteField(p, k, "y", cached = false)[1]
      Fq2 = ResidueRing(Rx, lift(Zx, minpoly(gen(Fq))))
      rt = Vector{Vector{elem_type(Fq)}}()
      RT = []
      d = 1
      for ti = 1:length(x)
        t = x[ti]
        g = gcd(d, degree(t[1]))
        d = lcm(d, degree(t[1]))
        r = roots(t[1], Fq)
        if g == 1
          push!(rt, [r[1]])
        else
          # I want only g roots! but I have f roots from an irreducible
          # poly of degree f
          #fundamentaly, I'd like to factor the poly over the field
          # so far (of degree d)
          # and choose one root for each factor.
          a = [r[1]]
          for i=1:g-1
            push!(a, frobenius(a[end]))
          end
          push!(rt, a)
        end
        push!(RT, [_lift_p2(Fq2, Zx(all_f[ti]), i) for i = rt[end]])
      end
      append!(re, [minpoly(Fpx, sum([rrt[i] * all_c[i] for i=1:length(all_c)])) for rrt in cartesian_product_iterator(rt, inplace = true)])
      append!(RE, [sum([rrt[i] * all_c[i] for i=1:length(all_c)]) for rrt in cartesian_product_iterator(RT), inplace = true])
    end
    if length(Set(re)) < length(re)
      all_c = [rand(1:p-1) for f = all_c]
      #can happen if index divisor, but unramified
      continue
      error("should not happen", p)
    end
    if sum(degree(x) for x = re) == degree(K)
      break
    end
    @show all_c = [rand(1:p-1) for f = all_c]
  end
  mu = [lift(Zx, re[i])(RE[i]) for i=1:length(re)]
  fac = [(lift(Zx, re[x]), 1, mu[x]) for x = 1:length(re) if lower_limit <= degree(re[x]) <= degree_limit]


  pe = sum([gens(K)[i] * all_c[i] for i=1:length(all_c)])

  result = Array{Tuple{ideal_type(O),Int}}(undef, length(fac))

  for k in 1:length(fac)
    fi = fac[k][1]
    ei = fac[k][2]

    b = fi(pe)
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

    #maybe: compute the roots of the f_i mod p^2 and evaluate the element..
    # this would check if elt is in p^2 everything being unramified

    if ei == 1 && iszero(fac[k][3])
      ideal.gen_two = ideal.gen_two + O(p)
    end

    ideal.gens_normal = fmpz(p)
    ideal.gens_weakly_normal = true

    if length(fac) == 1 && ideal.splitting_type[2] == degree(K)
      # Prime number is inert, in particular principal
      ideal.is_principal = 1
      ideal.princ_gen = O(p)
    end
    result[k] =  (ideal, ei)
  end
  return result

end

################################################################################
#
#  Approximation
#
################################################################################

# Returns x in O such that v_p(x) = v[i] for p = primes[i] and v_p(x) \geq 0 for all other primes.
# Assumes v[i] \geq 0 for all i.
# Algorithm 1.7.5 in Hoppe: Normal forms over Dedekind domains
function approximate_nonnegative(v::Vector{Int}, primes::Vector{T}) where { T <: Union{ NfAbsOrdIdl, NfRelOrdIdl } }
  @assert length(v) == length(primes)
  @assert length(primes) > 0

  O = order(primes[1])
  right_sides = Vector{elem_type(O)}(undef, length(primes))
  moduli = Vector{ideal_type(O)}(undef, length(primes))
  for i = 1:length(primes)
    @assert v[i] >= 0

    u = uniformizer(primes[i])
    right_sides[i] = u^v[i]
    moduli[i] = primes[i]^(v[i] + 1)
  end

  return crt(right_sides, moduli)
end

# Returns x in K such that v_p(x) = v[i] for p = primes[i].
# Valuations at other primes may be negative.
# Algorithm 1.7.6 in Hoppe: Normal forms over Dedekind domains
function approximate_simple(v::Vector{Int}, primes::Vector{T}) where { T <: Union{ NfAbsOrdIdl, NfRelOrdIdl } }
  a_pos, a_neg = _approximate_simple(v, primes)
  return divexact(elem_in_nf(a_pos), elem_in_nf(a_neg))
end

function _approximate_simple(v::Vector{Int}, primes::Vector{T}) where { T <: Union{ NfAbsOrdIdl, NfRelOrdIdl } }
  @assert length(v) == length(primes)
  @assert length(primes) > 0

  v_pos = zeros(Int, length(v))
  v_neg = zeros(Int, length(v))
  for i = 1:length(v)
    if v[i] < 0
      v_neg[i] = -v[i]
    else
      v_pos[i] = v[i]
    end
  end

  a_pos = approximate_nonnegative(v_pos, primes)
  a_neg = approximate_nonnegative(v_neg, primes)

  return a_pos, a_neg
end

# Returns x in K such that v_p(x) = v[i] for p = primes[i] and v_p(x) \geq 0 for all other primes p.
# Algorithm 1.7.8 in Hoppe: Normal forms over Dedekind domains
function approximate(v::Vector{Int}, primes::Vector{ <: NfAbsOrdIdl })
  @assert length(v) == length(primes)
  @assert length(primes) > 0

  O = order(primes[1])

  # Make the set primes complete: add all prime ideals lying over the same prime numbers
  prime_numbers = Set{fmpz}()
  for p in primes
    push!(prime_numbers, minimum(p, copy = false))
  end

  primes2 = Vector{ideal_type(O)}()
  for p in prime_numbers
    pdec = prime_decomposition(O, p)
    append!(primes2, [ pdec[i][1] for i = 1:length(pdec) ])
  end

  v2 = zeros(Int, length(primes2))

  D = Dict([ (primes[i], v[i]) for i = 1:length(primes) ])

  for i = 1:length(primes2)
    if haskey(D, primes2[i])
      v2[i] = D[primes2[i]]
    end
  end

  a_pos, a_neg = _approximate_simple(v2, primes2)

  # Take care of the additional negative valuations coming from a_neg^(-1)
  c = fmpq(norm(a_neg))
  for i = 1:length(primes)
    if v[i] >= 0
      continue
    end

    c *= fmpq(norm(primes[i]))^v[i]
  end

  return divexact(c*elem_in_nf(a_pos), elem_in_nf(a_neg))
end

# Return b in K with a \equiv b mod I and b_v >= 0 for v in pos_places
# Cohen, Advanced Topics in Computational Number Theory, Algorithm 4.2.20
function approximate(a::nf_elem, I::NfAbsOrdIdl, pos_places::Vector{InfPlc})
  F2 = GF(2)
  v = matrix(F2, length(pos_places), 1, [ is_positive(a, p) ? F2(0) : F2(1) for p in pos_places ])
  if all(iszero, v[:, 1])
    return a
  end
  bound = 5
  count = 1
  F2 = GF(2)
  M = zero_matrix(F2, length(pos_places), length(pos_places))
  betas = Vector{elem_type(order(I))}()
  r = 0
  while r != length(pos_places)
    count += 1
    b = 1 + rand(I, bound)
    N = deepcopy(M)
    for i = 1:length(pos_places)
      N[i, r + 1] = is_positive(b, pos_places[i]) ? F2(0) : F2(1)
    end
    rr = rank(N)
    if rr > r
      M = N
      r = rr
      push!(betas, b)
    end
    if count > 2^length(pos_places)*bound
      bound += 5
    end
  end

  w = inv(M)*v
  b = a
  for i = 1:nrows(w)
    if !iszero(w[i, 1])
      b *= betas[i]
    end
  end
  return b
end

################################################################################
#
#  Decomposition Group of a prime ideal
#
################################################################################

@doc Markdown.doc"""
    decomposition_group(P::NfOrdIdl; G::Vector{NfToNfMor}) -> Vector{NfToNfMor}

Given a prime ideal $P$ in a normal number field $G$, it returns a vector of the automorphisms $\sigma_1, \dots, \sigma_s$
such that $\sigma_i(P) = P$ for all $i = 1,\dots, s$.
If a subgroup $G$ of automorphisms is given, the output is the intersection of the decomposition group with that subgroup.
"""

function decomposition_group(P::NfOrdIdl; G::Vector{NfToNfMor} = NfToNfMor[],
                             orderG::Int = degree(P)*ramification_index(P))
  @assert is_prime(P)
  OK = order(P)
  K = nf(OK)
  if isempty(G)
    G = automorphisms(K, copy = false)
    if length(G) != degree(K)
      error("The field is not normal!")
    end
  end
  if is_index_divisor(OK, minimum(P, copy = false))
    q = 2
    R = ResidueRing(FlintZZ, q, cached = false)
    Rx = PolynomialRing(R, "x", cached = false)[1]
    fmod = Rx(K.pol)
    while iszero(discriminant(fmod))
      q = next_prime(q)
      R = ResidueRing(FlintZZ, q, cached = false)
      Rx = PolynomialRing(R, "x", cached = false)[1]
      fmod = Rx(K.pol)
    end
    D = Dict{nmod_poly, Int}()
    for i = 1:length(G)
      D[Rx(image_primitive_element(G[i]))] = i
    end
    dec_group = NfToNfMor[]
    local ppp
    let fmod = fmod
      function ppp(a::nmod_poly, b::nmod_poly)
        return compose_mod(a, b, fmod)
      end
    end
    for g in G
      if g in dec_group
        continue
      end
      y = OK(g(K(P.gen_two)), false)
      if y in P
        push!(dec_group, g)
        #I take the closure of dec_group modularly
        elems = nmod_poly[Rx(image_primitive_element(el)) for el in dec_group]
        new_elems = closure(elems, ppp, gen(Rx))
        dec_group = NfToNfMor[G[D[x]] for x in new_elems]
      end
      if length(dec_group) == orderG
        break
      end
    end
    return dec_group
  else
    res = decomposition_group_easy(G, P)
    return res
  end
end

function decomposition_group_easy(G, P)
  O = order(P)
  K = nf(O)
  R = ResidueRing(FlintZZ, Int(minimum(P, copy = false)), cached = false)
  Rt, t = PolynomialRing(R, "t", cached = false)
  fmod = Rt(K.pol)
  pols = nmod_poly[Rt(image_primitive_element(x)) for x in G]
  indices = Int[]
  second_gen = Rt(P.gen_two.elem_in_nf)
  if iszero(second_gen)
    return G
  end
  for i = 1:length(G)
    p1 = compose_mod(second_gen, pols[i], fmod)
    if iszero(p1) || iszero(mod(p1, second_gen))
      push!(indices, i)
    end
  end
  return G[indices]
end

@doc Markdown.doc"""
    decomposition_group(K::AnticNumberField, P::NfOrdIdl, m::Map)
                                                  -> Grp, GrpToGrp

Given a prime ideal $P$ of a number field $K$ and a map `m` return from
`automorphism_group(K)`, return the decompositon group of $P$ as a subgroup of
the domain of `m`.
"""
function decomposition_group(K::AnticNumberField, P::NfOrdIdl, mG::Map)
  iner = decomposition_group(P)
  return sub(domain(mG), [mG\a for a in iner])
end

################################################################################
#
#  Inertia subgroup of a prime ideal
#
################################################################################

@doc Markdown.doc"""
    inertia_subgroup(P::NfOrdIdl; G::Vector{NfToNfMor}) -> Vector{NfToNfMor}

Given a prime ideal $P$ in a normal number field, it returns a vector of the automorphisms $\sigma_1, \dots, \sigma_s$
such that $\sigma_i(P) = P$ for all $i = 1,\dots, s$ and induce the identity on the residue field.
If a subgroup $G$ of automorphisms is given, the output is the intersection of the inertia group with $G$.
"""

function inertia_subgroup(P::NfOrdIdl; G::Vector{NfToNfMor} = NfToNfMor[])
  @assert is_prime(P)
  O = order(P)
  K = nf(O)
  orderG = ramification_index(P)
  if isone(orderG)
    return NfToNfMor[id_hom(K)]
  end
  F, mF = ResidueField(O, P)
  if isempty(G)
    G = decomposition_group(P)
  end
  if !is_index_divisor(O, minimum(P, copy = false)) && fits(Int, minimum(P, copy = false))
    return inertia_subgroup_easy(F, mF, G)
  end
  gF = gen(F)
  igF = K(mF\gF)
  inertia_grp = NfToNfMor[]
  q = 2
  R = ResidueRing(FlintZZ, q, cached = false)
  Rx = PolynomialRing(R, "x", cached = false)[1]
  fmod = Rx(K.pol)
  while iszero(discriminant(fmod))
    q = next_prime(q)
    R = ResidueRing(FlintZZ, q, cached = false)
    Rx = PolynomialRing(R, "x", cached = false)[1]
    fmod = Rx(K.pol)
  end
  D = Dict{nmod_poly, Int}()
  for i = 1:length(G)
    D[Rx(image_primitive_element(G[i]))] = i
  end
  local ppp
  let fmod = fmod
    function ppp(a::nmod_poly, b::nmod_poly)
      return compose_mod(a, b, fmod)
    end
  end
  for g in G
    if g in inertia_grp
      continue
    end
    y = mF(O(g(igF), false))
    if y == gF
      push!(inertia_grp, g)
      elems = nmod_poly[Rx(image_primitive_element(el)) for el in inertia_grp]
      new_elems = closure(elems, ppp, gen(Rx))
      inertia_grp = NfToNfMor[G[D[x]] for x in new_elems]
      if length(inertia_grp) == orderG
        break
      end
    end
  end
  return inertia_grp
end

function inertia_subgroup_easy(F, mF, G::Vector{NfToNfMor})
  P = mF.P
  OK = order(P)
  K = nf(OK)
  p = minimum(P, copy = false)
  R = ResidueRing(FlintZZ, Int(p), cached = false)
  Rt = PolynomialRing(R, "t", cached = false)[1]
  fmod = Rt(K.pol)
  gF = gen(F)
  igF = K(mF\gF)
  igFq = Rt(igF)
  indices = Int[]
  for i = 1:length(G)
    g = G[i]
    img = Rt(image_primitive_element(g))
    res = compose_mod(igFq, img, fmod)
    resK = OK(lift(K, res), false)
    if mF(resK) == gF
      push!(indices, i)
    end
  end
  return G[indices]
end

@doc Markdown.doc"""
    inertia_subgroup(K::AnticNumberField, P::NfOrdIdl, m::Map) -> Grp, GrpToGrp

Given a prime ideal $P$ of a number field $K$ and a map `m` return from
`automorphism_group(K)`, return the intertia subgroup of $P$ as a subgroup of
the domain of `m`.
"""
function inertia_subgroup(K::AnticNumberField, P::NfOrdIdl, mG::Map)
  iner = inertia_subgroup(P)
  return sub(domain(mG), [mG\a for a in iner])
end

################################################################################
#
#  Ramification groups
#
################################################################################

function ramification_group(P::NfOrdIdl, i::Int)
  if i == 0
    return inertia_subgroup(P)
  end
  A = inertia_subgroup(P)
  pi = uniformizer(P)
  res = NfToNfMor[]
  a = elem_in_nf(pi)
  for f in A
    b = f(a)
    if b == a || valuation(b - a, P) >= i + 1
      push!(res, f)
    end
  end
  return res
end

@doc Markdown.doc"""
    ramification_group(K::AnticNumberField, P::NfOrdIdl, m::Map) -> Grp, GrpToGrp

Given a prime ideal $P$ of a number field $K$ and a map `m` return from
`automorphism_group(K)`, return the ramification group of $P$ as a subgroup of
the domain of `m`.
"""
function ramification_group(K::AnticNumberField, P::NfOrdIdl, i::Int, mG::Map)
  iner = ramification_group(P, i)
  return sub(domain(mG), [mG\a for a in iner])
end
