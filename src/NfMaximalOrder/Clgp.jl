################################################################################
#
#     Clgrp.jl : Class group computation of maximal orders in number fields
#
# This file is part of hecke.
#
# Copyright (c) 2015: Claus Fieker, Tommy Hofmann
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
# (C) 2015 Claus Fieker
#
################################################################################
#
# Todo: 
#  - make sure the precision for LLL is high enough (by checking that the
#    resulting elements have a reasonable norm/ length? theory?)
#    done
#  - add reasonable verbose printing
#    done
#  - write hnf from upper_triangular
#  - understand/use profiling information (memory, ...)     
#
#  - need different norm function: modular resultant? with a large known
#    factor AND without any proof...
#    otherwise, it takes much too long if the ideal is non-trivial
#  DONE (norm_div)
#
#  - move the various factor, is_smooth and similar to a sensible
#    spot. This has nothing to do with class groups
#  - the SingleP version: 
#      figure out if a union is better than the current version
#      ie have a version for easy primes
#         and a dumb version as fallback
#      make sure stuff works with fractionals as well!
#      just scaling by the den can affect smoothness (incomplete factor base)
#
#
# Clean up:
#  - sort the various data-types files
#  - write show functions
#  - remove debugging prints
#  - arrange the functions in e.g. Sparse in a reasonable order
#  - rename some of them
#  - export 
#  - use iterators in add_scaled and transform?
#
# Note: enumerating x,0,0,0 is pointless unless x==1
#
################################################################################

export class_group, FactorBase, is_smooth, factor

add_verbose_scope(:ClassGroup)
add_verbose_scope(:ClassGroup_time)
add_verbose_scope(:ClassGroup_gc)

add_assert_scope(:ClassGroup)
set_assert_level(:ClassGroup, 1)
set_assert_level(:LatEnum, 1)


################################################################################
#
#  Factor base over (Euclidean) Rings
#
################################################################################

# Note that T must admit gcd's and base must consist of elements x for which
# valuation(_, x) is definied.
# works (at least) for fmpz and nmod_poly, so it can be used for the
# smoothness test

function compose{T}(a::node{T}, b::node{T})
  return node{T}(a.content * b.content, a, b)
end

# assume that the set consists of pairwise coprime elements
function FactorBase{T}(x::Set{T}; check::Bool = true)
  ax = [ node{T}(p) for p in x]
  while length(ax) > 1
    if check && !isone(gcd(ax[2*i-1], ax[2*i]))
      error("input not coprime")
    end  
    bx = [ compose(ax[2*i-1], ax[2*i]) for i=1:div(length(ax), 2)]
    if isodd(length(ax))
      push!(bx, ax[end])
    end
    ax = bx
  end
  z = FactorBase{T}(ax[1].content, x)
  z.ptree = ax[1]
  return z
end

function show{T}(io::IO, B::FactorBase{T})
  print(io, "Factor base with \n$(B.base) and type $T")
end

function is_smooth{T}(c::FactorBase{T}, a::T)
  @assert a != 0
  g = gcd(c.prod, a)
  while g != 1 
    a = div(a, g)
    g = gcd(g, a)
  end
  return a == 1 || a==-1, a
end

function isleaf{T}(a::node{T})
  return !(isdefined(a, :left) || isdefined(a, :right))
end

function _split{T}(c::node{T}, a::T)
  if isleaf(c)
    return [gcd(a, c.content)]
  end
  if isdefined(c, :left)
    l = gcd(a, c.left.content)
    if l != 1
      ls = _split(c.left, l)
    else
      ls = Array{T, 1}()
    end
  else
    ls = Array{T, 1}()
  end
  if isdefined(c, :right)
    r = gcd(a, c.right.content)
    if r != 1 
      rs = _split(c.right, r)
    else
      rs = Array{T, 1}()
    end
  else
    rs = Array{T, 1}()
  end
  return vcat(ls, rs)
end

function factor{T}(c::FactorBase{T}, a::T)
  @assert a != 0
  f = Dict{T, Int}()
  lp = _split(c.ptree, a)
  for i in lp
    if mod(a, i)==0  ## combine: use divmod and do val of rest
                     ## to save a division
      v = valuation(a, i)
      f[i] = v[1]
      a = v[2]
      if a == 1 || a==-1  ## should be is_unit (think poly)
        break
      end
    end
  end
  assert(a==1 || a==-1)
  return f
end

function factor{T}(c::FactorBase{T}, a::fmpq)  ## fractions over T
  @assert a != 0
  f = Dict{T, Int}()
  n = abs(num(a))
  d = den(a)
  lp = _split(c.ptree, n*d)
  for i in lp
    if mod(d, i)==0
      v = valuation(d, i)
      if isdefined(f, :i)
        f[i] -= v[1]
      else
        f[i] = -v[1]
      end
      d = v[2]
      if d == 1 && n == 1
        break
      end
    end
    if mod(n, i)==0
      v = valuation(n, i)
      if isdefined(f, :i)
        f[i] += v[1]
      else
        f[i] = v[1]
      end
      n = v[2]
      if d == 1 && n==1
        break
      end
    end
  end
  @hassert :ClassGroup 1 d == 1 && n == 1 
  return f
end

################################################################################
#
#  NfFactorBase : Factor bases for number fields 
#  A factor basis is mostly a collection of prime ideals, designed,
#  if possible, to allow for rapid testing if elements are smooth.
#
################################################################################

function NfFactorBase(O::NfMaximalOrder, B::Int;
                      complete::Bool = true, degree_limit::Int = 5)
  @vprint :ClassGroup 2 "Splitting the prime ideals ...\n"
  lp = prime_ideals_up_to(O, B, complete = complete,
                          degree_limit = degree_limit)
  @vprint :ClassGroup 2 " done \n"
  lp = sort(lp, lt = function(a,b) return norm(a) > norm(b); end)
  FB = NfFactorBase()
  FB.size = length(lp)
  FB.ideals = lp

  # Magic constant 20?
  FB.rw = Array(Int, 20)
  FB.mx = 20

  for i = 1:length(lp)
    if !haskey(FB.fb, lp[i].gen_one)
      FB.fb[lp[i].gen_one] = [(i, lp[i])]
    else
      push!(FB.fb[lp[i].gen_one], (i, lp[i]))
    end
  end

  FB.fb_int = FactorBase(Set(keys(FB.fb)); check = false)

  return FB
end

################################################################################
#
#  Factor number field element over factor base. Put valuations into row i of
#  the relation matrix M. The matrix M needs to have at least as many columns
#  as the FB has ideals.
#
################################################################################

function factor!{T}(M::Smat{T}, i::Int, FB::NfFactorBase, a::nf_elem;
                    error = true, n = abs(norm(a)))
  return _factor(M, i, FB, a, error, n)
end


type FactorBaseSingleP
  P::fmpz
  pt::FactorBase{nmod_poly}
  lp::Array{Tuple{Int,NfMaximalOrderIdeal}, 1}
  doit::Function
  
  function FactorBaseSingleP(p::fmpz, lp::Array{Tuple{Int, NfMaximalOrderIdeal}, 1})
    FB = new()
    FB.lp = lp
    FB.P = p

    if length(lp) < 3 ##  || is_difficult(p) # ie. index divisor or so
      FB.doit = function(a::nf_elem, v::Int)
        r = Array{Tuple{Int, Int},1}()
        for x=1:length(lp)
          vl = valuation(a, lp[x][2])
          v -= vl*lp[x][2].splitting_type[2]
          push!(r, (lp[x][1], vl))
        end  
        return r, v
      end
    else
      Zx = PolynomialRing(ZZ, "x")[1]
      Fpx = PolynomialRing(ResidueRing(ZZ, p), "x")[1]
      O = order(lp[1][2])
      K = O.nf
      Qx = parent(K.pol)
      fp = Fpx(Zx(K.pol))
      lf = [ gcd(fp, Fpx(Zx(Qx(K(P[2].gen_two)))))::nmod_poly for P = lp]

      FB.pt = FactorBase(Set(lf), check = false)
      FB.doit = function(a::nf_elem, v::Int)
          g = Fpx(Zx(Qx(a)))
          g = gcd(g, fp)
          fl = is_smooth(FB.pt, g)[1]
          if fl
            d = factor(FB.pt, g)
            r = Array{Tuple{Int, Int}, 1}()
            vv=v
            for x in keys(d)
              id = findfirst(lf, x)
              vv -= FB.lp[id][2].splitting_type[2]
              push!(r, (FB.lp[id][1], 1))
            end
            if vv == 0
              return r, vv
            end
            r = Array{Tuple{Int, Int}, 1}()
            for x in keys(d)
              id = findfirst(lf, x)
              vl  = valuation(a, lp[id][2])
              v -= FB.lp[id][2].splitting_type[2]*vl
              push!(r, (FB.lp[id][1], vl))
            end
            return r, v
          else
            return Array(Tuple{Int, Int}, 1)()
          end
        end  
    end
    return FB
  end
end  

function _factor!{T}(M::Smat{T}, i::Int, FB::NfFactorBase, a::nf_elem,
                    error::Bool = true, n::fmpq = abs(norm(a)))
  d = factor(FB.fb_int, num(n)*den(a))
  rw = FB.rw
  lg::Int = 0
  for p in keys(d)
    vp = valuation(n, p)[1]
    for (j, P) in FB.fb[p]  ## TODO: use a poly factor base for
                            ## non-index divisors to speed this up
                            ## totally split primes in large degree 
                            ## fields are otherwise a pain
                            ## ie. the structure above!
      v = valuation(a, P)
      if v != 0
        vp -= P.splitting_type[2]*v
        lg += 1
        if lg <= FB.mx
          rw[lg] = j
          rw[lg + 1] = v
        else
          push!(rw, j)
          push!(rw, v)
        end
        lg += 1
      end
    end
    if vp != 0
      if error
        @hassert :ClassGroup 1 vp == 0
      end
      return false
    end
  end
  if lg > 0
    if length(rw) > FB.mx
      FB.mx = length(rw)
    end
    @hassert :ClassGroup lg > 1
    @hassert :ClassGroup iseven(lg)
    nrw = Array{Tuple{Int, Int}}(div(lg, 2))
    for i = 1:div(lg, 2)
      nrw[i] = (rw[2*(i-1)+1], rw[2*i])
    end
    sort!(nrw, lt=function(a,b) return a[1] < b[1]; end)
    @hassert :ClassGroup 1 length(nrw) > 0
    push!(M, SmatRow{T}(nrw))
    return true
  else 
    # factor failed or I have a unit.
    # sparse rel mat must not have zero-rows.
    return false
  end
end

function factor(FB::NfFactorBase, a::nf_elem)
  M = MatrixSpace(FlintZZ, 1, FB.size)()
  factor!(M, 1, FB, a)
  return M
end

function show(io::IO, I::IdealRelationsCtx)
  println(io, "IdealRelationCtx for ", I.A)
  println(io, "  current length bound ", I.c, " stats: ", I.cnt, " and ", I.bad)
end


################################################################################
#
#  The main class group part
#
################################################################################

global AllRels
function class_group_init(O::NfMaximalOrder, B::Int;
                          complete::Bool = true, degree_limit::Int = 0, T::DataType = Smat{fmpz})
  global AllRels = []
  clg = ClassGrpCtx{T}()

  if degree_limit == 0 
    degree_limit = degree(O)
  end

  clg.bad_rel = 0
  clg.rel_cnt = 0
  clg.last = 0

  @vprint :ClassGroup 2 "Computing factor base ... "
  clg.FB = NfFactorBase(O, B, complete = complete, degree_limit = degree_limit)
  @vprint :ClassGroup 2 " done\n"
  clg.M = T()
  clg.c = conjugates_init(nf(O).pol)
  for I in clg.FB.ideals
    a = nf(O)(I.gen_one)
    class_group_add_relation(clg, a, abs(norm(a)), fmpz(1))
    a = nf(O)(I.gen_two)
    class_group_add_relation(clg, a, abs(norm(a)), fmpz(1))
  end
  n = degree(O)
  l = MatrixSpace(FlintZZ, n, 1+clg.c.r2)()
  for i = 1:n
    l[i,1] = 1
  end
  for i = 1:clg.c.r2
    l[clg.c.r1+2*i, i+1] = 1
    l[clg.c.r1+2*i-1, i+1] = -1
  end
  # what I want is a lll-reduced basis for the kernel
  # it probably should be a sep. function
  # however, there is nullspace - which is strange...
  l,t = hnf_with_transform(l)
  t = sub(t, (1+clg.c.r2+1):rows(l), 1:rows(l))
  l = lll(t)
  clg.val_base = l
  return clg
end

#=
  should probably just use an integer as hash: p*root of poly

  so a is an integral element where the norm is almost smooth, it means
  norm(a) = prod over factor base * p
  where p is a prime.
  This means
  <p, a> is a prime ideal of norm p hence of degree 1
  if p is no index divisor, then <p,a> = <p, b> where
  b is a linear factor of f, the defining polynomial, mod p.
  I can compute b as gcd(a, f) of course.
  =#
function special_prime_ideal(p::fmpz, a::nf_elem)
  K = parent(a)
  f = K.pol
  R = parent(f)
  Zx = PolynomialRing(ZZ, "\$x_z")[1]
  Zf = Zx(f)
  Zpx = PolynomialRing(ResidueRing(ZZ, p), "\$x_p")[1]
  Za = Zx(parent(f)(a*den(a)))
  g = gcd(Zpx(Zf), Zpx(Za))
  return lift(Zx, g)
end

function israt(a::nf_elem)
  @assert degree(parent(a))>2 ## fails for deg1 and 2 due to efficiency
  return a.elem_length<2
end

function class_group_add_relation{T}(clg::ClassGrpCtx{T}, a::nf_elem, n::fmpq, nI::fmpz)
  if a==0
    return false
  end
  if a in clg.RS 
    return false
  end
  #print("trying relation of length ", Float64(length(clg.c, a)),
  #      " and norm ", Float64(n));
  fl, r = is_smooth(clg.FB.fb_int, num(n*nI)*den(a))
  if !fl
    # try for large prime?
    if isprime(r) && abs(r) < clg.B2
      i = special_prime_ideal(r, a)
      if haskey(clg.largePrime, i)
        lp = clg.largePrime[i]
        b = a//lp[1]
        fl = class_group_add_relation(clg, b, n*nI//lp[2], fmpz(1))
        if fl 
          clg.largePrime_success += 1
        else
          clg.largePrime_no_success += 1
        end
      else
        clg.largePrime[i] = (a, n*nI)
        push!(clg.relPartialNorm, (a, nI))
      end
      clg.largePrimeCnt += 1
    else
      clg.bad_rel += 1
    end
    #println(" -> fail")
    return false
  end
  if _factor!(clg.M, length(clg.R)+1, clg.FB, a, false, n*nI)
    push!(clg.R, a)
    push!(clg.RS, a)
    @hassert :ClassGroup 1 rows(clg.M) == length(clg.R)
    clg.rel_cnt += 1
    @v_do :ClassGroup 1 println(" -> OK, rate currently ",
           clg.bad_rel/clg.rel_cnt, " this ", clg.bad_rel - clg.last)
    clg.last = clg.bad_rel
    push!(clg.relNorm, (a, nI))
    return true
  else
    #println(" -> 2:fail")
    clg.bad_rel += 1
    return false
  end
end

################################################################################
#
#  Naive relation search: Based on coefficient size only
#
################################################################################

function class_group_random_ideal_relation(clg::ClassGrpCtx, r::Int,
                                           I::NfMaximalOrderIdeal = rand(clg.FB.ideals))
  s = 1
  if r < 2
    r = 2
  end
  for i = 1:r 
    I = I*rand(clg.FB.ideals)
    I, g = reduce_ideal_class(I)
    s *= g
  end
  return s;
end 

################################################################################
#
# Naive relation search: Tries random linear combinations of lll reduced basis
# The lll is done on the coefficient lattice.   
#
################################################################################
function class_group_small_elements_relation(clg::ClassGrpCtx,
                A::NfMaximalOrderIdeal, cnt::Int = degree(order(A)))
  l = FakeFmpqMat(lll(basis_mat(A)))*basis_mat(order(A))
  K = nf(order(A))
  if cnt <= degree(A.parent.order)
    lb = Array(nf_elem, degree(K))
    for i = 1:cnt
      lb[i] = elem_from_mat_row(K, l.num, i, l.den)
    end
    return lb
  end
  r = Int(ceil((2*cnt)^(1/degree(K))))
  r = -div(r+1, 2):div(r+1, 2)
  ll = Array(typeof(K()), degree(K))
  for i = 1:degree(K)
    ll[i] = elem_from_mat_row(K, l.num, i, l.den)
  end
  lb = Array(typeof(K()), cnt)
  for i = 1:cnt
    lb[i] = rand(ll, r)
  end
  return lb
end

################################################################################
#
# More interesting search: Enumeration and other things on the minkowski side
#
################################################################################

#scales the i-th column of a by 2^d[1,i]
function mult_by_2pow_diag!(a::Array{BigFloat, 2}, d::fmpz_mat)
  s = size(a)
  R = RealRing()
  tmp_mpz = R.z1
  for i = 1:s[1]
    for j = 1:s[2]
      e = ccall((:mpfr_get_z_2exp, :libmpfr), Clong, (Ptr{BigInt}, Ptr{BigFloat}), &tmp_mpz, &a[i,j])
      ccall((:mpfr_set_z_2exp, :libmpfr), Void, (Ptr{BigFloat}, Ptr{BigInt}, Clong, Int32), &a[i,j], &tmp_mpz, e+Clong(d[1,j]), Base.MPFR.ROUNDING_MODE[end])
    end
  end
end

#converts BigFloat -> fmpz via round(a*2^l), in a clever(?) way
function round_scale(a::Array{BigFloat, 2}, l::Int)
  s = size(a)
  b = MatrixSpace(FlintZZ, s[1], s[2])()
  R = RealRing()
  tmp_mpz = R.z1
  tmp_fmpz = R.zz1
  tmp_mpfr = R.t1
  for i = 1:s[1]
    for j = 1:s[2]
      e = a[i,j].exp
      a[i,j].exp += l
      ccall((:mpfr_round, :libmpfr), Int32, (Ptr{BigFloat}, Ptr{BigFloat}, Int32), &tmp_mpfr, &a[i,j], Base.MPFR.ROUNDING_MODE[end]) 
      a[i,j].exp = e
      f = ccall((:mpfr_get_z_2exp, :libmpfr), Clong, (Ptr{BigInt}, Ptr{BigFloat}),
        &tmp_mpz, &tmp_mpfr)
      ccall((:fmpz_set_mpz, :libflint), Void, (Ptr{fmpz}, Ptr{BigInt}),
        &tmp_fmpz, &tmp_mpz)
      if f > 0  
        ccall((:fmpz_mul_2exp, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Culong), &tmp_fmpz, &tmp_fmpz, f)
      else
        ccall((:fmpz_tdiv_q_2exp, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Culong), &tmp_fmpz, &tmp_fmpz, -f);
      end
      setindex!(b, tmp_fmpz, i, j)
    end
  end
  return b
end

function shift!(g::fmpz_mat, l::Int)
  for i=1:rows(g)
    for j=1:cols(g)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &g, i-1, j-1)
      if l > 0
        ccall((:fmpz_mul_2exp, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Int), z, z, l)
      else
        ccall((:fmpz_tdiv_q_2exp, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Int), z, z, -l)
      end
    end
  end
  return g
end
 
function lll(rt_c::roots_ctx, A::NfMaximalOrderIdeal, v::fmpz_mat;
                prec::Int = 100)
  c = minkowski_mat(rt_c, nf(order(A)), prec) ## careful: current iteration
                                              ## c is NOT a copy, so don't change.
  l, t1 = lll_with_transform(basis_mat(A))
  b = FakeFmpqMat(l)*basis_mat(order(A))
  if !isdefined(rt_c, :cache)
    rt_c.cache = 0*c
  end
  d = rt_c.cache
  mult!(d, b.num, c)
  if !iszero(v)
    @v_do :ClassGroup 2 println("using inf val", v)
    old = get_bigfloat_precision()
    set_bigfloat_precision(4*prec)
    mult_by_2pow_diag!(d, v);
    set_bigfloat_precision(old)
  end
  old = get_bigfloat_precision()
  set_bigfloat_precision(prec)
  g = round_scale(d, prec)
  @hassert :ClassGroup 1 !iszero(g)
  set_bigfloat_precision(old)
  g = g*g'
  shift!(g, -prec)
  g += rows(g)*one(parent(g))

  l, t = lll_gram_with_transform(g)
  ## test if entries in l are small enough, if not: increase precision
  ## or signal that prec was too low
  @v_do :ClassGroup 2 print_with_color(:green, "lll basis length profile\n");
  @v_do :ClassGroup 2 for i=1:rows(l)
    print(div(l[i,i], fmpz(2)^prec), " : ")
  end
  @v_do :ClassGroup 2 println("")
  if nbits(max(t)) >  div(prec, 2)
    print_with_color(:red, "lll trafo too large\n");
    throw(LowPrecisionLLL())
  end
  ## lattice has lattice disc = order_disc * norm^2
  ## lll needs to yield a basis sth
  ## l[1,1] = |b_i|^2 <= 2^((n-1)/2) disc^(1/n)  
  ## and prod(l[i,i]) <= 2^(n(n-1)/2) disc
  n = rows(l)
  den = basis_mat(order(A)).den
  disc = abs(discriminant(order(A)))*norm(A)^2 * den^(2*n)
  d = root(disc, n)+1
  d *= fmpz(2)^(div(n+1,2)) * fmpz(2)^prec
  pr = fmpz(1)
  if l[1,1] > d 
    print_with_color(:red, "LLL basis too large\n");
    println("bound is ", d, " value at ", 1, " is ", l[1,1]); 
    throw(LowPrecisionLLL())
  end
  for i=1:n
    pr = pr*l[i,i]
  end  
  if pr > fmpz(2)^(div(n*(n-1), 2)) * disc * fmpz(2)^(n*prec)
    print_with_color(:red, "LLL basis too large\n");
    println("prod too large: ", pr, " > 2^(n(n-1)/2) disc = ", fmpz(2)^(div(n*(n-1), 2)) * disc * fmpz(2)^(n*prec));
    throw(LowPrecisionLLL())
  end

  return l, t*t1
end

################################################################################
#
#  Algorithm of Schmettow
#
################################################################################

function one_step(c::roots_ctx, b::NfMaximalOrderFracIdeal,
                p::NfMaximalOrderIdeal; prec::Int = 100)
  b = p*b
  simplify(b)
  g1 = short_elem(c, b, prec = prec)
  b = g1*inv(b) 
  simplify(b)
  g2 = short_elem(c, b, prec = prec) 
  return simplify(g2*inv(b)), g1, g2
end

function short_elem(c::roots_ctx, A::NfMaximalOrderFracIdeal,
                v::fmpz_mat=MatrixSpace(FlintZZ, 1,1)(); prec::Int = 100)
  return divexact(short_elem(c, A.num, v, prec = prec), A.den)
end

function short_elem(c::roots_ctx, A::NfMaximalOrderIdeal,
                v::fmpz_mat = MatrixSpace(FlintZZ, 1,1)(); prec::Int = 100)
  K = nf(order(A))
  temp = FakeFmpqMat(basis_mat(A))*basis_mat(order(A))
  b = temp.num
  b_den = temp.den
  l, t = lll(c, A, v, prec = prec)
  w = window(t, 1,1, 1, cols(t))
  c = w*b
  q = elem_from_mat_row(K, c, 1, b_den)
  return q
end

################################################################################
#
################################################################################

function enum_ctx_from_ideal(c::roots_ctx, A::NfMaximalOrderIdeal,
                v::fmpz_mat;prec::Int = 100, limit::Int = 0, Tx::DataType = Int, TU::DataType = Float64, TC::DataType = Float64)
  l, t = lll(c, A, v, prec = prec)
  temp = FakeFmpqMat(basis_mat(A))*basis_mat(order(A))
  b = temp.num
  b_den = temp.den
  K = nf(order(A))
  if limit == 0
    limit = rows(l)
  end
 
  E = enum_ctx_from_gram(l, FlintZZ(2)^prec, Tx = Tx, TC = TC, TU = TU,
                  limit = limit)::enum_ctx{Tx, TC, TU}
  E.t = t*b
  E.t_den = b_den
  ## we want to find x sth. norm(x) <= sqrt(|disc|)*norm(A)
  ## |N(x)^2|^(1/n) <= T_2(x)/n 
  ## so if T_2(x) <= n * D^(1/n)
  ## then |N(x)| <= D^(1/2)
  d = abs(discriminant(order(A))) * norm(A)^2
  ## but we don't want to overshoot too much the length of the last
  ## basis element.
  den = basis_mat(order(A)).den ## we ignore the den above, but this
                                ## changes the discriminant!!!
  b = min(den^2 * (root(d, E.n)+1)*E.n * E.d, E.G[E.limit, E.limit]*E.limit)
  @v_do :ClassGroup 2 println("T_2 from disc ", (root(d, E.n)+1)*E.n * E.d)
  @v_do :ClassGroup 2 println("    from Gram ", E.G[E.limit, E.limit]*E.limit)
  @v_do :ClassGroup 2 println(" using ", b)
  enum_ctx_start(E, b)
  return E
end

global _start = 0.0
function class_group_small_real_elements_relation_start(clg::ClassGrpCtx,
                A::NfMaximalOrderIdeal; prec::Int = 200, val::Int = 0,
                limit::Int = 0)
  global _start
  @v_do :ClassGroup_time 2 rt = time_ns()
  I = IdealRelationsCtx{Int, Float64, Float64}(clg, A, prec = prec, val = val, limit = limit)
  @v_do :ClassGroup_time 2 _start += time_ns()-rt
  return I
end

global _elt = Uint(0)

function class_group_small_real_elements_relation_next(I::IdealRelationsCtx)
  global _elt, _next
  K = nf(order(I.A))
  while true
    if enum_ctx_next(I.E)
      # println("elt is", I.E.x)
      # should we (again) add content_is_one()?
      if !isone(content(I.E.x))
        continue
      end
      @v_do :ClassGroup_time 2 rt = time_ns()
#      I.M = I.E.x * I.E.t
      ccall((:fmpz_mat_mul, :libflint), Void, (Ptr{fmpz_mat}, Ptr{fmpz_mat}, Ptr{fmpz_mat}), &I.M, &I.E.x, &I.E.t)
      q = elem_from_mat_row(K, I.M, 1, I.E.t_den)
      #println("found ", q, " norm ", norm(q)//norm(I.A))
      @v_do :ClassGroup_time 2 _elt += time_ns()- rt
      return q
    end
    @v_do :ClassGroup 2 print_with_color(:red, "restart after ")
    @v_do :ClassGroup 2 print(I.E.cnt)
    @v_do :ClassGroup 3 println(" for ", I.A, I.E.c)
    @v_do :ClassGroup 2 println(" length now ", I.E.c*2)
#    throw(NoElements())
    I.restart += 1
    if I.restart > 10
      _elt = I
      error("too much restarting");
    end
    enum_ctx_start(I.E, I.E.c*2)
  end
end

# Do better: re-use partial hnf, check rank mod p, ...

const modu = next_prime(2^20)
function class_group_current_result(clg::ClassGrpCtx)
  global modu
  full_rank = false
  if isdefined(clg, :H)
    full_rank = rows(clg.H) == cols(clg.H)
    new_rel = sub(clg.M, (clg.last_H+1):rows(clg.M), 1:cols(clg.M))
    last_diag = [clg.H[i,i] for i =1:min(rows(clg.H), cols(clg.H))]
    vcat!(clg.H, new_rel)
    h = clg.H
    t = time_ns()
    if clg.H_is_modular
      upper_triangular(h, mod = modu)
      if rows(h) == cols(h)
        h = copy(clg.M)
        println("1st non modular hnf")
        upper_triangular(h)
        clg.H_is_modular = false
        full_rank = true
      end
    else
      upper_triangular(h)
    end
    clg.hnf_time += time_ns()-t
    clg.hnf_call += 1
    diag = [clg.H[i,i] for i =1:min(rows(clg.H), cols(clg.H))]
#=    
we do need redundant relations for the units.
=#    
    if diag == last_diag
      deleteat!(clg.M.rows, (clg.last_H+1):length(clg.R))
      deleteat!(clg.R, (clg.last_H+1):length(clg.R))
      clg.M.r = length(clg.M.rows)
      @vprint :ClassGroup 1 "pruning again...\n"
    end
  else
    full_rank = false
    t = time_ns()
    h = sub(clg.M, 1:clg.M.r, 1:clg.M.c)
    if clg.H_is_modular
      upper_triangular(h, mod = modu)
      if rows(h) == cols(h)
        h = copy(clg.M)
        println("1st non modular hnf")
        upper_triangular(h)
        clg.H_is_modular = false
        full_rank = true
      end
    else
      upper_triangular(h)
    end
    clg.hnf_time += time_ns()-t
    clg.hnf_call += 1
    last_H = 0
  end
  @v_do :ClassGroup 1 println("rank is currently ", rows(h), " need to be ",
                  cols(h), " mat is ", clg.M)
  clg.H = h
  clg.last_H = length(clg.R)
  if length(clg.R)/rows(h) > 4
    print_with_color(:yellow, "not enough useful relations\n")
  end
    
  piv = Array(Int, 0)
  if full_rank
    for i = h.rows
      if abs(i.entry[1].val) == 1
        push!(piv, i.entry[1].col)
      end
    end
  else
    for i = h.rows
      push!(piv, i.entry[1].col)
    end
  end
  mis = setdiff(Set(1:cols(h)), Set(piv))

  if !full_rank
    clg.mis = mis
    clg.h = FlintZZ(0)
    return (fmpz(0), mis)::Tuple{fmpz, Set{Int}}
  end

  if full_rank
    clg.h = FlintZZ(abs(prod([h[i,i] for i=1:cols(h)])))
  end

  clg.mis = mis
  return (clg.h, clg.mis)::Tuple{fmpz, Set{Int}}
end

################################################################################
#
#  Main loop to find relations
#
################################################################################

global last_E
function class_group_find_relations(clg::ClassGrpCtx; val = 0, prec = 100,
                limit = 10)
  clg.hnf_time = 0.0
  clg.hnf_call = 0
  clg.rel_cnt = 0
  clg.bad_rel = 0

  n = degree(clg.FB.ideals[1].parent.order)
  t = time_ns()
  I = []
  O = parent(clg.FB.ideals[1]).order
  sqrt_disc = isqrt(abs(discriminant(O)))
  np = Int(ceil(nbits(sqrt_disc)/Base.GMP.GMP_BITS_PER_LIMB)+1)

  f = 0

  for i in clg.FB.ideals
    OK = false
    while !OK
      try
        f = class_group_small_real_elements_relation_start(clg, i, limit = limit,
                        prec = prec, val = val)
        OK = true                
      catch e
        if isa(e, LowPrecisionCholesky)
          print_with_color(:red, "prec too low in cholesky,")
          prec = Int(ceil(1.2*prec))
          println(" increasing to ", prec)
          if prec > 1000
            error("1:too much prec")
          end
        elseif isa(e, LowPrecisionLLL)
          print_with_color(:red, "prec too low in LLL,")
          prec = Int(ceil(1.2*prec))
          println(" increasing to ", prec)
          if prec > 1000
            error("2:too much prec")
          end
        else
          rethrow(e)
        end
      end
    end  

    push!(I, f)
    f.vl = val
    while true
      e = class_group_small_real_elements_relation_next(I[end])
      n = abs(norm_div(e, norm(I[end].A), np))
      if n==0 || e==0
        println("found ", e, " of norm ", n)
        global AllRels = I[end]
      end
#        print_with_color(:blue, "norm OK:")
#        println(n//norm(I[end].A), " should be ", sqrt_disc)
      if n > sqrt_disc
#        prec = Int(ceil(prec*1.2))
        print_with_color(:red, "norm too large:")
        println(n, " should be ", sqrt_disc)
        println("offending element is ", e)
#        println("offending ideal is ", I[end].A)
        println("skipping ideal (for now)")
        break
      end
      f = class_group_add_relation(clg, e, n, norm(I[end].A))
#      global AllRels
#      push!(AllRels, (e, n))
      if f
        I[end].cnt += 1
        break
      else
        I[end].bad += 1
        if I[end].bad > (clg.bad_rel/clg.rel_cnt)*2
          @v_do :ClassGroup 2 println("too slow in getting s.th. for ", i,
                          "\ngood: ", I[end].cnt,  " bad: ",  I[end].bad,
                          " ratio: ", (clg.bad_rel/clg.rel_cnt))
          break
        end
      end
    end
    @v_do :ClassGroup_gc 1 gc()
    if cols(clg.M) < rows(clg.M)*1.1
      @vprint :ClassGroup 1 println("rel mat probably full rank, leaving phase 1");
      while length(I) < length(clg.FB.ideals)
        push!(I, class_group_small_real_elements_relation_start(clg, clg.FB.ideals[length(I)+1], limit = limit, prec = prec, val = val))
      end
      break
    end
  end

  @v_do :ClassGroup 1 println("used ", (time_ns()-t)/1e9,
                  " sec for small elts, so far ", clg.hnf_time/1e9,
                  " sec for hnf in ", clg.hnf_call, " calls");
  @v_do :ClassGroup 1 println("added ", clg.rel_cnt, " good relations and ",
                  clg.bad_rel, " bad ones, ratio ", clg.bad_rel/clg.rel_cnt)

  s = time_ns()

  h, piv = class_group_current_result(clg)

  idl = clg.FB.ideals
  want_extra = 5
  bad_h = false
  bad_norm = 0
  while h != 1 && (h==0 || want_extra > 0)
    for i in sort([ x for x in piv], lt = >)
      E = I[i]
      lt = max(100, round((clg.bad_rel/clg.rel_cnt)*2))

      while true
        if (E.cnt==0 && E.bad > lt) || (E.cnt != 0 && (bad_h || E.bad > lt))
          @v_do :ClassGroup 2 println("cnt ", E.cnt, " bad ", E.bad, " limit ", lt)
          @v_do :ClassGroup 2 println("re-starting (at ", i, ") ")
          @v_do :ClassGroup 3 println("for ideal ", E.A)

          A = idl[i]
          while norm(A) < sqrt_disc
            A *= rand(idl)
          end
          bad_norm = 0

          try
            I[i] = class_group_small_real_elements_relation_start(clg, A,
                          val = E.vl, limit = limit, prec = prec)
          catch e                
            if isa(e, LowPrecisionCholesky)
              print_with_color(:red, "2:prec too low in cholesky,")
              prec = Int(ceil(1.2*prec))
              println(" increasing to ", prec)
            elseif isa(e, LowPrecisionLLL)
              print_with_color(:red, "2:prec too low in LLL,")
              prec = Int(ceil(1.2*prec))
              println(" increasing to ", prec)
            else
              rethrow(e)
            end  
          end  
          E = I[i]
        end
        e = class_group_small_real_elements_relation_next(E)
        n = abs(norm_div(e, norm(E.A), np))
        #=
        if n*norm(E.A) != abs(norm(e))
          println("bad norm for ", e, " is ", n, " or ", n*norm(E.A),
             " should be ", norm(e), " np ", np, " norm(I) = ", norm(E.A))
          @assert false   
        end
        =#
        if n > sqrt_disc
          @v_do :ClassGroup 2 begin
            print_with_color(:red, "2:norm too large:")
            println(n, " should be ", sqrt_disc)
            println("offending element is ", e)
            println("prec now ", prec)
          end  
          bad_norm += 1
          if bad_norm /(E.cnt + E.bad + 1) > 0.1
            print_with_color(:red, "too many large norms, changing ideal\n")
            println("bad_norm: ", bad_norm, " cnt: ", E.cnt, " bad ", E.bad)
            A = idl[i]
            while norm(A) < sqrt_disc
              A *= rand(idl)
            end
            I[i] = class_group_small_real_elements_relation_start(clg, A,
                            val = E.vl, limit = limit, prec = prec)
            E = I[i]
            bad_norm = 0
          end
          #= CF: think careful here
           - norm might be wrong as we did not use enough primes
           - use as large prime variant
           - bad chance for smooth
           lets skip it for now
          =#
          continue;
        end
        if class_group_add_relation(clg, e, n, norm(E.A))
          E.cnt += 1
          if length(clg.R) - clg.last_H > 20
            break
          end
          break
        else
          E.bad += 1
        end
        if  clg.bad_rel - clg.last > 1000000
          global AllRels = (i, I[i], E)
          error("to bad in finding rel")
        end
      end
    end
    last_h = h
    l_piv = piv
    h, piv = class_group_current_result(clg)
    if h != 0
      if h==1 
        return h, piv
      end
      @v_do :ClassGroup 1 println("full rank: current h = ", h,
                      " want ", want_extra, " more")
      if h == last_h 
        want_extra -= 1
      else
        want_extra = 15
      end
    end
    if length(l_piv) - length(piv) < length(l_piv)/2
      bad_h = true
    else
      bad_h = false
    end
    @v_do :ClassGroup_gc 1 gc()
  end

  @v_do :ClassGroup 1 println("used ", (time_ns()-s)/1e9, " total so far ",
                  clg.hnf_time/1e9, " sec for hnf in ", clg.hnf_call, " calls");
  @v_do :ClassGroup 1 println("added ", clg.rel_cnt, " good relations and ",
                  clg.bad_rel, " bad ones, ratio ", clg.bad_rel/clg.rel_cnt)
  return class_group_current_result(clg)
end

function rank_increase(clg::ClassGrpCtx)
  if isdefined(clg, :H)
    old_h = rows(clg.H)
    new = rows(clg.M) - clg.last_H 
    h, piv = class_group_current_result(clg)
    return rows(clg.H)-old_h, new
  end
  if !isdefined(clg, :H)
    h, piv = class_group_current_result(clg)
    return rows(clg.H), rows(clg.M)
  end
end

function class_group_find_relations2(clg::ClassGrpCtx; val = 0, prec = 100,
                limit = 10)
  clg.hnf_time = 0.0
  clg.hnf_call = 0
  clg.rel_cnt = 0
  clg.bad_rel = 0

  n = degree(clg.FB.ideals[1].parent.order)
  t = time_ns()
  I = []
  O = parent(clg.FB.ideals[1]).order
  sqrt_disc = isqrt(abs(discriminant(O)))
  np = Int(ceil(nbits(sqrt_disc)/Base.GMP.GMP_BITS_PER_LIMB)+1)

  local f

  nI = length(clg.FB.ideals)
  Idl = clg.FB.ideals
  for i in nI:-1:1
    I = Idl[i]
    OK = false
    too_slow = false
    while !OK
      try
        f = class_group_small_real_elements_relation_start(clg, I, 
                                       limit = limit, prec = prec, val = val)
        OK = true                
      catch e
        if isa(e, LowPrecisionCholesky)
          print_with_color(:red, "prec too low in cholesky,")
          prec = Int(ceil(1.2*prec))
          println(" increasing to ", prec)
          if prec > 1000
            error("1:too much prec")
          end
        elseif isa(e, LowPrecisionLLL)
          print_with_color(:red, "prec too low in LLL,")
          prec = Int(ceil(1.2*prec))
          println(" increasing to ", prec)
          if prec > 1000
            error("2:too much prec")
          end
        else
          rethrow(e)
        end
      end
    end  

    f.vl = val
    while true
      e = class_group_small_real_elements_relation_next(f)
      n = abs(norm_div(e, norm(f.A), np))
      if n > sqrt_disc || f.restart > 0
        print_with_color(:red, "norm too large or restarting:")
        println(n, " should be ", sqrt_disc)
        println("offending element is ", e)
        println("skipping ideal (for now)")
        break
      end
      fl = class_group_add_relation(clg, e, n, norm(f.A))
      if fl
        f.cnt += 1
        if rows(clg.M) % 20 == 0
          a,b = rank_increase(clg)
          if a/b < 0.5
            @v_do :ClassGroup 2 println("rank too slow", a, b)
            too_slow=true
            break
          end
        end
      else
        f.bad += 1
        if f.bad > (clg.bad_rel/clg.rel_cnt)*2
          @v_do :ClassGroup 2 println("too slow in getting s.th. for ", i,
                          "\ngood: ", f.cnt,  " bad: ",  f.bad,
                          " ratio: ", (clg.bad_rel/clg.rel_cnt))
          too_slow = true                
          break
        end
      end
    end
    @v_do :ClassGroup_gc 1 gc()
    if too_slow
      break
    end
  end

  @v_do :ClassGroup 1 println("used ", (time_ns()-t)/1e9,
                  " sec for small elts, so far ", clg.hnf_time/1e9,
                  " sec for hnf in ", clg.hnf_call, " calls");
  @v_do :ClassGroup 1 println("added ", clg.rel_cnt, " good relations and ",
                  clg.bad_rel, " bad ones, ratio ", clg.bad_rel/clg.rel_cnt)

  s = time_ns()

  h, piv = class_group_current_result(clg)

  want_extra = 5
  bad_h = false
  no_rand = 1
  while h != 1 && (h==0 || want_extra > 0)
    for i in sort([ x for x in piv], lt = >)
      I = Idl[i]
      lt = max(100, round((clg.bad_rel/clg.rel_cnt)*2))

      while true
        #print_with_color(:red, "starting ideal no ")
        #println(i, " now")
        A = Idl[i]
        j = 0
        while norm(A) < sqrt_disc && j < no_rand
          A *= rand(Idl)
          j += 1
        end
        bad_norm = 0

        E = 0
        try
          E = class_group_small_real_elements_relation_start(clg, A,
                        val = val, limit = limit, prec = prec)
        catch e                
          if isa(e, LowPrecisionCholesky)
            print_with_color(:red, "2:prec too low in cholesky,")
            prec = Int(ceil(1.2*prec))
            println(" increasing to ", prec)
          elseif isa(e, LowPrecisionLLL)
            print_with_color(:red, "2:prec too low in LLL,")
            prec = Int(ceil(1.2*prec))
            println(" increasing to ", prec)
          else
            rethrow(e)
          end  
        end  
        no_rand_local = no_rand
        while true
          e = class_group_small_real_elements_relation_next(E)
          n = abs(norm_div(e, norm(E.A), np))
          if n > sqrt_disc || E.restart > 2
            @v_do :ClassGroup 2 begin
              print_with_color(:red, "2:norm too large (or restarting):")
              println(n, " should be ", sqrt_disc)
              println("offending element is ", e)
              println("prec now ", prec)
            end  
            A = Idl[i]
            j = 0
            # TH: without added no_rand_local < nI it crashes sometimes
            #     but I don't know what I am doing
            while norm(A) < sqrt_disc && j < no_rand_local && no_rand_local < nI
              A *= rand(Idl[(nI-no_rand_local):nI])
              j += 1
              no_rand_local += 1
            end
            E = class_group_small_real_elements_relation_start(clg, A,
                            val = E.vl, limit = limit, prec = prec)
            #= CF: think careful here
             - norm might be wrong as we did not use enough primes
             - use as large prime variant
             - bad chance for smooth
             lets skip it for now
            =#
            continue;
          end
          if class_group_add_relation(clg, e, n, norm(E.A))
            E.cnt += 1
            #print_with_color(:green, "success\n")
            if length(clg.R) - clg.last_H > 20
              #print_with_color(:blue, "found rels, trying again\n")
              break
            end
          else
            E.bad += 1
          end
        end
        if length(clg.R) - clg.last_H > cols(clg.M)*0.1
          #print_with_color(:blue, "2:found rels, trying again\n")
          break
        end
      end
      if length(clg.R) - clg.last_H > cols(clg.M)*0.1
        #print_with_color(:blue, "3:found rels, trying again\n")
        break
      end
    end
    last_h = h
    l_piv = piv
    last_rank = rows(clg.H)
    last_rels = clg.last_H
    h, piv = class_group_current_result(clg)
    if (rows(clg.H) - last_rank) < 0.5 * (clg.last_H - last_rels)
      #println("rank too slow, increasing randomness")
      no_rand += 5
      no_rand = min(no_rand, length(clg.FB.ideals))
      #println("new is ", no_rand)
    end
    if h != 0
      if h==1 
        return h, piv
      end
      @v_do :ClassGroup 1 println("full rank: current h = ", h,
                      " want ", want_extra, " more")
      if h == last_h 
        want_extra -= 1
      else
        want_extra = 15
      end
    end
    if length(l_piv) - length(piv) < length(l_piv)/2
      bad_h = true
    else
      bad_h = false
    end
    @v_do :ClassGroup_gc 1 gc()
  end

  @v_do :ClassGroup 1 println("used ", (time_ns()-s)/1e9, " total so far ",
                  clg.hnf_time/1e9, " sec for hnf in ", clg.hnf_call, " calls");
  @v_do :ClassGroup 1 println("added ", clg.rel_cnt, " good relations and ",
                  clg.bad_rel, " bad ones, ratio ", clg.bad_rel/clg.rel_cnt)
  return class_group_current_result(clg)
end

function class_group_find_relations3(clg::ClassGrpCtx; val = 0, prec = 100,
                limit = 10, no_b = 1)
  O = order(clg.FB.ideals[1])
  K = nf(O)
  n = degree(K)
  b = basis(O, K)

  while rows(clg.M) < 2*cols(clg.M)
    no_poss = 2^no_b * binom(n, no_b)
    no_poss = root(no_poss, 2)
    no = 0
    while no < no_poss && rows(clg.M) < 2*cols(clg.M)
      x = sum([rand([-1, 1])*rand(b) for i =1:no_b])
      nrm = norm_div(x, fmpz(1), 3)
      fl = class_group_add_relation(clg, x, nrm, fmpz(1))
      no += 1
    end
    if no >= no_poss
      no_b += 1
      println("giving more basis, now", no_b)
      break
      continue;
    else
      break
    end
  end
end 
################################################################################
#
#  Main function
#
################################################################################

function class_group(O::NfMaximalOrder; bound = -1, method = 2, large = 1000)
  if bound == -1
    bound = Int(ceil(log(abs(discriminant(O)))^2*0.3))
  end

  c = class_group_init(O, bound, complete = false)
  c.B2 = bound * large

  if method==1
    class_group_find_relations(c)
  else
    class_group_find_relations2(c)
  end

  return c
end


################################################################################
#
#  Conversion to Magma
#
################################################################################

function toMagma(f::IOStream, clg::ClassGrpCtx)
  print(f, "K<a> := NumberField(", nf(order(clg.FB.ideals[1])).pol, ");\n");
  print(f, "M := MaximalOrder(K);\n");
  print(f, "fb := [ ")
  for i=1:clg.FB.size
    print(f, "ideal<M| ", clg.FB.ideals[i].gen_one, ", ",
                    elem_in_nf(clg.FB.ideals[i].gen_two), ">")
    if i < clg.FB.size
      print(f, ",\n")
    end
  end
  print(f, "];\n")

  print(f, "R := [ ")
  for i = 1:length(clg.R)
    print(f, clg.R[i])
    if i < length(clg.R)
      print(f, ",\n")
    end
  end
  print(f, "];\n")

  toMagma(f, clg.M, name = "MM")
end

function toMagma(s::ASCIIString, c::ClassGrpCtx)
  f = open(s, "w")
  toMagma(f, c)
  close(f)
end


function toMagma(f::IOStream, a::Array{Any, 1}; name::ASCIIString="R")
  print(f, name, " := [\n")
  for i=1:(length(a)-1)
    print(f, a[i], ",\n")
  end
  print(f, a[end], "];\n")
end

function toMagma(s::ASCIIString, a::Array{Any, 1}; name::ASCIIString="R", mode::ASCIIString ="w")
  f = open(s, mode)
  toMagma(f, a, name = name)
  close(f)
end
  

################################################################################
#
#  Conversion to Nemo/hecke for storage
#
################################################################################

function toNemo(f::IOStream, a::Array{Any, 1}; name::ASCIIString="R")
  print(f, name, " = [\n")
  for i=1:(length(a)-1)
    print(f, a[i], ",\n")
  end
  print(f, a[end], "];\n")
end

function toNemo(s::ASCIIString, a::Array{Any, 1}; name::ASCIIString="R", mode::ASCIIString ="w")
  f = open(s, mode)
  toNemo(f, a, name = name)
  close(f)
end
 

################################################################################
##  Garbage?
################################################################################

#
# beware of the precision issue.
#
function lll(M::NfMaximalOrder)
  I = hecke.ideal(M, parent(basis_mat(M).num)(1))
  K = nf(M)
  c = conjugates_init(K.pol)

  prec = 100
  while true
    try
      q,w = lll(c, I, parent(basis_mat(M).num)(0), prec = prec)
      return NfMaximalOrder(K, FakeFmpqMat(w*basis_mat(M).num, basis_mat(M).den))
    catch e
      if isa(e, LowPrecisionLLL)
        prec = Int(round(prec*1.2))
        if prec>1000
          error("precision too large in LLL");
        end
        continue;
      else
        rethrow(e)
      end
    end
  end
end

################################################################################
#
#  Verification
#
################################################################################

# think of a sensible function name


function _validate_class_unit_group(c::ClassGrpCtx, U::UnitGrpCtx)
  O = U.order

  T = torsion_units(O)

  U.torsion_units = T

  U.torsion_units_order = length(T)

  w = U.torsion_units_order

  r1, r2 = signature(O)

  residue = zeta_residue(O, 0.6931)

  pre = prec(parent(residue))

  Ar = ArbField(pre)

  loghRtrue = Ar(residue) + log(Ar(w)*sqrt(abs(Ar(discriminant(O))))/(Ar(2)^(r1+r2) * pi_arb(pre)^r2))

  # I should assert that radius(loghRtrue) < log(2)

  @assert isfinite(loghRtrue)

  while true
    loghRapprox = log(c.h* abs(U.tentative_regulator))

    @assert isfinite(loghRapprox)

    if contains(loghRtrue, loghRapprox)
      return fmpz(1)
    elseif !overlaps(loghRtrue, loghRapprox)
      e = exp(loghRapprox - loghRtrue)
      t = ArfField(pre)()
      s = fmpz()
      ccall((:arb_get_abs_ubound_arf, :libarb), Void, (Ptr{arf}, Ptr{arb}, Clong), &t, &e, pre)
      ccall((:arf_get_fmpz, :libarb), Void, (Ptr{fmpz}, Ptr{arf}, Cint), &s, &t, 1) # 1 is round up
      return s
    end

    error("Not yet implemented")
  end
end

function _class_unit_group(O::NfMaximalOrder)

  c = class_group(O)

  U = UnitGrpCtx{FactoredElem{nf_elem}}(O)

  _unit_group_find_units(U, c)

  @assert U.full_rank

  return c, U, _validate_class_unit_group(c, U)
end


