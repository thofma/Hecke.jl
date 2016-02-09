################################################################################
#
#          GenNfOrdUnits.jl : Units in generic number field orders 
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
#  Copyright (C) 2015 Tommy Hofmann
#
################################################################################

export is_unit, is_torsion_unit, is_independent, pow!, unit_group,
       conjugates_arb, unit_group

order(u::UnitGrpCtx) = u.order

function _unit_group_init(O::NfMaximalOrder)
  u = UnitGrpCtx{FactoredElem{nf_elem}}(O)
  return u
end

function show(io::IO, U::UnitGrpCtx)
  print(io, "Unit group context of\n$(order(U))\n")
end

################################################################################
#
#  Unit rank
#
################################################################################

doc"""
***
    unit_rank(O::GenNfOrd) -> Int

> Returns the unit_rank of $\mathcal O$, that is, the rank of the free part of the unit
> group of $\mathcal O$.
"""
function unit_rank(O::GenNfOrd)
  r1, r2 = signature(nf(O))
  return r1 + r2 - 1
end

################################################################################
#
#  Testing for invertibility
#
################################################################################

doc"""
***
    is_unit(x::NfOrderElem) -> Bool

> Returns whether $x$ is invertible or not.
"""
function is_unit(x::NfOrderElem)
  return abs(norm(x)) == 1 
end

_is_unit(x::NfOrderElem) = is_unit(x)

function _is_unit{T <: Union{nf_elem, FactoredElem{nf_elem}}}(x::T)
  return abs(norm(x)) == 1
end

################################################################################
#
#  Torsion unit test
#
################################################################################

doc"""
***
    is_torsion_unit(x::NfOrderElem, checkisunit::Bool = false) -> Bool

> Returns whether $x$ is a torsion unit, that is, whether there exists $n$ such
> that $x^n = 1$.
> 
> If `checkisunit` is `true`, it is first checked whether $x$ is a unit of the
> maximal order of the number field $x$ is lying in.
"""
function is_torsion_unit(x::NfOrderElem, checkisunit::Bool = false)
  return is_torsion_unit(x.elem_in_nf, checkisunit)
end

################################################################################
#
#  Order of a single torsion unit
#
################################################################################

doc"""
***
    torsion_unit_order(x::NfOrderElem, n::Int)

> Given a torsion unit $x$ together with a multiple $n$ of its order, compute
> the order of $x$, that is, the smallest $k \in \mathbb Z_{\geq 1}$ such
> that $x^`k` = 1$.
>
> It is not checked whether $x$ is a torsion unit.
"""
function torsion_unit_order(x::NfOrderElem, n::Int)
  return torsion_unit_order(x.elem_in_nf, n)
end

################################################################################
#
#  Torsion unit group
#
################################################################################

doc"""
***
    torsion_units(O::GenNfOrd) -> Array{NfOrderElem, 1}

> Given an order $O$, compute the torsion units of $O$.
"""
function torsion_units(O::GenNfOrd)
  ar, g = _torsion_units(O)
  return ar
end

doc"""
***
    torsion_units(O::GenNfOrd) -> NfOrderElem

> Given an order $O$, compute a generator of the torsion units of $O$.
"""
function torsion_units_gen(O::GenNfOrd)
  ar, g = _torsion_units(O)
  return g
end

function _torsion_units(O::GenNfOrd)
  if isdefined(O, :torsion_units)
    return O.torsion_units
  end

  n = degree(O)
  K = nf(O)
  rts = conjugate_data_arb(K)
  A = ArbField(rts.prec)
  M = ArbMatSpace(A, n, n)()
  r1, r2 = signature(K)
  B = basis(O)

  if r1 > 0
    return [ O(1), -O(1) ], -O(1)
  end

  function _t2_pairing(x, y, p)
    local i
    v = minkowski_map(x, p)
    w = minkowski_map(y, p)
 
    t = zero(parent(v[1]))
 
    for i in 1:r1
      t = t + v[i]*w[i]
    end
 
    for i in (r1 + 1):(r1 + 2*r2)
      t = t + v[i]*w[i]
    end
 
    return t
  end

  p = 64

  gram_found = false

  while !gram_found
    for i in 1:n, j in 1:n
      M[i,j] = _t2_pairing(B[i], B[j], p)
      if !isfinite(M[i, j])
        p = 2*p
        break
      end
    end
    gram_found = true
  end

  l = enumerate_using_gram(M, A(n))

  R = Array{NfOrderElem, 1}()

  for i in l
    if O(i) == zero(O)
      continue
    end
    if is_torsion_unit(O(i))
      push!(R, O(i))
    end
  end

  i = 0

  for i in 1:length(R)
    if torsion_unit_order(R[i], length(R)) == length(R)
      break
    end
  end

  O.torsion_units = R, deepcopy(R[i])

  return O.torsion_units
end

################################################################################
#
#  Test if units are independent
#
################################################################################

function _conjugates_arb_log(A::FactoredElemMon{nf_elem}, a::nf_elem, abs_tol::Int)
  if haskey(A.conj_log_cache, abs_tol)
    if haskey(A.conj_log_cache[abs_tol], a)
      return A.conj_log_cache[abs_tol][a]
    else
      z = conjugates_arb_log(a, abs_tol)
      A.conj_log_cache[abs_tol][a] = z
      return z
    end
  else
    A.conj_log_cache[abs_tol] = Dict{nf_elem, arb}()
    z = conjugates_arb_log(a, abs_tol)
    A.conj_log_cache[abs_tol][a] = z
    return z
  end
end

function conjugates_arb(x::FactoredElem{nf_elem}, abs_tol::Int)
  d = degree(_base_ring(x))
  res = Array(acb, d)

  i = 1

  for a in base(x)
    z = conjugates_arb(a, abs_tol)
    if i == 1
      for j in 1:d
        res[j] = z[j]^x.fac[a]
      end
    else
      for j in 1:d
        res[j] = res[j] * z[j]^x.fac[a]
      end
    end
    i = i + 1
  end

  return res
end

function conjugates_arb_log(x::FactoredElem{nf_elem}, abs_tol::Int)
  K = base_ring(x)::AnticNumberField
  r1, r2 = signature(K)
  d = r1 + r2
  res = Array(arb, d)

  i = 1

  for a in base(x)
    z = _conjugates_arb_log(parent(x), a, abs_tol)
    if i == 1
      for j in 1:d
        res[j] = x.fac[a]*z[j]
      end
    else
      for j in 1:d
        res[j] = res[j] + x.fac[a]*z[j]
      end
    end
    i = i + 1
  end

  return res
end

_base_ring(x::nf_elem) = parent(x)::AnticNumberField

_base_ring(x::FactoredElem{nf_elem}) = base_ring(x)::AnticNumberField


function is_independent{T}(x::Array{T, 1})

  K = _base_ring(x[1])

  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  p = 32

  # This can be made more memory friendly
  while true
    @assert p != 0

    conlog = conjugates_arb_log(x[1], -p)

    A = MatrixSpace(parent(conlog[1]), length(x), rr)()::arb_mat

    for i in 1:rr
      A[1, i] = conlog[i]
    end

    Ar = base_ring(A)

    for k in 2:length(x)
      conlog = conjugates_arb_log(x[k], -p)
      for i in 1:rr
        A[k, i] = conlog[i]
      end
    end

    B = A*transpose(A)
    C = parent(B)()
    d = det(B)
    y = (Ar(1)//Ar(r))^r * (Ar(21)//Ar(128) * log(Ar(deg))//(Ar(deg)^2))^(2*r)
    if isfinite(d) && ispositive(y - d)
      return false
    elseif isfinite(d) && ispositive(d)
      return true
    end
    p = 2*p
  end
end

function add_dependent_unit{S, T}(x::UnitGrpCtx{S}, y::T)
  u, m = add_dependent_unit(x.units, y)
  x.units = u
  x.tentative_regulator = _reg(u, 64)
  return m
end

function add_dependent_unit{S, T <: Union{nf_elem, FactoredElem{nf_elem}}}(x::Array{S, 1}, y::T)
  # I need to find a relation

  K = _base_ring(x[1])

  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  p = 128 
  #println("precision is $(c.prec)");

  zz = Array(fmpz, r + 1)
# Find 
#while true
  conlog = conjugates_arb_log(x[1], p)

  A = ArbMatSpace(parent(conlog[1]), length(x), rr)()
  b = ArbMatSpace(parent(conlog[1]), 1, rr)()
  Ar = base_ring(A)
  
  for i in 1:rr
    A[1, i] = conlog[i]
  end

  for k in 2:length(x)
    conlog = conjugates_arb_log(x[k], p)
    #println("logs of $(x[k]): $conlog")
    for i in 1:rr
      A[k, i] = conlog[i]
    end
  end

  conlog = conjugates_arb_log(y, p)

  for i in 1:rr
    b[1,i] = conlog[i]
  end
  B = A*transpose(A)
  B = transpose(A)*inv(B)
  v = b*B

  z = Array(fmpq, r)
  
  rreg = abs(_reg(x, p)) # use submatrix of A instead or store it

  #println(midpoint(20*rreg))

  # This is bad someone should fix it

  bound = fmpz(BigInt(ceil(BigFloat(midpoint(20*rreg)))))

  #println("bound for den is $bound ")

  largest_den = ZZ(0)

  j = 1

#  while largest_den < bound
   A = [ _max_frac_bounded(_arb_get_fmpq(v[1, i]), bound) for i in 1:r]
#   println("Maximal depth of reconstruction: $A \n")
   B = fill(0, r)
   B[end] = -1

  while true
   # increased last element by one
    B[end] += 1
    # looking at overflows from end to beginning
    for i = r:-1:2
      if B[i] > A[i]
        B[i]= 0
        B[i-1] += 1
      end
    end
    # if overflow in the first entry, stop
    if B[1] > A[1]
      break
    end

    is_zero = true
    is_contained = true
    for i in 1:r
      temp_fmpq = _arb_get_fmpq(v[1, i])
      z[i] = fmpq(cfrac(temp_fmpq, B[i])[1])
      is_zero = is_zero && iszero(z[i])
      is_contained = is_contained && Nemo.contains(v[1, i], z[i])
      @assert den(z[i]) < bound
    end

    if is_zero || !is_contained
      continue
    end

    dlcm = den(z[1])

    for i in 2:length(z)
      dlcm = lcm(dlcm, den(z[i]))
    end

    for i in 1:r
      zz[i] = num(z[i]*dlcm)
    end 

    zz[r + 1] = -dlcm
    
    #println("Possible relation: $zz")

    if !check_relation_mod_torsion(x, y, zz)
      j = j + 1
    else
      break
    end
  end

  g = zz[1]

  for i in 1:length(zz)
    g = gcd(g, zz[i])
    if g == 1
      break
    end
  end

  for i in 1:length(zz)
    zz[i] = div(zz[i], g)
  end

  #println(zz)

  m = MatrixSpace(FlintZZ, r + 1, 1)(reshape(zz, r + 1, 1))

  h, u = hnf_with_transform(m)::Tuple{fmpz_mat, fmpz_mat} # Why annotations?

  @assert h[1,1] == 1

  u = inv(u)

  m = submat(u, 1:r+1, 2:r+1)

  return transform(vcat(x, y), m), m
end

function transform(x::Array{nf_elem}, y::fmpz_mat)
  n = length(x)
  @assert n == rows(y)
  m = cols(y)
  z = Array(nf_elem, m)
  for i in 1:m
    z[i] = x[1]^y[1, i]
    for j in 2:n
      z[i] = z[i]*x[j]^y[j, i]
    end
  end
  return z
end

function _max_frac_bounded(x::fmpq, b::fmpz)
  n = 2
  c = cfrac(x, n)[1]
  q = fmpq(c)

  while abs(den(q)) < b && q != x
    n = 2*n
    c = cfrac(x, n)[1]
    q = fmpq(c)
  end

  while abs(den(q)) > b
    n = n - 1
    c = cfrac(x, n)[1]
    q = fmpq(c)
  end

  return n
end

function check_relation_mod_torsion{T}(x::Array{T, 1}, y::T, z::Array{fmpz, 1})
# this should be improved
  (length(x) + 1 != length(z)) && error("Lengths of arrays does not fit")
  r = x[1]^z[1]

  for i in 2:length(x)
    r = r*x[i]^z[i]
  end 

  return is_torsion_unit(r*y^z[length(z)])
end

*(x::FactoredElem{nf_elem}, y::NfOrderElem) = x*elem_in_nf(y)

*(x::NfOrderElem, y::FactoredElem{nf_elem}) = y*x

function _pow{T <: Union{nf_elem, FactoredElem{nf_elem}}}(x::Array{T, 1}, y::Array{fmpz, 1})
  if eltype(x) == nf_elem
    K = parent(x[1])::AnticNumberField
  elseif eltype(x) == FactoredElem{nf_elem}
    K = base_ring(x[1])::AnticNumberField
  end

  zz = deepcopy(y)

  z = Array(fmpz, length(x))

  for i in 1:length(x)
    z[i] = mod(zz[i], 2)
    zz[i] = zz[i] - z[i]
  end

  r = K(1)

  return zz
end

################################################################################
#
#  Free part of the unit group
#
################################################################################

function _reg{T}(x::Array{T, 1}, abs_tol::Int)
  K = _base_ring(x[1])
  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  p = 32

  while true
    conlog = conjugates_arb_log(x[1], p)

    A = ArbMatSpace(parent(conlog[1]), r, r)()

    for j in 1:r
      A[1, j] = conlog[j]
    end

    for i in 2:r
      conlog = conjugates_arb_log(x[i], p)
      for j in 1:r
        A[i, j] = conlog[j]
      end
    end

    z = abs(det(A))

    if isfinite(z) && radiuslttwopower(z, abs_tol)
      return z
    end
    
    p = 2*p
  end
end

function _make_row_primitive(x::fmpz_mat, j::Int)
  y = x[j, 1]
  for i in 1:cols(x)
    y = gcd(y, x[j, i])
  end
  if y > 1
    for i in 1:cols(x)
      x[j, i] = div(x[j, i], y)
    end
  end
end

function unit_group(O::NfMaximalOrder, c::ClassGrpCtx)
  u = UnitGrpCtx{FactoredElem{nf_elem}}(O)
  _unit_group_find_units(u, c)
  return u
end

function _unit_group_find_units(u::UnitGrpCtx, x::ClassGrpCtx)
  O = order(u)
  ker, rnk = nullspace(transpose(fmpz_mat(x.M)))
  rnk = Int(rnk)
  ker = transpose(ker)

  K = nf(order(x.FB.ideals[1]))
  r = unit_rank(O)
  r1, r2 = signature(O)

  A = u.units

  j = 0

  while(length(A) < r)
    j = j + 1

    if j > rows(ker)
      #println("found only $(length(A)) many units but I need $r many")
      return length(A)
    end

    if is_zero_row(ker, j)
      continue
    end

    #println("testing element $j")
    _make_row_primitive(ker, j)

    y = FactoredElem(x, ker, j)

    if is_torsion_unit(y)
      #println("torsion unit: $y")
      continue
    end
    _add_unit(u, y)
  end

  u.full_rank = true

  j = 0

  no_change_matrix = MatrixSpace(ZZ, unit_rank(O), unit_rank(O))(1)
  no_change_matrix = vcat(no_change_matrix, MatrixSpace(ZZ, 1, unit_rank(O))(0))

  not_larger = 0

  while(j < rows(ker)) && not_larger < 6
    j = j + 1
    if is_zero_row(ker, j)
      continue
    end

    y = FactoredElem(x, ker, j)
    
    if is_torsion_unit(y)
      #println("torsion unit: $y")
      continue
    end

    m = add_dependent_unit(u, y)

    if m == no_change_matrix
      not_larger = not_larger + 1
    else
      not_larger = 0
    end

    #println(_reg(u.units))
  end

  u.tentative_regulator = _reg(u.units, 64)
end

function _add_unit(u::UnitGrpCtx, x::FactoredElem{nf_elem})
  if is_independent(vcat(u.units, [x]))
    push!(u.units, x)
  end
  nothing
end

################################################################################
#
#  Factored elements over number fields/orders
#
################################################################################

# Get FactoredElem from ClassGrpCtx

function FactoredElem(x::ClassGrpCtx, y::fmpz_mat, j::Int)
  return FactoredElem(x.R, [ y[j, i] for i in 1:cols(y) ])
end

# Compute (log(abs(x_1)),...) where x_i is the ith conjugate

function conjugates_log(x::FactoredElem{nf_elem})
  M = parent(x)
  K = base_ring(x)  
  d = degree(K)
  r1, r2 = signature(K)
  res = Array(arb, r1 + r2)
  c = conjugate_data_arb(K)
  #println("precision is $(c.prec)");

  for i in 1:r1+r2
    res[i] = ArbField(c.prec)(0)
  end

  #println("Cached logarithms: $(M.basis_conjugates_log)")

  for a in base(x)
    # We should replace this using multipoint evaluation of libarb
    if haskey(M.basis_conjugates_log, a) && M.basis_conjugates_log[a][1] == c.prec
      z = M.basis_conjugates_log[a][2] 
      for i in 1:r1+r2
        res[i] = res[i] + x.fac[a]*z[i]
      end
    else
      z = Array(arb, r1 + r2)
      for i in 1:r1
        z[i] = log(abs(evaluate(parent(K.pol)(a),c.real_roots[i])))
      end
      for i in 1:r2
        z[r1 + i] = 2*log(abs(evaluate(parent(K.pol)(a), c.complex_roots[i])))
      end
      M.basis_conjugates_log[a] = (c.prec, z)
      for i in 1:r1+r2
        res[i] = res[i] + x.fac[a]*z[i]
        if !isfinite(res[i])
          refine(c)
          return conjugates_log(x)
        end
      end
    end
  end
  return res
end

# I don't know why I return absolute values
function conjugates_arb(x::FactoredElem{nf_elem})
  K = base_ring(x)
  M = parent(x)
  d = degree(K)
  res = Array(arb, d)
  c = conjugate_data_arb(K)
  
  for i in 1:d
    res[i] = ArbField(c.prec)(1)
  end

  for a in base(x)
    if haskey(M.basis_conjugates, a) && M.basis_conjugates[a][1] == c.prec
      z = M.basis_conjugates[a][2] 
      for i in 1:d
        res[i] = res[i]*z[i]^x.fac[a]
      end
    else
      z = Array(arb, d)
      for i in 1:d
        z[i] = abs(evaluate(parent(K.pol)(a),c.roots[i]))
      end
      M.basis_conjugates[a] = (c.prec, z)
      for i in 1:d
        res[i] = res[i]*z[i]^x.fac[a]
        if !isfinite(res[i])
          refine(c)
          return conjugates_arb(x)
        end
      end
    end
  end
  return res
end

function inv(x::FactoredElem{nf_elem})
  y = deepcopy(x)
  for a in base(y)
    y.fac[a] = -y.fac[a]
  end
  return y
end

function ^(x::nf_elem, y::fmpz)
  if y < 0
    return inv(x)^(-y)
  elseif y == 0
    return parent(x)(1)
  elseif y == 1
    return deepcopy(x)
  elseif mod(y, 2) == 0
    z = x^(div(y, 2))
    return z*z
  elseif mod(y, 2) == 1
    return x^(y-1) * x
  end
end

function issaturated(U::UnitGrpCtx, p::Int, B::Int = 2^30 - 1)
  N = 3*unit_rank(order(U))
  primes =  _find_primes_for_saturation(order(U), p, N, B)
  
  m = _matrix_for_saturation(U, primes[1], p)

  for i in 2:N
    m = vcat(m, _matrix_for_saturation(U, primes[i], p))
  end

  (K, k) = _right_kernel(m)

  K = transpose(K)
  L = lift(K)

  nonzerorows = Array{Int, 1}()

  for j in 1:rows(L)
    if !is_zero_row(L, j)
      push!(nonzerorows, j)
    end
  end

  if k == 0 
    return (true, zero(nf(order(U))))
  elseif k == 1 && sum([ L[nonzerorows[1], i] for i in 1:cols(L)-1]) == 0
    # Only one root, which is torsion.
    # We assume that the torsion group is the full torsion group
    return (true, zero(nf(order(U))))
  else
    for j in nonzerorows
      
      #println(K)
      a = U.units[1]^(L[j, 1])
      for i in 2:length(U.units)
        a = a*U.units[i]^L[j, i]
      end
      
      if gcd(p, U.torsion_units_order) != 1
        a = a*elem_in_nf(U.torsion_units_gen)^L[j, length(U.units) + 1]
      end

      #print("Evaluating the element...")
      b = evaluate(a)
      #println("DONE")
      has_root, roota = root(b, p)

      if !has_root
        continue
      end

      return (false, roota)
    end
  end

  # try some random linear combination of kernel vectors

  MAX = 100

  println("No root found so far")

  for i in 1:MAX
    ra = rand(0:p-1, rows(K))
    v = MatrixSpace(base_ring(K), 1, cols(K))(0)
    for j in 1:cols(K)
      for l in 1:rows(K)
        v[1, j] = v[1, j] + ra[l]*K[l,j]
      end
    end

    if v == parent(v)(0)# || sum([v[1, j] for j in 1:rows(K)-1]) == 0
      continue
    end
    
    v = lift(v)

    a = U.units[1]^(v[1, 1])
    for j in 2:length(U.units)
      a = a*U.units[j]^v[1, j]
    end

    if gcd(p, U.torsion_units_order) != 1
      a = a*elem_in_nf(U.torsion_units_gen)^v[1, length(U.units) + 1]
    end

      #print("Evaluating the element...")
    b = evaluate(a)
      #println("DONE")
    has_root, roota = root(b, p)

    if has_root
      return (false, roota)
    end
  end

  return (true, zero(nf(order(U))))
end

function root(a::nf_elem, n::Int)
  #println("Compute $(n)th root of $a")
  Kx, x = PolynomialRing(parent(a), "x")

  f = x^n - a

  fac = factor(f)
  #println("factorization is $fac")

  for i in keys(fac)
    if degree(i) == 1
      return (true, -coeff(i, 0)//coeff(i, 1))
    end
  end

  return (false, zero(parent(a)))
end

# TH:
# Let U = <u_1,...,u_n,z> with z a generator for Tor(U)
# For a prime p the group U/U^p is F_p-vector space of dimension
# rank(U) or rank(U) + 1 (depending on the order of z).
# if p divides N(P) - 1 = #F_P*, then F_P*/F_P*^p is a one-dimensional
# F_p-vector space. Thus the canonical map F_p-linear
#               U/U^p -> F_P*/F_P*^p
# can be described by a 1 x (rank(U)) or 1 x (rank(U) + 1) matrix over F_p,
# and can be computed by solving discrete logarithms in F_P
#
# The output will be of type
# elem_type(MatrixSpace(ResidueRing(ZZ, p), 1, rank(U) ( + 1))), so
# nmod_mat or 
# THIS FUNCTION IS NOT TYPE STABLE
function _matrix_for_saturation(U::UnitGrpCtx, P::NfMaximalOrderIdeal, p::Int)
  O = order(U)
  K = nf(O)
  F, mF = ResidueField(O, P)
  mK = extend(mF, K)
  g = _primitive_element(F)

  # We have to add the generator of the torsion group
  if gcd(p, U.torsion_units_order) != 1
    res = MatrixSpace(ResidueRing(FlintZZ, p), 1, unit_rank(O) + 1)()
  else
    res = MatrixSpace(ResidueRing(FlintZZ, p), 1, unit_rank(O))()
  end

  t = K()

  for i in 1:length(U.units)
    u = U.units[i]
    y = one(F)

    # P.gen_two should be P-unformizer
    #println("$(P.gen_one), $b, $(P.gen_two)")

    for b in base(u)
      t = b*K(P.gen_two)^(-valuation(b, P))

      if mod(den(t), minimum(P)) == 0
        l = valuation(den(t), P)
        y = y*(mK(t*elem_in_nf(P.anti_uniformizer)^l)*mF(P.anti_uniformizer)^(-l))^u.fac[b]
      else
        y = y*mK(t)^u.fac[b]
      end
    end

    res[1, i] = disc_log(y, g, p)
  end

  if gcd(p, U.torsion_units_order) != 1
    res[1, unit_rank(O) + 1] = disc_log(mF(U.torsion_units_gen), g, p)
  end

  return res
end

# TH:
# This function finds n prime ideals P of O such that p divides N(P) - 1
# Moreover the prime ideals are unramified and min(P) does not divide
# the index of O in the equation order.
#
# The function loops through all prime ideals ordered by the minimum,
# starting at next_prime(st)
function _find_primes_for_saturation(O::NfMaximalOrder, p::Int, n::Int,
                                     st::Int = 0)
  res = Array(NfMaximalOrderIdeal, n)
  i = 0

  q = st
  while i < n
    q = next_prime(q)

    if mod(index(O), q) == 0 || isramified(O, q)
      continue
    end

    lp = prime_decomposition(O, q)

    j = 1

    while j <= length(lp) && i < n
      Q = lp[j]
      if mod(norm(Q[1]) - 1, p) == 0
        i = i + 1
        res[i] = Q[1]
      end
      j = j + 1
    end
  end

  return res
end
        
function _primitive_element(F::FqNmodFiniteField)
  @assert characteristic(F) < typemax(Int)
  #println("Computing primitive element of $F")
  #println("Have to factor $(order(F) - 1)")
  fac = factor(order(F) - 1)
  f = degree(F)
  p = Int(characteristic(F))
  g = gen(F)
  while true
    r = rand(0:p-1, f)
    a = zero(F)
    for i in 1:f
      a = a + r[i]*g^(i-1)
    end
    if iszero(a)
      continue
    end
    is_primitive = true
    for l in keys(fac)
      if isone(a^(div(order(F) - 1, l)))
        is_primitive = false
      end
    end
    if is_primitive
      return a
    end
  end
end

function FactoredElem(x::nf_elem)
  z = FactoredElem{nf_elem}()
  z.fac[x] = fmpz(1)
  z.parent = FactoredElemMon{nf_elem}(parent(x))
  return z
end

function validate(c::ClassGrpCtx, u::UnitGrpCtx)
  b = _validate_class_unit_group(c, u)

  p = 2

  while b > 1
    print("Saturating at $p...")
    issat, new_unit = issaturated(u, p)
    while !issat
      #println("I have found a new unit: $new_unit")
      add_dependent_unit(u, FactoredElem(new_unit))
      #println("$(u.tentative_regulator)")
      
      b = _validate_class_unit_group(c, u)

      if b == 1
        break
      end

      issat, new_unit = issaturated(u, p)
    end

    b = _validate_class_unit_group(c, u)
    #println("Bound is now $b")
    p = next_prime(p)
  end
end

# To get a nice "interface" for elements and factored elements

base_ring(x::nf_elem) = parent(x)

function is_unit(x::FactoredElem{nf_elem})
  return abs(norm(z)) == 1
end

function norm(x::FactoredElem{nf_elem})
  z = fmpq(1)
  for a in base(x)
    z = z*norm(a)^x.fac[a]
  end
  return z
end

function ^(x::fmpq, y::fmpz)
  if typemax(Int) > y
    return x^Int(y)
  else
    error("Not implemented (yet)")
  end
end

################################################################################
#
#  High level interface
#
################################################################################

function unit_group(O::NfMaximalOrder)
  if isdefined(O, :unit_group)
    return O.unit_group::Map{AbGrp, FactoredElem{nf_elem}}
  else
    c, U, b = _class_unit_group(O)
    f = AbToNfOrdUnitGrp(O, U.units, U.torsion_units_gen, U.torsion_units_order)
    O.unit_group = f
    return f
  end
end
