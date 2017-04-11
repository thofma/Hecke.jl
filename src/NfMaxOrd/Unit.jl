################################################################################
#
#       NfMaxOrd/Units.jl : Units in generic number field orders 
#
# This file is part of Hecke.
#
# Copyright (c) 2015, 2016: Claus Fieker, Tommy Hofmann
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
#  Copyright (C) 2015, 2016 Tommy Hofmann
#
################################################################################

export isunit, istorsion_unit, isindependent, unit_group

add_verbose_scope(:UnitGroup)

################################################################################
#
#  Initialization 
#
################################################################################

function _unit_group_init(O::NfMaxOrd)
  u = UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(O)
  return u
end

################################################################################
#
#  Field access
#
################################################################################

order(u::UnitGrpCtx) = u.order

################################################################################
#
#  String I/O
#
################################################################################

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
    unit_rank(O::NfOrd) -> Int

> Returns the unit rank of $\mathcal O$, that is, the rank of the unit group
> $\mathcal O^\times$.
"""
function unit_rank(O::NfOrd)
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
    isunit(x::NfOrdElem) -> Bool

> Returns whether $x$ is invertible or not.
"""
function isunit(x::NfOrdElem)
  return abs(norm(x)) == 1 
end

_isunit(x::NfOrdElem) = isunit(x)

function _isunit{T <: Union{nf_elem, FacElem{nf_elem, AnticNumberField}}}(x::T)
  return abs(norm(x)) == 1
end

################################################################################
#
#  Test if units are independent
#
################################################################################

doc"""
***
    isindependent{T}(x::Array{T, 1})

> Given an array of non-zero elements in a number field, returns whether they
> are multiplicatively independent.
"""
function isindependent{T}(x::Array{T, 1}, p::Int = 32)
  return _isindependent(x, p)
end

function _isindependent{T}(x::Array{T, 1}, p::Int = 32)
  K = _base_ring(x[1])

  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  # This can be made more memory friendly
  while true
    @assert p != 0

    conlog = conjugates_arb_log(x[1], p)

    A = MatrixSpace(parent(conlog[1]), length(x), rr)()

    for i in 1:rr
      A[1, i] = conlog[i]
    end

    Ar = base_ring(A)

    for k in 2:length(x)
      conlog = conjugates_arb_log(x[k], p)
      for i in 1:rr
        A[k, i] = conlog[i]
      end
    end

    B = A*transpose(A)
    @vprint :UnitGroup 1 "Computing det of $(rows(B))x$(cols(B)) matrix with precision $(p) ... \n"
    d = det(B)

    y = (Ar(1)//Ar(r))^r * (Ar(21)//Ar(128) * log(Ar(deg))//(Ar(deg)^2))^(2*r)
    if isfinite(d) && ispositive(y - d)
      return false, p
    elseif isfinite(d) && ispositive(d)
      return true, p
    end
    p = 2*p
  end
end

function _isindependent{T}(u::UnitGrpCtx{T}, y::FacElem{T})
  K = _base_ring(x[1])
  p = u.indep_prec

  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  # This can be made more memory friendly
  while true
    @assert p != 0

#    if length(u.units) == 0
#      A = _conj_log_mat([y], p)
#      B = MatrixSpace(base_ring(A), rows(A), rows(A))
#      z.conj_log_mat_tranpose = (transpose(A), p)
#      mul!(B, A, z.conj_log_mat_transpose)
#      z.conj_log_mat = (A, p)
#      z.conj_log_mat_times_transpose = (B, p)
#    end
#
#    if z.conj_log_mat[2] == p # the old matrix has the same precision as our working precision
#      A = z.conj_log_mat[1]
#      conjlog = conjugates_arb_log(y, p)
#      newrow = MatrixSpace(base_ring(A), 1, cols(A))()
#      newcol = MatrixSpace(base_ring(A), cols(A), 1)()
#      z.conj_log_mat = (vcat(A, newrow), p)
#      z.conj_log_mat_transpose = (hcat(z.conj_log_mat_transpose[1], newcol), p)
#
#      for i in 1:cols(A)
#        z.conj_log_mat[1][rows(A) + 1, i] = conjlog[i]
#        z.conj_log_mat_transpose[1][i, rows(A) + 1]
#      end
#      A = z.conj_log_mat[1]
#    end
    A = _conj_log_mat(u.units, p)

    B = A*transpose(A)
    @vprint :UnitGroup 1 "Computing det of $(rows(B))x$(cols(B)) matrix with precision $(p) ... \n"
    d = det(B)

    y = (Ar(1)//Ar(r))^r * (Ar(21)//Ar(128) * log(Ar(deg))//(Ar(deg)^2))^(2*r)
    if isfinite(d) && ispositive(y - d)
      return false, p
    elseif isfinite(d) && ispositive(d)
      return true, p
    end
    p = 2*p
  end
end

# Checks whether x[1]^z[1] * ... x[n]^z[n]*y^[n+1] is a torsion unit
# This can be improved
function _check_relation_mod_torsion{T}(x::Array{T, 1}, y::T, z::Array{fmpz, 1}, p::Int = 16)
  (length(x) + 1 != length(z)) && error("Lengths of arrays does not fit")
  r = x[1]^z[1]

  for i in 2:length(x)
    r = r*x[i]^z[i]
  end 

  w = r*y^z[length(z)]

  b, _ = istorsion_unit(w, false, p)
#  b, _ = istorsion_unit(w)
  return b
end

function _find_rational_relation!(rel::Array{fmpz, 1}, v::arb_mat, bound::fmpz)
  @vprint :UnitGroup 2 "Finding rational approximation in $v\n"
  r = length(rel) - 1

  z = Array{fmpq}(r)

  # Compute an upper bound in the denominator of an entry in the relation
  # using Cramer's rule and lower regulator bounds

  # Now comes the rational approximation phase

  # First a trivial check:
  # If the relation contains only integers, it does not yield any information

  i = 0

  is_integer = true

  while is_integer && i < r
    i = i + 1
    b, o = unique_integer(v[1, i])
    if b
      rel[i] = o
    end
    is_integer = is_integer && b
  end

  if is_integer
    rel[r + 1] = -1
    @vprint :UnitGroup 2 "Found rational relation: $rel.\n"
    return true
  end

  for i in 1:r
    if radius(v[1, i]) > 1
      # This is a strange case I cannot handle at the moment
      return false
      #no_change_matrix = MatrixSpace(ZZ, r, r)(1)
      #no_change_matrix = vcat(no_change_matrix, MatrixSpace(ZZ, 1, r)(0))
      #return x, no_change_matrix
    end

    app =  _frac_bounded_2(v[1, i], bound)
    if app[1]
      z[i] = app[2]
    else
      @vprint :UnitGroup 2 "Something went wrong with the approximation.\n"
      return false
    end
  end

  dlcm = den(z[1])

  for i in 2:length(z)
    dlcm = lcm(dlcm, den(z[i]))
  end

  for i in 1:r
    rel[i] = num(z[i]*dlcm)
  end 

  rel[r + 1] = -dlcm

  # Check that relation is primitive
  g = rel[1]

  for i in 2:length(rel)
    g = gcd(g, rel[i])
    if g == 1
      break
    end
  end

  @assert g == 1

  @vprint :UnitGroup 2 "Found rational relation: $rel.\n"
  return true
end

# Given r elements x_1,...,x_r, where r is the unit rank, and y an additional unit,
# compute a basis z_1,...z_r such that <x_1,...x_r,y,T> = <z_1,...,z_r,T>,
# where T are the torsion units
function _find_relation{S, T}(x::Array{S, 1}, y::T, p::Int = 64)

  K = _base_ring(x[1])

  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  R = ArbField(p)

  zz = Array{fmpz}(r + 1)

  @vprint :UnitGroup 1 "Computing conjugates log matrix ... \n"
  A = _conj_log_mat_cutoff(x, p)

  Ar = base_ring(A)

  b = ArbMatSpace(Ar, 1, r)()

  conlog = conjugates_arb_log(y, p)

  for i in 1:r
    b[1, i] = conlog[i]
  end

  B = parent(A)()


  # I should do this using lu decomposition and caching
  # The inversion could go wrong,
  # Then we again have to increase the precision

  inv_succesful = false

  try
    @vprint :UnitGroup 1 "Inverting matrix ... \n"
    B = inv(A)
    inv_succesful = true
  catch e
    @vprint :UnitGroup 1 "Cannot invert matrix ... \n"
    rethrow(e)
  end

  v = b*B

  z = Array{fmpq}(r)

  rreg = det(A)

  bound = _denominator_bound_in_relation(rreg, K)

  # Compute an upper bound in the denominator of an entry in the relation
  # using Cramer's rule and lower regulator bounds


  rel = Array{fmpz}(r + 1)
  for i in 1:r+1
    rel[i] = zero(FlintZZ)
  end

  while !inv_succesful || !_find_rational_relation!(rel, v, bound)
    p =  2*p

    inv_succesful = false

    A = _conj_log_mat_cutoff(x, p)

    Ar = base_ring(A)

    b = ArbMatSpace(Ar, 1, r)()

    conlog = conjugates_arb_log(y, p)

    for i in 1:r
      b[1, i] = conlog[i]
    end

    if !inv_succesful
      try
        @vprint :UnitGroup 1 "Inverting matrix ... \n"
        B = inv(A)
        inv_succesful = true
      catch
        @vprint :UnitGroup 1 "Cannot invert matrix. Increasing precision to $(2*p)\n"
      end
    end

    v = b*B
  end

  # Check if it is a relation modulo torsion units!
  @vprint :UnitGroup 1 "Checking relation $rel \n"

  if !_check_relation_mod_torsion(x, y, rel)
    #error("Dirty approximation did not work")
    return _find_relation(x, y, 2*p)
    #rel[r + 1 ] = 0
    #return rel
  end

  @vprint :UnitGroup 1 "Found a valid relation!\n"
  return rel
end

function _denominator_bound_in_relation(rreg::arb, K::AnticNumberField)
  # Compute an upper bound in the denominator of an entry in the relation
  # using Cramer's rule and lower regulator bounds

  arb_bound = rreg * inv(lower_regulator_bound(K))

  # I want to get an upper bound as an fmpz
  tm = arf_struct(0, 0, 0, 0)
  ccall((:arf_init, :libarb), Void, (Ptr{arf_struct}, ), &tm)

  ccall((:arb_get_abs_ubound_arf, :libarb), Void, (Ptr{arf_struct}, Ptr{arb}, Int), &tm, &arb_bound, 64)

  bound = fmpz()

  # round towards +oo
  ccall((:arf_get_fmpz, :libarb), Void, (Ptr{fmpz}, Ptr{arf_struct}, Cint), &bound, &tm, 3)

  ccall((:arf_clear, :libarb), Void, (Ptr{arf_struct}, ), &tm)

  return bound
end

function _transform(x::Array{nf_elem}, y::fmpz_mat)
  n = length(x)
  @assert n == rows(y)
  m = cols(y)
  z = Array{nf_elem}(m)
  for i in 1:m
    z[i] = x[1]^y[1, i]
    for j in 2:n
      z[i] = z[i]*x[j]^y[j, i]
    end
  end
  return z
end

function _frac_bounded_2(y::arb, bound::fmpz)
  p = prec(parent(y))
  x = _arb_get_fmpq(y)

  n = 1
  c = cfrac(x, n)[1]
  q = fmpq(c)

  new_q = q

  while nbits(num(new_q)) < div(p, 2) && nbits(den(new_q)) < div(p, 2) && den(new_q) < bound

    if contains(y, new_q)
      return true, new_q
    end

    n += 1
    c = cfrac(x, n)[1]
    new_q = fmpq(c)

  end
  return false, zero(FlintQQ)
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

function _rel_add_prec(U)
  return U.rel_add_prec
end

function _add_dependent_unit{S, T}(U::UnitGrpCtx{S}, y::T; rel_only = false)
  K = nf(order(U))
  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  p = _rel_add_prec(U)

  #p = 64

  zz = Array{fmpz}(r + 1)

  @v_do :UnitGroup 1 pushindent()
  p, B = _conj_log_mat_cutoff_inv(U, p)
  @v_do :UnitGroup 1 popindent()
  @vprint :UnitGroup 2 "Precision is now $p\n"

  Ar = base_ring(B)

  b = ArbMatSpace(Ar, 1, r)()

  conlog = conjugates_arb_log(y, p)

  for i in 1:r
    b[1, i] = conlog[i]
  end

  # I should do this using lu decomposition and caching
  # The inversion could go wrong,
  # Then we again have to increase the precision

  inv_succesful = true

  @vprint :UnitGroup 3 "For $p element b: $b\n"
  v = b*B
  @vprint :UnitGroup 3 "For $p the vector v: $v\n"

  z = Array{fmpq}(r)

  rreg = arb()

  if isdefined(U, :tentative_regulator)
    rreg = U.tentative_regulator
  else
    rreg = regulator(U.units, 64)
  end

  bound = _denominator_bound_in_relation(rreg, K)

    rel = Array{fmpz}(r + 1)
  for i in 1:r+1
    rel[i] = zero(FlintZZ)
  end

  @vprint :UnitGroup 2 "First iteration to find a rational relation ... \n"
  while !_find_rational_relation!(rel, v, bound)
    @vprint :UnitGroup 2 "Precision not high enough, increasing from $p to $(2*p)\n"
    p =  2*p
    p, B = _conj_log_mat_cutoff_inv(U, p)

    @assert p > 0

    conlog = conjugates_arb_log(y, p)

    b = ArbMatSpace(parent(conlog[1]), 1, r)()

    for i in 1:r
      b[1, i] = conlog[i]
    end

    @vprint :UnitGroup 3 "For $p element b: $b\n"

    v = b*B
    @vprint :UnitGroup 3 "For $p the vector v: $v\n"
  end

  @vprint :UnitGroup 3 "For $p rel: $rel\n"

  @vprint :UnitGroup 2 "Second iteration to check relation ... \n"

  while !_check_relation_mod_torsion(U.units, y, rel, p)
    @vprint :UnitGroup 2 "Precision not high enough, increasing from $p to $(2*p)\n"
    p = 2*p
    @assert p > 0
    p, B = _conj_log_mat_cutoff_inv(U, p)

    @assert p != 0

    conlog = conjugates_arb_log(y, p)

    b = ArbMatSpace(parent(conlog[1]), 1, r)()

    for i in 1:r
      b[1, i] = conlog[i]
    end

    @vprint :UnitGroup 3 "For $p element b: $b\n"
    v = b*B
    @vprint :UnitGroup 3 "For $p the vector v: $v\n"
    _find_rational_relation!(rel, v, bound)
    @vprint :UnitGroup 3 "For $p rel: $rel\n"
  end

  if rel_only
    return rel
  end

  if abs(rel[r + 1]) == 1 || rel[r + 1] == 0
    U.rel_add_prec = p
    return false
  end

  m = MatrixSpace(FlintZZ, r + 1, 1)(reshape(rel, r + 1, 1))

  h, u = hnf_with_transform(m)

  @assert h[1,1] == 1

  u = inv(u)

  m = submat(u, 1:r+1, 2:r+1)

  U.units =  _transform(vcat(U.units, y), m)

  U.conj_log_mat_cutoff = Dict{Int, arb_mat}()
  U.conj_log_mat_cutoff_inv = Dict{Int, arb_mat}()
  U.tentative_regulator = regulator(U.units, 64)
  U.rel_add_prec = p
  if abs(rel[r+1]) > 100 # we enlarged
    U.units = reduce(U.units, p)
  end
  return true
end

function  _conj_log_mat{T}(x::Array{T, 1}, p::Int)
  conlog = conjugates_arb_log(x[1], p)

  r, s = signature(_base_ring(x[1]))
  rr = r + s

  A = MatrixSpace(parent(conlog[1]), length(x), rr)()

  for i in 1:rr
    A[1, i] = conlog[i]
  end

  Ar = base_ring(A)

  for k in 2:length(x)
    conlog = conjugates_arb_log(x[k], p)
    for i in 1:rr
      A[k, i] = conlog[i]
    end
  end
  return A
end

function _conj_log_mat_cutoff{T}(x::Array{T, 1}, p::Int)
  r = length(x)
  conlog = conjugates_arb_log(x[1], p)
  A = ArbMatSpace(parent(conlog[1]), r, r)()

  for i in 1:r
    A[1, i] = conlog[i]
  end

  for k in 2:r
    conlog = conjugates_arb_log(x[k], p)
    for i in 1:r
      A[k, i] = conlog[i]
    end
  end
  return A
end

function _conj_log_mat_cutoff(x::UnitGrpCtx, p::Int)
  if haskey(x.conj_log_mat_cutoff,  p)
    @vprint :UnitGroup 2 "Conj matrix for $p cached\n"
    return x.conj_log_mat_cutoff[p]
  else
    @vprint :UnitGroup 2 "Conj matrix for $p not cached\n"
    x.conj_log_mat_cutoff[p] = _conj_log_mat_cutoff(x.units, p)
    return x.conj_log_mat_cutoff[p]
  end
end

function _conj_log_mat_cutoff_inv(x::UnitGrpCtx, p::Int)
  @vprint :UnitGroup 2 "Computing inverse of conjugates log matrix (starting with prec $p) ... \n"
  if haskey(x.conj_log_mat_cutoff_inv,  p)
    @vprint :UnitGroup 2 "Inverse matrix cached for $p\n"
    return p, x.conj_log_mat_cutoff_inv[p]
  else
    @vprint :UnitGroup 2 "Inverse matrix not cached for $p\n"
    try
      @vprint :UnitGroup 2 "Trying to invert conj matrix with prec $p \n"
      @vprint :UnitGroup 3 "Matrix to invert is $(_conj_log_mat_cutoff(x, p))"
      x.conj_log_mat_cutoff_inv[p] = inv(_conj_log_mat_cutoff(x, p))
      @vprint :UnitGroup 2 "Successful. Returning with prec $p \n"
      @vprint :UnitGroup 3 "$(x.conj_log_mat_cutoff_inv[p])\n"
      return p, x.conj_log_mat_cutoff_inv[p]
    catch e
      # I should check that it really is that error
      @vprint :UnitGroup 2 "Increasing precision .. (error was $e)\n"
      @v_do :UnitGroup 2 pushindent()
      r = _conj_log_mat_cutoff_inv(x, 2*p)
      @v_do :UnitGroup 2 popindent()
      return r
    end
  end
end

# Powering function for fmpz exponents
function _pow{T}(x::Array{T, 1}, y::Array{fmpz, 1})
  K = _base_ring(x[1])

  zz = deepcopy(y)

  z = Array{fmpz}(length(x))

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

doc"""
***
    regulator(x::Array{T, 1}, abs_tol::Int) -> arb

> Compute the regulator $r$ of the elements in $x$, such that the radius of $r$
> is less then `-2^abs_tol`.
"""
function regulator{T}(x::Array{T, 1}, abs_tol::Int)
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

    if isfinite(z) && radiuslttwopower(z, -abs_tol)
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

function _make_row_primitive!(x::Array{fmpz, 1})
  y = x[1]
  for i in 2:length(x)
    y = gcd(y, x[i])
    if y == 1
      return x
    end
  end
  if y > 1
    for i in 1:cols(x)
      x[i] = div(x[i], y)
    end
  end
end

################################################################################
#
#  Compute unit group from class group context
#
################################################################################

function _unit_group(O::NfMaxOrd, c::ClassGrpCtx)
  u = UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(O)
  _unit_group_find_units(u, c)
  return u
end

# TH:
# Current strategy
# ================
# Compute some "random" kernel elements using the transformation matrix to first
# find r independent units, where r is the unit rank.
# In the second round, try to enlarge the unit group with some random kernel
# elements.
function _unit_group_find_units_with_trafo(u::UnitGrpCtx, x::ClassGrpCtx)
  @vprint :UnitGroup 1 "Processing ClassGrpCtx to find units ... \n"

  @vprint :UnitGroup 1 "Relation matrix has size $(rows(x.M)) x $(cols(x.M))\n"

  O = order(u)

  #ker = transpose(ker)

  K = nf(order(x.FB.ideals[1]))
  r = unit_rank(O)
  r1, r2 = signature(O)

  A = u.units

  j = 0

  dim_ker = length(x.M.rel_gens.rows) # dimension of the kernel

  total_dim = length(x.M.bas_gens.rows) + dim_ker

  kelem = fmpz[ 0 for i in 1:total_dim ]

  trafos = x.M.trafo

  MAX_RND_RD_1 = 2*r

  time_indep = 0.0
  time_add_dep_unit = 0.0
  time_kernel = 0.0
  time_torsion = 0.0

  while(length(A) < r)

    for i in 1:length(kelem)
      kelem[i] = 0
    end

    if j > MAX_RND_RD_1
      return 0
    end
    @vprint :UnitGroup 1 "Found $(length(A)) independent units so far ($(r - length(A)) left to find)\n"
    j = j + 1

    for i in 1:dim_ker
      kelem[end - i + 1] = rand(0:1)
    end

    time_kernel += @elapsed for i in length(trafos):-1:1
      apply_right!(kelem, trafos[i])
    end

    _make_row_primitive!(kelem)

    y = FacElem(vcat(x.R_gen, x.R_rel), kelem)

    time_torsion += @elapsed is_tors, p = istorsion_unit(y, false, u.tors_prec)
    u.tors_prec = max(p, u.tors_prec)
    if is_tors
      continue
    end

    @vprint :UnitGroup 1 "Exponents are of bit size $(maximum([ nbits(o) for o in kelem]))\n"

    time_indep += @elapsed _add_unit(u, y)

  end

  @vprint :UnitGroup 1 "Found $r linear independent units \n"

  @vprint :UnitGroup 1 "Independent unit time: $time_indep\n"
  @vprint :UnitGroup 1 "Adding dependent unit time: $time_add_dep_unit\n"
  @vprint :UnitGroup 1 "Torsion test time: $time_torsion\n"
  @vprint :UnitGroup 1 "Kernel time: $time_kernel\n"

  u.full_rank = true

  u.units = reduce(u.units, u.tors_prec)

  j = 0

  not_larger = 0

  @vprint :UnitGroup 1 "Enlarging unit group by adding more kernel basis elements ...\n"
  while not_larger < 5 

    for i in 1:length(kelem)
      kelem[i] = 0
    end

    for i in 1:dim_ker
      kelem[end - i + 1] = rand(-2:2)
    end

    time_kernel += @elapsed for i in length(trafos):-1:1
      apply_right!(kelem, trafos[i])
    end

    y = FacElem(vcat(x.R_gen, x.R_rel), kelem)

    #!isunit(y) && throw(BlaError(x, kelem))

    @vprint :UnitGroup 2 "Test if kernel element yields torsion unit ... \n"
    @v_do :UnitGroup 2 pushindent()
    time_torsion += @elapsed is_tors, p = istorsion_unit(y, false, u.tors_prec)
    u.tors_prec = max(p, u.tors_prec)
    if is_tors
      @v_do :UnitGroup 2 popindent()
      @vprint :UnitGroup 2 "Element is torsion unit\n"
      continue
    end
    @v_do :UnitGroup 2 popindent()

    @v_do :UnitGroup 2 pushindent()
    time_add_dep_unit += @elapsed m = _add_dependent_unit(u, y)
    @v_do :UnitGroup 2 popindent()

    if !m
      not_larger = not_larger + 1
    else
      not_larger = 0
    end
  end

  u.tentative_regulator = regulator(u.units, 64)

  @vprint :UnitGroup 1 "Finished processing\n"
  @vprint :UnitGroup 1 "Regulator of current unit group is $(u.tentative_regulator)\n"
  @vprint :UnitGroup 1 "-"^80 * "\n"
  @vprint :UnitGroup 1 "Independent unit time: $time_indep\n"
  @vprint :UnitGroup 1 "Adding dependent unit time: $time_add_dep_unit\n"
  @vprint :UnitGroup 1 "Torsion test time: $time_torsion\n"
  @vprint :UnitGroup 1 "Kernel time: $time_kernel\n"
  return 1
end

function _unit_group_find_units(u::UnitGrpCtx, x::ClassGrpCtx)
  @vprint :UnitGroup 1 "Processing ClassGrpCtx to find units ... \n"

  @vprint :UnitGroup 1 "Relation module $(x.M)\n"

  O = order(u)

  K = nf(order(x.FB.ideals[1]))
  r = unit_rank(O)

  if r == 0
    Ar = ArbField(u.indep_prec)
    u.tentative_regulator = Ar(1)
    u.regulator = Ar(1)
    u.regulator_precision = u.indep_prec
    u.full_rank = true
    return 1
  end

  r1, r2 = signature(O)

  A = u.units

  j = 0

  MAX_RND_RD_1 = 2*r

  time_indep = 0.0
  time_add_dep_unit = 0.0
  time_kernel = 0.0
  time_torsion = 0.0

  while(length(A) < r)

    if j > MAX_RND_RD_1
      return 0
    end

    @vprint :UnitGroup 1 "Found $(length(A)) independent units so far ($(r - length(A)) left to find)\n"
    j = j + 1

    xj = rand(1:rows(x.M.rel_gens))
    time_kernel += @elapsed k, d = solve_dixon_sf(x.M.bas_gens, x.M.rel_gens[xj])
    @assert length(k.values) == 0 || gcd(foldr(gcd, k.values), d) == 1

    y = FacElem(vcat(x.R_gen[k.pos], x.R_rel[xj]), vcat(k.values, -d))
    @assert abs(norm(y)) == 1

    @vprint :UnitGroup 1 "Exponents are of bit size $(maximum([ nbits(o) for o in values(y.fac)]))\n"

    time_torsion += @elapsed is_tors, p = istorsion_unit(y, false, u.tors_prec)
    u.tors_prec = max(p, u.tors_prec)
    if is_tors
      continue
    end

    @vprint :UnitGroup 1 "Exponents are of bit size $(maximum([ nbits(o) for o in values(y.fac)]))\n"

    time_indep += @elapsed _add_unit(u, y)

  end

  @vprint :UnitGroup 1 "Found $r linear independent units \n"

  @vprint :UnitGroup 1 "Independent unit time: $time_indep\n"
  @vprint :UnitGroup 1 "Adding dependent unit time: $time_add_dep_unit\n"
  @vprint :UnitGroup 1 "Torsion test time: $time_torsion\n"
  @vprint :UnitGroup 1 "Kernel time: $time_kernel\n"

  u.full_rank = true

  u.units = reduce(u.units, u.tors_prec)

  j = 0

  not_larger = 0

  @vprint :UnitGroup 1 "Enlarging unit group by adding remaining kernel basis elements ...\n"
  while not_larger < 5 

    add = []
    rel = SMat{fmpz}()
    for jj in 1:min(div(rows(x.M.rel_gens), 10)+1, 20)
      xj = rand(1:rows(x.M.rel_gens))
      if xj in add
        continue
      end
      push!(add, xj)
      push!(rel, x.M.rel_gens[xj])
    end

    time_kernel += @elapsed k, d = solve_dixon_sf(x.M.bas_gens, rel)
    time_kernel += @elapsed s = saturate(hcat(k, (-d)*id(SMat, FlintZZ, k.r)))

    ge = vcat(x.R_gen[1:k.c], x.R_rel[add])
    for i=1:s.r
      y = FacElem(ge[s[i].pos], s[i].values)
      @assert abs(norm(y)) == 1

      @vprint :UnitGroup 1 "Exponents are of bit size $(maximum([ nbits(o) for o in values(y.fac)]))\n"

      @vprint :UnitGroup 2 "Test if kernel element yields torsion unit ... \n"
      @v_do :UnitGroup 2 pushindent()
      time_torsion += @elapsed is_tors, p = istorsion_unit(y, false, u.tors_prec)
      u.tors_prec = max(p, u.tors_prec)
      if is_tors
        @v_do :UnitGroup 2 popindent()
        #println("torsion unit: $y")
        @vprint :UnitGroup 2 "Element is torsion unit\n"
        continue
      end
      @vprint :UnitGroup 2 "Element is non-torsion unit\n"
      @v_do :UnitGroup 2 popindent()

      @v_do :UnitGroup 2 pushindent()
      time_add_dep_unit += @elapsed m = _add_dependent_unit(u, y)
      @v_do :UnitGroup 2 popindent()

      if !m
        not_larger = not_larger + 1
      else
        not_larger = 0
      end
    end
  end

  u.tentative_regulator = regulator(u.units, 64)

  @vprint :UnitGroup 1 "Finished processing\n"
  @vprint :UnitGroup 1 "Regulator of current unit group is $(u.tentative_regulator)\n"
  @vprint :UnitGroup 1 "-"^80 * "\n"
  @vprint :UnitGroup 1 "Independent unit time: $time_indep\n"
  @vprint :UnitGroup 1 "Adding dependent unit time: $time_add_dep_unit\n"
  @vprint :UnitGroup 1 "Torsion test time: $time_torsion\n"
  @vprint :UnitGroup 1 "Kernel time: $time_kernel\n"
  return 1
end


function _add_unit(u::UnitGrpCtx, x::FacElem{nf_elem, AnticNumberField})
  isindep, p = isindependent(vcat(u.units, [x]), u.indep_prec)
  u.indep_prec = max(p, u.indep_prec)
  if isindep
    push!(u.units, x)
  end
end

################################################################################
#
#  Size reduction
#
################################################################################

function _reduce_size{T}(x::Array{T, 1}, prec::Int = 64)
  K = _base_ring(x[1])

  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  conlog = conjugates_arb_log(x[1], prec)

  A = MatrixSpace(parent(conlog[1]), length(x), rr)()

  B = MatrixSpace(FlintZZ, rows(A), cols(A))()

  for i in 1:rr
    A[1, i] = conlog[i]
  end

  Ar = base_ring(A)

  for i in 1:rows(A)
    for j in 1:cols(A)
      b, y = unique_integer(ceil(ldexp(A[i, j], 64)))
      @assert b
      B[i, j] = y
    end
  end

  L, U = lll_with_transform(B)
end


################################################################################
#
#  Saturation
#
################################################################################

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
function _is_saturated(U::UnitGrpCtx, p::Int, B::Int = 2^30 - 1, proof::Bool = false)
  if proof
    error("Not yet implemented")
  end

  N = 3*unit_rank(order(U))

  @vprint :UnitGroup 1 "Computing $N prime ideals for saturation ...\n"

  primes =  _find_primes_for_saturation(order(U), p, N, B)

  m = _matrix_for_saturation(U, primes[1], p)

  for i in 2:N
    m = vcat(m, _matrix_for_saturation(U, primes[i], p))
  end

  @vprint :UnitGroup 1 "Computing kernel of p-th power map ...\n"
  (K, k) = _right_kernel(m)

  K = transpose(K)
  L = lift(K)
  T = typeof(L[1,1])

  nonzerorows = Array{Int, 1}()

  for j in 1:rows(L)
    if !iszero_row(L, j)
      push!(nonzerorows, j)
    end
  end

  if k == 0 
    return (true, zero(nf(order(U))))
  elseif k == 1 && sum(T[ L[nonzerorows[1], i]::T for i in 1:cols(L)-1]) == 0
    # Only one root, which is torsion.
    # We assume that the torsion group is the full torsion group
    return (true, zero(nf(order(U))))
  else
    for j in nonzerorows
      a = U.units[1]^(L[j, 1])
      for i in 2:length(U.units)
        a = a*U.units[i]^L[j, i]
      end

      if gcd(p, U.torsion_units_order) != 1
        a = a*elem_in_nf(U.torsion_units_gen)^L[j, length(U.units) + 1]
      end

      b = evaluate(a)

      @vprint :UnitGroup 1 "Testing/computing root ... \n"

      @vprint :UnitGroup 1 "Bitsize of coefficient $([nbits(elem_in_basis(U.order(b))[i]) for i in 1:degree(U.order)])"

      #has_root, roota = root(b, p)
      has_root, _roota = ispower(U.order(b), p)
      roota = elem_in_nf(_roota)


      if !has_root
        continue
      end

      return (false, roota)
    end
  end

  # try some random linear combination of kernel vectors

  MAX = 10

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

    b = evaluate(a)

    #has_root, roota = root(b, p)
    has_root, _roota = ispower(U.order(b), p)
    roota = elem_in_nf(_roota)


    if has_root
      return (false, roota)
    end
  end

  return (true, zero(nf(order(U))))
end

# The output will be of type
# elem_type(MatrixSpace(ResidueRing(ZZ, p), 1, rank(U) ( + 1))), so
# nmod_mat or fmpz_mod_mat
# THIS FUNCTION IS NOT TYPE STABLE
function _matrix_for_saturation(U::UnitGrpCtx, P::NfMaxOrdIdl, p::Int)
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
      t = b*anti_uniformizer(P.gen_two)^(valuation(b, P))

      #if mod(den(t), minimum(P)) == 0
      #  l = valuation(den(t), P)
      #  y = y*(mK(t*elem_in_nf(P.anti_uniformizer)^l)*mF(P.anti_uniformizer)^(-l))^u.fac[b]
      #else
        y = y*mK(t)^u.fac[b]
      #end
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
function _find_primes_for_saturation(O::NfMaxOrd, p::Int, n::Int,
                                     st::Int = 0)
  res = Array{NfMaxOrdIdl}(n)
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
  #println("Computing primitive element of $F")
  #println("Have to factor $(order(F) - 1)")
  fac = factor(order(F) - 1)
  while true
    a = rand(F)
    if iszero(a)
      continue
    end
    is_primitive = true
    for (l, ll) in fac
      if isone(a^(div(order(F) - 1, l)))
        is_primitive = false
        break
      end
    end
    if is_primitive
      return a
    end
  end
end

function _refine_with_saturation(c::ClassGrpCtx, u::UnitGrpCtx)
  @vprint :UnitGroup "Enlarging unit group using saturation ... \n"

  b = _validate_class_unit_group(c, u)

  p = 2

  while b > 1
    @vprint :UnitGroup 1 "Saturating at $p ... \n"

    @v_do :UnitGroup 1 pushindent()
    issat, new_unit = _is_saturated(u, p)
    @v_do :UnitGroup 1 popindent()

    while !issat
      #println("I have found a new unit: $new_unit")
      _add_dependent_unit(u, FacElem(new_unit))
      #println("$(u.tentative_regulator)")

      @v_do :UnitGroup 1 pushindent()
      b = _validate_class_unit_group(c, u)
      @v_do :UnitGroup 1 popindent()

      if b == 1
        break
      end

      @v_do :UnitGroup 1 pushindent()
      issat, new_unit = _is_saturated(u, p)
      @v_do :UnitGroup 1 popindent()
    end

    @v_do :UnitGroup 1 pushindent()
    b = _validate_class_unit_group(c, u)
    @v_do :UnitGroup 1 popindent()

    p = next_prime(p)
    if p > b
      break
    end
  end
  return b
end

################################################################################
#
#  Reduce units using LLL
#
################################################################################

function scaled_log_matrix{T}(u::Array{T, 1}, prec::Int = 32)

  r,s = signature(_base_ring(u[1]))
  A = MatrixSpace(ZZ, length(u), r + s)()
  prec = max(prec, maximum([nbits(maxabs_exp(U))+nbits(length(U.fac)) for U = u]))
  @vprint :UnitGroup 2 "starting prec in scaled_log_matrix: $prec\n"

  for i in 1:length(u)
    c = conjugates_arb_log(u[i], prec)
    if any(x->radius(x) > 1e-9, c)  # too small...
      @vprint :UnitGroup 2 "increasing prec in scaled_log_matrix, now: $prec"
      prec *= 2
      if prec > 2^32
        error("cannot do lll on units")
        break
      end
    end
    for j in 1:length(c)
      tt = fmpz()
      t = ccall((:arb_mid_ptr, :libarb), Ptr{arf_struct}, (Ptr{arb}, ), &c[j])
      l = ccall((:arf_get_fmpz_fixed_si, :libarb), Int, (Ptr{fmpz}, Ptr{arf_struct}, Int), &tt, t, -prec)
      A[i, j] = tt
    end
  end
  return A, prec
end

function row_norm(A::fmpz_mat, i::Int)
  return sum([A[i,j]^2 for j=1:cols(A)])
end

function row_norms(A::fmpz_mat)
  return [row_norm(A, i) for i=1:rows(A)]
end


function reduce{T}(u::Array{T, 1}, prec::Int = 32)
  r = length(u)
  if r == 0
    return u
  end

  while true
    A, prec = scaled_log_matrix(u, prec)

    L, U = lll_with_transform(A)
    @vprint :UnitGroup 2 "reducing units by $U\n"
    pA = prod(row_norms(A))
    pL = prod(row_norms(L))
    @vprint :UnitGroup 1 "reducing norms of logs from $pA -> $pL, rat is $(Float64(1.0*pA//pL))"
    u = transform(u, transpose(U))
    if pL >= pA
      return u
    end
  end  
end

################################################################################
#
#  High level interface
#
################################################################################

function lower_regulator_bound(K::AnticNumberField)
  return ArbField(64)("0.054")
end
