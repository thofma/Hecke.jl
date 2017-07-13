################################################################################
#
#    NfOrd/NfOrd.jl : Orders in absolute number fields
#
# This file is part of hecke.
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
#  Copyright (C) 2015, 2016, 2017 Tommy Hofmann
#
################################################################################

export ==, +, basis, basis_mat, basis_mat_inv, discriminant, degree, den,
       gen_index, EquationOrder, index, isequation_order, isindex_divisor, lll,
       lll_basis, maximal_order, minkowski_mat, nf, norm_change_const, Order,
       parent, poverorder, pmaximal_overorder, ring_of_integers, signature,
       trace_matrix

################################################################################
#
#  Make NfOrd fully working Nemo ring
#
################################################################################

Nemo.parent_type(::Type{NfOrdElem}) = NfOrd

Nemo.elem_type(::Type{NfOrd}) = NfOrdElem

Nemo.elem_type(::NfOrd) = NfOrdElem

################################################################################
#
#  Basic field access
#
################################################################################

doc"""
    nf(O::NfOrd) -> AnticNumberField

Returns the ambient number field of $\mathcal O$.
"""
@inline nf(O::NfOrd) = O.nf

doc"""
    parent(O::NfOrd) -> NfOrdSet

Returns the parent of $\mathcal O$, that is, the set of orders of the ambient
number field.
"""
@inline parent(O::NfOrd) = O.parent

doc"""
    isequation_order(O::NfOrd) -> Bool

Returns whether $\mathcal O$ is the equation order of the ambient number
field.
"""
@inline isequation_order(O::NfOrd) = O.isequation_order

@inline ismaximal_known(O::NfOrd) = O.ismaximal != 0

# The following function should actually do more!
@inline ismaximal(O::NfOrd) = O.ismaximal == 1

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_basis(O::NfOrd)
  if isdefined(O, :basis_ord)
    return nothing
  end
  b = O.basis_nf
  d = degree(O)
  B = Vector{NfOrdElem}(d)
  for i in 1:length(b)
    v = [fmpz(0) for j in 1:d]
    one!(v[i])
    B[i] = NfOrdElem(O, b[i], v)
  end
  O.basis_ord = B
  return nothing
end

function assure_has_basis_mat(O::NfOrd)
  if isdefined(O, :basis_mat)
    return nothing
  end
  A = O.basis_nf
  O.basis_mat = FakeFmpqMat(basis_mat(A))
  return nothing
end

function assure_has_basis_mat_inv(O::NfOrd)
  if isdefined(O, :basis_mat_inv)
    return nothing
  end
  O.basis_mat_inv = inv(basis_mat(O))
  return nothing
end

################################################################################
#
#  Basis
#
################################################################################

function basis_ord{T}(O::NfOrd, copy::Type{Val{T}} = Val{true})
  assure_has_basis(O)
  if copy == Val{true}
    return deepcopy(O.basis_ord)::Vector{NfOrdElem}
  else
    return O.basis_ord::Vector{NfOrdElem}
  end
end

doc"""
    basis(O::NfOrd) -> Array{NfOrdElem, 1}

Returns the $\mathbf Z$-basis of $\mathcal O$.
"""
@inline basis{T}(O::NfOrd, copy::Type{Val{T}} = Val{true}) = basis_ord(O, copy)

doc"""
    basis(O::NfOrd, K::AnticNumberField) -> Vector{nf_elem}

Returns the $\mathbf Z$-basis elements of $\mathcal O$ as elements of the
ambient number field.
"""
function basis(O::NfOrd, K::AnticNumberField)
  nf(O) != K && error()
  return deepcopy(O.basis_nf)
end

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

doc"""
    basis_mat(O::NfOrd) -> FakeFmpqMat

Returns the basis matrix of $\mathcal O$ with respect to the power basis
of the ambient number field.
"""
function basis_mat(O::NfOrd)
  assure_has_basis_mat(O)
  return deepcopy(O.basis_mat)
end

doc"""
    basis_mat_inv(O::NfOrd) -> FakeFmpqMat

Returns the inverse of the basis matrix of $\mathcal O$.
"""
function basis_mat_inv(O::NfOrd)
  assure_has_basis_mat_inv(O)
  return deepcopy(O.basis_mat_inv)
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, S::NfOrdSet)
  print(io, "Set of orders of the number field ")
  print(io, S.nf)
end

function show(io::IO, O::NfOrd)
  if ismaximal_known(O) && ismaximal(O)
    show_maximal(io, O)
  else
    show_gen(io, O)
  end
end

function show_gen(io::IO, O::NfOrd)
  print(io, "Order of ")
  println(io, nf(O))
  print(io, "with Z-basis ")
  print(io, basis(O))
end

function show_maximal(io::IO, O::NfOrd)
  print(io, "Maximal order of $(nf(O)) \nwith basis $(O.basis_nf)")
end

################################################################################
#
#  Discriminant
#
################################################################################

doc"""
    discriminant(O::NfOrd) -> fmpz

Returns the discriminant of $\mathcal O$.
"""
function discriminant(O::NfOrd)
  if isdefined(O, :disc)
    return deepcopy(O.disc)
  end

  if isequation_order(O)
    O.disc = num(discriminant(nf(O).pol))
  else
    O.disc = discriminant(basis(O))
  end

  return deepcopy(O.disc)
end

################################################################################
#
#  Degree
#
################################################################################

doc"""
    degree(O::NfOrd) -> Int

Returns the degree of $\mathcal O$.
"""
degree(O::NfOrd) = degree(O.nf)

################################################################################
#
#  (Generalized) index
#
################################################################################

doc"""
    gen_index(O::NfOrd) -> fmpq

Generalized index of $\mathcal O$ with respect to the ambient equation
order $\mathbf Z[\alpha]$.
"""
function gen_index(O::NfOrd)
  if isdefined(O, :gen_index)
    return deepcopy(O.gen_index)
  else
    assure_has_basis_mat(O)
    O.gen_index = FlintQQ(O.basis_mat.den^degree(O), det(O.basis_mat.num))
    return deepcopy(O.gen_index)
  end
end

doc"""
    index(O::NfOrd) -> fmpz

Assuming that the order $\mathcal O$ contains the ambient equation order
$\mathbf Z[\alpha]$, this function returns the index
$[ \mathcal O : \mathbf ZZ]$.
"""
function index(O::NfOrd)
  if isdefined(O, :index)
    return deepcopy(O.index)
  else
    i = gen_index(O)
    !isone(den(i)) && error("Order does not contain the equation order")
    O.index = num(i)
    return deepcopy(O.index)
  end
end

################################################################################
#
#  Index divisor
#
################################################################################

doc"""
    isindex_divisor(O::NfOrd, d::fmpz) -> Bool
    isindex_divisor(O::NfOrd, d::Int) -> Bool

Returns whether $d$ is a divisor of the index of $\mathcal O$.
"""
function isindex_divisor(O::NfOrd, d::Union{fmpz, Int})
  i = index(O)
  return i % d == 0
end

################################################################################
#
#  Deepcopy
#
################################################################################

doc"""
    deepcopy(O::NfOrd) -> NfOrd

Makes a copy of $\mathcal O$.
"""
function Base.deepcopy_internal(O::NfOrd, dict::ObjectIdDict)
  z = NfOrd(O.nf)
  for x in fieldnames(O)
    # TODO
    # This is slow. Julia can't infere the type of the right hand side.
    # (According to @code_warntype).
    if x != :nf && x != :parent && isdefined(O, x)
      setfield!(z, x, Base.deepcopy_internal(getfield(O, x), dict))
    end
  end
  z.nf = O.nf
  z.parent = O.parent
  return z
end

################################################################################
#
#  Signature
#
################################################################################

doc"""
    signature(O::NfOrd) -> Tuple{Int, Int}

Returns the signature of the ambient number field of $\mathcal O$.
"""
function signature(x::NfOrd)
  if x.signature[1] != -1
    return x.signature
  else
    x.signature = signature(nf(x))
    return x.signature
  end
end

################################################################################
#
#  Minkowski matrix
#
################################################################################

doc"""
    minkowski_mat(O::NfOrd, abs_tol::Int = 64) -> arb_mat

Returns the Minkowski matrix of $\mathcal O$.
Thus if $\mathcal O$ has degree $d$, then the
result is a matrix in $\operatorname{Mat}_{d\times d}(\mathbf R)$.
The entries of the matrix are real balls of type `arb` with radius
less then `2^-abs_tol`.
"""
function minkowski_mat(O::NfOrd, abs_tol::Int = 64)
  if isdefined(O, :minkowski_mat) && O.minkowski_mat[2] > abs_tol
    A = deepcopy(O.minkowski_mat[1])
  else
    T = Vector{Vector{arb}}(degree(O))
    B = O.basis_nf
    for i in 1:degree(O)
      T[i] = minkowski_map(B[i], abs_tol)
    end
    p = maximum([ prec(parent(T[i][j])) for i in 1:degree(O), j in 1:degree(O) ])
    M = ArbMatSpace(ArbField(p), degree(O), degree(O))()
    for i in 1:degree(O)
      for j in 1:degree(O)
        M[i, j] = T[i][j]
      end
    end
    O.minkowski_mat = (M, abs_tol)
    A = deepcopy(M)
  end
  return A
end

################################################################################
#
#  Inclusion of number field elements
#
################################################################################

# Check if a number field element is contained in O
# In this case, the second return value is the coefficient vector with respect
# to the basis of O
function _check_elem_in_order{T}(a::nf_elem, O::NfOrd,
                                 short::Type{Val{T}} = Val{false})
  assure_has_basis_mat_inv(O)
  t = O.tcontain
  elem_to_mat_row!(t.num, 1, t.den, a)
  t = mul!(t, t, O.basis_mat_inv)
  if short == Val{true}
    return isone(t.den)
  else
    if !isone(t.den)
      return false, Vector{fmpz}()
    else
      v = Vector{fmpz}(degree(O))
      for i in 1:degree(O)
        v[i] = deepcopy(t.num[1, i])
      end
      return true, v
    end
  end
end

doc"""
    in(a::nf_elem, O::NfOrd) -> Bool

Checks whether $a$ lies in $\mathcal O$.
"""
function in(a::nf_elem, O::NfOrd)
  return _check_elem_in_order(a, O, Val{true})
end

################################################################################
#
#  Denominator in an order
#
################################################################################

doc"""
    den(a::nf_elem, O::NfOrd) -> fmpz

Returns the smallest positive integer $k$ such that $k \cdot a$ lies in O.
"""
function den(a::nf_elem, O::NfOrd)
  assure_has_basis_mat_inv(O)
  M = O.tcontain
  elem_to_mat_row!(M.num, 1, M.den, a)
  M = mul!(M, M, O.basis_mat_inv)
  return deepcopy(M.den)
end

##################################3#############################################
#
#  Norm change constant
#
################################################################################

# For x = \sum_i x_i omega_i let |x|_1 = \sqrt(x_1^2 + ... + x_d^2).
# And let |x|_2 = sqrt(T_2(x))
# Then there exist c1, c2 such that
# |x|_2^2 <= c1 |x|_2^2, |x|_1^2 <= c2 |x|_1^2
# A suitable pair (c1, c2) can be determined using the Minkowski map/matrix
#
# Reference
# Fieker, Friedrichs
# On Reconstruction of Algebraic Numbers
# (in particular p. 288)
doc"""
    norm_change_const(O::NfOrd) -> (Float64, Float64)

Returns $(c_1, c_2) \in \mathbf R_{>0}^2$ such that for all
$x = \sum_{i=1}^d x_i \omega_i \in \mathcal O$ we have
$T_2(x) \leq c_1 \cdot \sum_i^d x_i^2$
and
$\sum_i^d x_i^2 \leq c_2 \cdot T_2(x)$,
where $(\omega_i)_i$ is the $\mathbf Z$-basis of $\mathcal O$.
"""
function norm_change_const(O::NfOrd)
  if O.norm_change_const[1] > 0
    return O.norm_change_const
  else
    d = degree(O)
    M = minkowski_mat(O, 64)
    # I need to swap rows (really?)
    # I don't think we have to swap rows,
    # since permutation matrices are orthogonal
    #r1, r2 = signature(O)
    #for i in 2:2:r2
    #  swap_rows!(M, r1 + i, r1 + 2*r2 - i + 1)
    #end

    M = M*M'

    N = Symmetric([ Float64(M[i, j]) for i in 1:rows(M), j in 1:cols(M) ])
    #forcing N to really be Symmetric helps julia - aparently
    r = sort(eigvals(N))
    if !(r[1] > 0)
      # more complicated methods are called for...
      l_max = root(trace(M^d), d) #an upper bound within a factor of 2
                                    #according to a paper by Victor Pan
      pr = 128
      l_min = l_max
      if isodd(d) d+=1; end
      while true
        try
          M = inv(M)
          l_min = root(trace(M^d), d) #as above...
          if isfinite(l_min)
            z = (Float64(l_max), Float64(l_min))
            O.norm_change_const = z
            return z
          end
          M = minkowski_mat(O, pr)
          pr *= 2
        catch e  # should verify the correct error
          M = minkowski_mat(O, pr)
          pr *= 2
        end
      end
    end

    @assert r[1]>0
#    N = transpose(M)*M
#    N = MatrixSpace(AcbField(prec(base_ring(N))), rows(N), cols(N))(N)
#    chi = charpoly(PolynomialRing(base_ring(N), "x")[1], N)
#    return chi
#    r = roots(chi)
#    # I want upper bound for the largest and lower bound for the smallest root
#
#    tm = arf_struct(0, 0, 0, 0)
#    ccall((:arf_init, :libarb), Void, (Ptr{arf_struct}, ), &tm)
#    ccall((:arb_get_abs_ubound_arf, :libarb), Void, (Ptr{arf_struct}, Ptr{arb}), &tm, &real(r[end]))
#    # 3 is round to infinity
#    c1 = ccall((:arf_get_d, :libarb), Cdouble, (Ptr{arf_struct}, Cint), &tm, 3)
#
#    ccall((:arb_get_abs_ubound_arf, :libarb), Void, (Ptr{arf_struct}, Ptr{arb}), &tm, &(inv(real(r[1]))))
#    c2 = ccall((:arf_get_d, :libarb), Cdouble, (Ptr{arf_struct}, Cint), &tm, 3)
#
#    ccall((:arf_clear, :libarb), Void, (Ptr{arf_struct}, ), &tm)
#
#    z = (c1, c2)
    z = (r[end], inv(r[1]))
    O.norm_change_const = z
    return z
  end
end

################################################################################
#
#  Construction
#
################################################################################

doc"""
    Order(B::Array{nf_elem, 1}, check::Bool = true) -> NfOrd

Returns the order with $\mathbf Z$-basis $B$. If `check` is set, it is checked
whether $B$ defines an order.
"""
function Order(::AnticNumberField, a::Array{nf_elem, 1}, check::Bool = true,
               cache::Bool = true)
  K = parent(a[1])
  if check
    b, bmat, bmat_inv, _ = defines_order(K, a)
    if !b
      error("The elements do not define an order")
    else
      return NfOrd(K, bmat, bmat_inv, deepcopy(a), cache)
    end
  else
    return NfOrd(deepcopy(a), cache)
  end
end

function Order(K::AnticNumberField, a::Vector, check::Bool = true,
               cache::Bool = true)
  local b
  try
    b = map(K, a)
  catch
    error("Cannot coerce elements from array into the number field")
  end
  return Order(K, b, check, cache)
end

doc"""
    Order(K::AnticNumberField, A::FakeFmpqMat, check::Bool = true) -> NfOrd

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function Order(K::AnticNumberField, a::FakeFmpqMat, check::Bool = true,
               cache::Bool = true)
  if check
    b, ainv, d = defines_order(K, a)
    if !b
      error("The basis matrix does not define an order")
    else
      return NfOrd(K, deepcopy(a), ainv, d, cache)
    end
  else
    return NfOrd(K, deepcopy(a), cache)
  end
end

doc"""
    Order(K::AnticNumberField, A::fmpq_mat, check::Bool = true) -> NfOrd

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function Order(K::AnticNumberField, a::fmpq_mat, check::Bool = true,
               cache::Bool = true)
  return Order(K, FakeFmpqMat(a), cache)
end

doc"""
    Order(K::AnticNumberField, A::fmpz_mat, check::Bool = true) -> NfOrd

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function Order(K::AnticNumberField, a::fmpz_mat, check::Bool = true,
               cache::Bool = true)
  return Order(K, FakeFmpqMat(a), check, cache)
end

doc"""
    Order(A::NfOrdFracIdl) -> NfOrd

Returns the fractional ideal $A$ as an order of the ambient number field.
"""
function Order(a::NfOrdFracIdl, check::Bool = true, cache::Bool = true)
  return Order(nf(order(a)), basis_mat(a)*basis_mat(order(a)), check, cache)
end

doc"""
    EquationOrder(K::AnticNumberField) -> NfOrd

Returns the equation order of the number field $K$.
"""
function EquationOrder(K::AnticNumberField, cache::Bool = true)
  M = FakeFmpqMat(one(MatrixSpace(FlintZZ, degree(K), degree(K))))
  Minv = FakeFmpqMat(one(MatrixSpace(FlintZZ, degree(K), degree(K))))
  z = NfOrd(K, M, Minv, [gen(K)^i for i in 0:(degree(K) - 1)], cache)
  z.isequation_order = true
  return z
end

################################################################################
#
#  Equality
#
################################################################################

# this is used in dictionaries
function Base.isequal(R::NfOrd, S::NfOrd)
  return R === S
end

function ==(R::NfOrd, S::NfOrd)
  nf(R) != nf(S) && return false
  assure_has_basis_mat(R)
  assure_has_basis_mat(S)
  return R.basis_mat == S.basis_mat
end

################################################################################
#
#  Trace matrix
#
################################################################################

function trace_matrix(O::NfOrd)
  if isdefined(O, :trace_mat)
    return deepcopy(O.trace_mat)
  end
  K = nf(O)
  b = O.basis_nf
  n = degree(K)
  g = MatrixSpace(FlintZZ, n, n)()
  for i=1:n
    t = trace(b[i]^2)
    @assert isinteger(t)
    g[i, i] = num(t)
    for j in (i + 1):n
      t = trace(b[i]*b[j])
      @assert isinteger(t)
      g[i, j] = num(t)
      g[j, i] = num(t)
    end
  end
  O.trace_mat = g
  return deepcopy(g)
end

################################################################################
#
#  Addition of orders
#
################################################################################

doc"""
    +(R::NfOrd, S::NfOrd) -> NfOrd

Given two orders $R$, $S$ of $K$, this function returns the smallest order
containing both $R$ and $S$. It is assumed that $R$, $S$ contain the ambient
equation order and have coprime index.
"""
function +(a::NfOrd, b::NfOrd)
  parent(a) != parent(b) && error("Orders must have same ambient number field")
  !isone(gcd(index(a), index(b))) && error("Indice must be coprime")
  assure_has_basis_mat(a)
  assure_has_basis_mat(b)
  aB = a.basis_mat
  bB = b.basis_mat
  d = degree(a)
  c = sub(_hnf(vcat(bB.den*aB.num, aB.den*bB.num), :lowerleft), d + 1:2*d, 1:d)
  O = Order(nf(a), FakeFmpqMat(c, aB.den*bB.den))
  O.primesofmaximality = unique(vcat(a.primesofmaximality, b.primesofmaximality))
  return O
end

################################################################################
#
#  p-overorder
#
################################################################################

function _poverorder(O::NfOrd, p::fmpz)
  R = ring_of_multipliers(pradical(O, p))
  return R
end

function _poverorder(O::NfOrd, p::Integer)
  return _poverorder(O, fmpz(p))
end

doc"""
    poverorder(O::NfOrd, p::fmpz) -> NfOrd
    poverorder(O::NfOrd, p::Integer) -> NfOrd

This function tries to find an order that is locally larger than $\mathcal O$
at the prime $p$: If $p$ divides the index $[ \mathcal O_K : \mathcal O]$,
this function will return an order $R$ such that
$v_p([ \mathcal O_K : R]) < v_p([ \mathcal O_K : \mathcal O])$. Otherwise
$\mathcal O$ is returned.
"""
function poverorder(O::NfOrd, p::fmpz)
  if isequation_order(O)
    return dedekind_poverorder(O, p)
  else
    return _poverorder(O, p)
  end
end

function poverorder(O::NfOrd, p::Integer)
  return poverorder(O::NfOrd, fmpz(p))
end

################################################################################
#
#  p-maximal overorder
#
################################################################################

doc"""
    pmaximal_overorder(O::NfOrd, p::fmpz) -> NfOrd
    pmaximal_overorder(O::NfOrd, p::Integer) -> NfOrd

This function finds a $p$-maximal order $R$ containing $\mathcal O$. That is,
the index $[ \mathcal O_K : R]$ is not dividible by $p$.
"""
function pmaximal_overorder(O::NfOrd, p::fmpz)
  @vprint :NfOrd 1 "computing p-maximal overorder for $p ... \n"
  if rem(discriminant(O), p) != 0
    push!(O.primesofmaximality, p)
    return O
  end

  d = discriminant(O)
  @vprint :NfOrd 1 "extending the order at $p for the first time ... \n"
  OO = poverorder(O, p)
  dd = discriminant(OO)
  i = 1
  while d != dd
    i += 1
    @vprint :NfOrd 1 "extending the order at $p for the $(i)th time ... \n"
    d = dd
    OO = poverorder(OO, p)
    dd = discriminant(OO)
  end
  push!(OO.primesofmaximality, p)
  return OO
end

function pmaximal_overorder(O::NfOrd, p::Integer)
  return pmaximal_overorder(O, fmpz(p))
end

function MaximalOrder(O::NfOrd, primes::Array{fmpz, 1})
  OO = deepcopy(O)
  disc = abs(discriminant(O))
  for i in 1:length(primes)
    p = primes[i]
    (j, disc) = remove(disc, p)
    if j == 1
      continue
    end
    @vprint :NfOrd 1 "Computing p-maximal overorder for $p ..."
    OO += pmaximal_overorder(O, p)
    @vprint :NfOrd 1 "done\n"
  end
  return OO
end

function MaximalOrder(O::NfOrd)
  OO = deepcopy(O)
  @vtime :NfOrd fac = factor(Nemo.abs(discriminant(O)))
  for (p,j) in fac
    if j == 1
      continue
    end
    @vprint :NfOrd 1 "Computing p-maximal overorder for $p ..."
    OO += pmaximal_overorder(O, p)
    @vprint :NfOrd 1 "done\n"
  end
  return OO
end

# don't know what this is doing

function _lll_gram(M::NfOrd)
  K = nf(M)
  @assert istotally_real(K)
  g = trace_matrix(M)

  q,w = lll_gram_with_transform(g)
  On = NfOrd(K, FakeFmpqMat(w*basis_mat(M).num, basis_mat(M).den))
  On.ismaximal = M.ismaximal
  return On
end

function lll_basis(M::NfOrd)
  I = hecke.ideal(M, parent(basis_mat(M).num)(1))
  return lll_basis(I)
end

function lll(M::NfOrd)
  K = nf(M)

  if istotally_real(K)
    return _lll_gram(M)
  end

  I = hecke.ideal(M, parent(basis_mat(M).num)(1))

  prec = 100
  while true
    try
      q,w = lll(I, parent(basis_mat(M).num)(0), prec = prec)
      On = NfOrd(K, FakeFmpqMat(w*basis_mat(M).num, basis_mat(M).den))
      On.ismaximal = M.ismaximal
      return On
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
#  Constructors for users
#
################################################################################

doc"""
***
    MaximalOrder(K::AnticNumberField) -> NfOrd

Returns the maximal order of $K$.
**Example**

    julia> Qx, x = QQ["x"]
    julia> K, a = NumberField(x^3 + 2, "a")
    julia> O = MaximalOrder(K)
"""
function MaximalOrder(K::AnticNumberField, cache::Bool = true)
  O = EquationOrder(K)
  @vprint :NfOrd 1 "Computing the maximal order ...\n"
  O = MaximalOrder(O)
  @vprint :NfOrd 1 "... done\n"
  M = NfOrd(K, basis_mat(O), cache)
  M.ismaximal = 1
  return M
end

doc"""
***
    MaximalOrder(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd

Assuming that ``primes`` contains all the prime numbers at which the equation
order $\mathbf{Z}[\alpha]$ of $K = \mathbf{Q}(\alpha)$ is not maximal,
this function returns the maximal order of $K$.
"""
function MaximalOrder(K::AnticNumberField, primes::Array{fmpz, 1})
  O = EquationOrder(K)
  @vprint :NfOrd 1 "Computing the maximal order ...\n"
  O = MaximalOrder(O, primes)
  @vprint :NfOrd 1 "... done\n"
  return NfOrd(K, basis_mat(O))
end

doc"""
***
    maximal_order(K::AnticNumberField) -> NfOrd
    ring_of_integers(K::AnticNumberField) -> NfOrd

Returns the maximal order of $K$.
"""
function maximal_order(K::AnticNumberField)
  try
    c = _get_maximal_order_of_nf(K)::NfOrd
    return c
  catch e
    if !isa(e, AccessorNotSetError)
      rethrow(e)
    end
    O = MaximalOrder(K)::NfOrd
    _set_maximal_order_of_nf(K, O)
    return O
  end
end

doc"""
***
    maximal_order(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd
    maximal_order(K::AnticNumberField, primes::Array{Integer, 1}) -> NfOrd
    ring_of_integers(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd
    ring_of_integers(K::AnticNumberField, primes::Array{Integer, 1}) -> NfOrd

Assuming that ``primes`` contains all the prime numbers at which the equation
order $\mathbf{Z}[\alpha]$ of $K = \mathbf{Q}(\alpha)$ is not maximal
(e.g. ``primes`` may contain all prime divisors of the discriminant of
$\mathbf Z[\alpha]$), this function returns the maximal order of $K$.
"""
function maximal_order(K::AnticNumberField, primes::Array{fmpz, 1})
  O = MaximalOrder(K, primes)
  return O
end

maximal_order{T}(K::AnticNumberField, primes::Array{T, 1}) =
  maximal_order(K, map(FlintZZ, primes))

doc"""
***
    maximal_order(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd
    maximal_order(K::AnticNumberField, primes::Array{Integer, 1}) -> NfOrd
    ring_of_integers(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd
    ring_of_integers(K::AnticNumberField, primes::Array{Integer, 1}) -> NfOrd

Assuming that ``primes`` contains all the prime numbers at which the equation
order $\mathbf{Z}[\alpha]$ of $K = \mathbf{Q}(\alpha)$ is not maximal,
this function returns the maximal order of $K$.
"""
ring_of_integers(x...) = maximal_order(x...)

################################################################################
#
#  Check if something defines an order
#
################################################################################

# this is not optimizied for performance
# if false, then this returns (false, garbage, garbage)
# if true, then this return (true, basis_mat, basis_mat_inv)
function defines_order(K::AnticNumberField, x::FakeFmpqMat)
  if rows(x) != degree(K) || cols(x) != degree(K)
    return false, x, Vector{nf_elem}()
  end
  local xinv
  try
    xinv = inv(x)
  catch
    return false, x, Vector{nf_elem}()
  end
  n = degree(K)
  B_K = basis(K)
  d = Vector{nf_elem}(n)
  # Construct the basis elements from the basis matrix
  for i in 1:n
    d[i] = elem_from_mat_row(K, x.num, i, x.den)
  end

  # Check if Z-module spanned by x is closed under multiplcation
  l = Vector{nf_elem}(n)
  for i in 1:degree(K)
    for j in 1:degree(K)
      l[j] = d[i]*d[j]
    end
    Ml = basis_mat(l)
    if !isone((Ml * xinv).den)
      return false, x, Vector{nf_elem}()
    end
  end
  # Check if 1 is contained in the Z-module
  Ml = basis_mat([one(K)])
  if !isone((Ml * xinv).den)
    return false, x, Vector{nf_elem}()
  end
  return true, xinv, d
end

function defines_order(K::AnticNumberField, A::Vector{nf_elem})
  if length(A) != degree(K)
    return false, FakeFmpqMat(), FakeFmpqMat(), A
  else
    B = basis_mat(A)
    b, Binv, _ = defines_order(K, B)
    return b, B, Binv, A
  end
end
