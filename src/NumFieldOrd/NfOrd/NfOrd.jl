################################################################################
#
#    NfOrd/NfOrd.jl : Orders in absolute number fields
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
#  Copyright (C) 2015, 2016, 2017 Tommy Hofmann
#
################################################################################

export ==, +, basis, basis_matrix, basis_mat_inv, contains_equation_order,
       discriminant, degree, gen_index, EquationOrder, index,
       is_equation_order, is_index_divisor, lll, lll_basis, nf,
       minkowski_matrix, norm_change_const, Order, parent, different,
       signature, trace_matrix, codifferent, reduced_discriminant

################################################################################
#
#  Make NfOrd fully working Nemo ring
#
################################################################################

Nemo.parent_type(::Type{NfAbsOrdElem{S, T}}) where {S, T} = NfAbsOrd{S, T}

Nemo.elem_type(::NfAbsOrd{S, T}) where {S, T} = NfAbsOrdElem{S, T}

Nemo.elem_type(::Type{NfAbsOrd{S, T}}) where {S, T} = NfAbsOrdElem{S, T}

ideal_type(::NfAbsOrd{S, T}) where {S, T} = NfAbsOrdIdl{S, T}

ideal_type(::Type{NfAbsOrd{S, T}}) where {S, T} = NfAbsOrdIdl{S, T}

fractional_ideal_type(::NfAbsOrd{S, T}) where {S, T} = NfOrdFracIdl

fractional_ideal_type(::Type{NfAbsOrd{S, T}}) where {S, T} = NfOrdFracIdl

Nemo.base_ring(::NfAbsOrd) = FlintZZ

@doc Markdown.doc"""
    parent(O::NfAbsOrd) -> NfOrdSet

Returns the parent of $\mathcal O$, that is, the set of orders of the ambient
number field.
"""
parent(O::NfOrd) = NfAbsOrdSet(nf(O), false)

function contains_equation_order(O::NfAbsOrd)
  if isdefined(O, :index)
    return true
  end
  if isdefined(O, :basis_mat_inv)
    return isone(O.basis_mat_inv.den)
  end
  return isinteger(gen_index(O))
end

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_basis(O::NfAbsOrd)
  if isdefined(O, :basis_ord)
    return nothing
  end
  b = O.basis_nf
  d = degree(O)
  B = Vector{elem_type(O)}(undef, d)
  for i in 1:length(b)
    v = fmpz[fmpz(0) for j in 1:d]
    one!(v[i])
    B[i] = NfAbsOrdElem(O, b[i], v)
  end
  O.basis_ord = B
  return nothing
end

function Base.getindex(O::NfAbsOrd, i::Int)
  if iszero(i)
    return zero(O)
  end
  assure_has_basis(O)
  @assert i <= degree(O) && i > 0 "Index must be a positive integer smaller than the dimension"
  return O.basis_ord[i]
end

function assure_has_basis_matrix(O::NfAbsOrd)
  if isdefined(O, :basis_matrix)
    return nothing
  end
  A = O.basis_nf#::Vector{elem_type(nf(O))}
  O.basis_matrix = FakeFmpqMat(basis_matrix(A))
  return nothing
end

function assure_has_basis_mat_inv(O::NfAbsOrd)
  if isdefined(O, :basis_mat_inv)
    return nothing
  end
  M = basis_matrix(O, copy = false)
  if isdefined(O, :index) && is_lower_triangular(M.num)
    #The order contains the equation order and the matrix is lower triangular
    #The inverse is lower triangular and it has denominator 1
    #to exploit this, I call can_solve
    I = solve_lt(M.num, scalar_matrix(FlintZZ, nrows(M), M.den))
    O.basis_mat_inv = FakeFmpqMat(I)
    return nothing
  end
  O.basis_mat_inv = inv(basis_matrix(O, copy = false))
  return nothing
end

################################################################################
#
#  Basis
#
################################################################################

@inline function basis_ord(O::NfAbsOrd; copy::Bool = true)
  assure_has_basis(O)
  if copy
    res = O.basis_ord::Vector{elem_type(O)}
    return deepcopy(res)::Vector{elem_type(O)}
  else
    return O.basis_ord::Vector{elem_type(O)}
  end
end

@doc Markdown.doc"""
    basis(O::NfAbsOrd) -> Vector{NfAbsOrdElem}

Returns the $\mathbf Z$-basis of $\mathcal O$.
"""
@inline basis(O::NfAbsOrd; copy::Bool = true) = basis_ord(O, copy = copy)

@doc Markdown.doc"""
    basis(O::NfOrd, K::AnticNumberField) -> Vector{nf_elem}

Returns the $\mathbf Z$-basis elements of $\mathcal O$ as elements of the
ambient number field.
"""
function basis(O::NfOrd, K::AnticNumberField; copy::Bool = true)
  nf(O) != K && error()
  if copy
    return deepcopy(O.basis_nf)
  else
    return O.basis_nf
  end
end

function basis(O::NfAbsOrd{NfAbsNS, NfAbsNSElem}, K::NfAbsNS; copy::Bool = true)
  nf(O) != K && error()
  if copy
    return deepcopy(O.basis_nf)
  else
    return O.basis_nf
  end
end

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

@doc Markdown.doc"""
    basis_matrix(O::NfAbsOrd) -> FakeFmpqMat

Returns the basis matrix of $\mathcal O$ with respect to the basis
of the ambient number field.
"""
function basis_matrix(O::NfAbsOrd; copy::Bool = true)
  assure_has_basis_matrix(O)
  if copy
    return deepcopy(O.basis_matrix)
  else
    return O.basis_matrix
  end
end

@doc Markdown.doc"""
    basis_mat_inv(O::NfAbsOrd) -> FakeFmpqMat

Returns the inverse of the basis matrix of $\mathcal O$.
"""
function basis_mat_inv(O::NfAbsOrd; copy::Bool = true) where T
  assure_has_basis_mat_inv(O)
  if copy
    return deepcopy(O.basis_mat_inv)
  else
    return O.basis_mat_inv
  end
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

function extra_name(O::NfAbsOrd)
  set_name!(O)
  s = get_attribute(O, :name)
  s !== nothing && return
  set_name!(nf(O))
  s = get_attribute(nf(O), :name)
  if s !== nothing
    set_name!(O, "O_$s")
  end
  return get_attribute(O, :name)
end

function show(io::IO, O::NfAbsOrd)
  @show_name(io, O)
  @show_special(io, O)
  if is_maximal_known_and_maximal(O)
    show_maximal(io, O)
  else
    show_gen(io, O)
  end
end

function show_gen(io::IO, O::NfAbsOrd)
  print(io, "Order of ")
  println(io, nf(O))
  print(io, "with Z-basis ")
  print(io, basis(O, copy = false))
end

function show_maximal(io::IO, O::NfAbsOrd)
  print(io, "Maximal order of $(nf(O)) \nwith basis $(O.basis_nf)")
end

################################################################################
#
#  Discriminant
#
################################################################################

function assure_has_discriminant(O::NfAbsOrd)
  if isdefined(O, :disc)
    return nothing
  else
    if is_equation_order(O) && is_simple(nf(O)) && is_defining_polynomial_nice(nf(O))
      O.disc = numerator(discriminant(nf(O).pol))
    else
      O.disc = det(trace_matrix(O, copy = false))
    end
  end
  return nothing
end

@doc Markdown.doc"""
    discriminant(O::NfOrd) -> fmpz

Returns the discriminant of $\mathcal O$.
"""
function discriminant(O::NfAbsOrd)
  assure_has_discriminant(O)
  return O.disc
end

#TODO: compute differently in equation orders, this is the rres...
@doc Markdown.doc"""
    reduced_discriminant(O::NfOrd) -> fmpz

Returns the reduced discriminant, that is, the largest elementary divisor of
the trace matrix of $\mathcal O$.
"""
function reduced_discriminant(O::NfOrd)
  if is_equation_order(O)
    Zx = PolynomialRing(FlintZZ, cached = false)[1]
    f = Zx(nf(O).pol)
    return rres(f, derivative(f))
  end
  return maximal_elementary_divisor(trace_matrix(O, copy = false))
end

################################################################################
#
#  (Generalized) index
#
################################################################################

@doc Markdown.doc"""
    gen_index(O::NfOrd) -> fmpq

Returns the generalized index of $\mathcal O$ with respect to the equation
order of the ambient number field.
"""
function gen_index(O::NfAbsOrd)
  if isdefined(O, :gen_index)
    return deepcopy(O.gen_index)
  else
    #TODO: Remove once the determinant checks if a matrix is upper/lower triangular.
    if is_lower_triangular(basis_matrix(O, copy = false).num)
      return basis_matrix(O, copy = false).den^degree(O)//prod_diagonal(basis_matrix(O, copy = false).num)
    end
    O.gen_index = inv(det(basis_matrix(O, copy = false)))
    return deepcopy(O.gen_index)
  end
end

@doc Markdown.doc"""
    index(O::NfOrd) -> fmpz

Assuming that the order $\mathcal O$ contains the equation order
$\mathbf Z[\alpha]$ of the ambient number field, this function returns the
index $[ \mathcal O : \mathbf Z]$.
"""
function index(O::NfAbsOrd; copy::Bool = true)
  if !isdefined(O, :index)
    i = gen_index(O)
    !isone(denominator(i)) && error("Order does not contain the equation order")
    O.index = abs(numerator(i))
    end
  if copy
    return deepcopy(O.index)
    else
    return O.index
  end
end

################################################################################
#
#  Index divisor
#
################################################################################

@doc Markdown.doc"""
    is_index_divisor(O::NfOrd, d::fmpz) -> Bool
    is_index_divisor(O::NfOrd, d::Int) -> Bool

Returns whether $d$ is a divisor of the index of $\mathcal O$. It is assumed
that $\mathcal O$ contains the equation order of the ambient number field.
"""
function is_index_divisor(O::NfAbsOrd, d::IntegerUnion)
  i = index(O, copy = false)
  return iszero(i % d)
end

################################################################################
#
#  Ramified Primes
#
################################################################################

@doc Markdown.doc"""
    ramified_primes(O::NfAbsOrd) -> Vector{fmpz}

Returns the list of prime numbers that divide $\operatorname{disc}(\mathcal O)$.
"""
function ramified_primes(O::NfAbsOrd)
  return collect(keys(factor(discriminant(O)).fac))
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(O::NfAbsOrd{S, T}, dict::IdDict) where {S, T}
  z = NfAbsOrd{S, T}(O.nf)
  for x in fieldnames(typeof(O))
    if x != :nf && isdefined(O, x)
      setfield!(z, x, Base.deepcopy_internal(getfield(O, x), dict))
    end
  end
  if isdefined(z, :basis_ord)
    # Until now we have parent(basis(x)) !== z
    for b in z.basis_ord
      b.parent = z
    end
  end
  return z
end

################################################################################
#
#  Minkowski matrix
#
################################################################################

@doc Markdown.doc"""
    minkowski_matrix(O::NfAbsOrd, abs_tol::Int = 64) -> arb_mat

Returns the Minkowski matrix of $\mathcal O$.  Thus if $\mathcal O$ has degree
$d$, then the result is a matrix in $\operatorname{Mat}_{d\times d}(\mathbf
R)$. The entries of the matrix are real balls of type `arb` with radius less
then `2^-abs_tol`.
"""
function minkowski_matrix(O::NfAbsOrd, abs_tol::Int = 64)
  if isdefined(O, :minkowski_matrix) && O.minkowski_matrix[2] >= abs_tol
    A = deepcopy(O.minkowski_matrix[1])
  else
    M = minkowski_matrix(O.basis_nf, abs_tol)
    O.minkowski_matrix = (M, abs_tol)
    A = deepcopy(M)
  end
  return A
end

function minkowski_matrix(B::Vector{S}, abs_tol::Int = 64) where S <: NumFieldElem
  K = parent(B[1])
  T = Vector{Vector{arb}}(undef, length(B))
  for i in 1:length(B)
    T[i] = minkowski_map(B[i], abs_tol)
  end
  p = maximum(Int[ precision(parent(T[i][j])) for i in 1:length(B), j in 1:absolute_degree(K) ])
  M = zero_matrix(ArbField(p, cached = false), length(B), absolute_degree(K))
  for i in 1:length(B)
    for j in 1:absolute_degree(K)
      M[i, j] = T[i][j]
    end
  end
  return M
end

@doc Markdown.doc"""
    minkowski_gram_mat_scaled(O::NfAbsOrd, prec::Int = 64) -> fmpz_mat

Let $c$ be the Minkowski matrix as computed by `minkowski_matrix` with precision $p$.
This function computes $d = round(c 2^p)$ and returns $round(d d^t/2^p)$.
"""
function minkowski_gram_mat_scaled(O::NfAbsOrd, prec::Int = 64)
  if isdefined(O, :minkowski_gram_mat_scaled) && O.minkowski_gram_mat_scaled[2] >= prec
    A = deepcopy(O.minkowski_gram_mat_scaled[1])
    shift!(A, prec - O.minkowski_gram_mat_scaled[2])
  else
    c = minkowski_matrix(O, prec+2)
    d = zero_matrix(FlintZZ, degree(O), degree(O))
    A = zero_matrix(FlintZZ, degree(O), degree(O))
    round_scale!(d, c, prec)
    ccall((:fmpz_mat_gram, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}), A, d)
    shift!(A, -prec)
    O.minkowski_gram_mat_scaled = (A, prec)
    A = deepcopy(A)
  end
  # to ensure pos. definitenes, we add n to the diag.
  for i=1:degree(O)
    fmpz_mat_entry_add_ui!(A, i, i, UInt(nrows(A)))
  end
  return A
end

function minkowski_gram_mat_scaled(B::Vector{T}, prec::Int = 64) where T <: NumFieldElem
  K = parent(B[1])
  c = minkowski_matrix(B, prec+2)
  d = zero_matrix(FlintZZ, length(B), absolute_degree(K))
  A = zero_matrix(FlintZZ, length(B), length(B))
  round_scale!(d, c, prec)
  ccall((:fmpz_mat_gram, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}), A, d)
  shift!(A, -prec)
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
function _check_elem_in_order(a::T, O::NfAbsOrd{S, T},
                              short::Type{Val{U}} = Val{false}) where {S, T, U}
  assure_has_basis_mat_inv(O)
  t = O.tcontain
  elem_to_mat_row!(t.num, 1, t.den, a)
  t = mul!(t, t, O.basis_mat_inv)
  if short == Val{true}
    return isone(t.den)
  elseif short == Val{false}
    if !isone(t.den)
      return false, Vector{fmpz}()
    else
      v = Vector{fmpz}(undef, degree(O))
      for i in 1:degree(O)
        v[i] = t.num[1, i]
      end
      return true, v
    end
  end
end


function in(a::NfAbsNSElem, O::NfAbsOrd)
  @assert parent(a) == nf(O)
  return _check_elem_in_order(a, O, Val{true})
end

@doc Markdown.doc"""
    in(a::NumFieldElem, O::NumFieldOrd) -> Bool

Checks whether $a$ lies in $\mathcal O$.
"""
function in(a::nf_elem, O::NfOrd)
  @assert parent(a) == nf(O)
  if is_defining_polynomial_nice(nf(O)) && contains_equation_order(O)
    d = denominator!(O.tcontain_fmpz, a)
    if isone(d)
      return true
    end
    exp_index = basis_matrix(O, copy = false).den
    if !divisible(exp_index, d)
      return false
    end
    M = basis_mat_inv(O, copy = false)
    d2 = ppio(M.den, d)[1]
    t = O.tcontain
    elem_to_mat_row!(t.num, 1, t.den, a)
    d = mul!(d, d, d2)
    if fits(Int, d)
      R = ResidueRing(FlintZZ, Int(d), cached = false)
      return _check_containment(R, M.num, t.num)
    else
      R1 = ResidueRing(FlintZZ, d, cached = false)
      return _check_containment(R1, M.num, t.num)
    end
  end
  return _check_elem_in_order(a, O, Val{true})
end

function _check_containment(R, M, t)
  M1 = map_entries(R, M)
  t1 = map_entries(R, t)
  mul!(t1, t1, M1)
  return iszero(t1)
end

################################################################################
#
#  Denominator in an order
#
################################################################################

@doc Markdown.doc"""
    denominator(a::nf_elem, O::NfOrd) -> fmpz

Returns the smallest positive integer $k$ such that $k \cdot a$ is contained in
$\mathcal O$.
"""
function denominator(a::NfAbsNSElem, O::NfAbsOrd)
  M = O.tcontain
  elem_to_mat_row!(M.num, 1, M.den, a)
  M = mul!(M, M, basis_mat_inv(O, copy = false))
  return deepcopy(M.den)
end


function denominator(a::nf_elem, O::NfOrd)
  if is_defining_polynomial_nice(nf(O)) && contains_equation_order(O)
    d = denominator(a)
    if isone(d)
      return d
    end
    d1, d2 = ppio(d, index(O))
    if isone(d1)
      return d2
    end
    a1 = d2*a
    a1 = mod(a1, d1)
    M = basis_mat_inv(O, copy = false)
    d3 = ppio(M.den, d1)[1]
    M1 = mod(M.num, d1*d3)
    t = O.tcontain
    elem_to_mat_row!(t.num, 1, t.den, a1)
    mul!(t.num, t.num, M1)
    c = gcd(content(t.num), d1*d3)
    c1 = divexact(d1*d3, c)
    return d2*c1
  end
  M = O.tcontain
  elem_to_mat_row!(M.num, 1, M.den, a)
  M = mul!(M, M, basis_mat_inv(O, copy = false))
  return deepcopy(M.den)
end


function integral_split(a::nf_elem, O::NfOrd)
  assure_has_basis_mat_inv(O)
  M = O.tcontain
  elem_to_mat_row!(M.num, 1, M.den, a)
  M = mul!(M, M, O.basis_mat_inv)
  return M.den, M.num
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
#
# TODO: Make this rigorous using interval arithmetic. The only problem is that
#       the characteristic polynomial might not be squarefree.
@doc Markdown.doc"""
    norm_change_const(O::NfOrd) -> (Float64, Float64)

Returns $(c_1, c_2) \in \mathbf R_{>0}^2$ such that for all
$x = \sum_{i=1}^d x_i \omega_i \in \mathcal O$ we have
$T_2(x) \leq c_1 \cdot \sum_i^d x_i^2$
and
$\sum_i^d x_i^2 \leq c_2 \cdot T_2(x)$,
where $(\omega_i)_i$ is the $\mathbf Z$-basis of $\mathcal O$.
"""
function norm_change_const(O::NfOrd; cached::Bool = true)
  if cached && isdefined(O, :norm_change_const)
    return O.norm_change_const::Tuple{BigFloat, BigFloat}
  end

  z = _norm_change_const(O.basis_nf)
  O.norm_change_const = z
  return z::Tuple{BigFloat, BigFloat}
end

function _norm_change_const(v::Vector{nf_elem})
  d = degree(parent(v[1]))
  M = minkowski_matrix(v, 64)
  # I don't think we have to swap rows,
  # since permutation matrices are orthogonal
  #r1, r2 = signature(O)
  #for i in 2:2:r2
  #  swap_rows!(M, r1 + i, r1 + 2*r2 - i + 1)
  #end

  M = M*transpose(M)

  N = Symmetric([ Float64(M[i, j]) for i in 1:nrows(M), j in 1:ncols(M) ])
  #forcing N to really be Symmetric helps julia - aparently
  if any(!isfinite, N)
    fl1 = true
  else
    r = sort(LinearAlgebra.eigvals(N))
    fl1 = false
    for ind = 1:length(r)
      if isnan(r[ind])
        fl1 = true
        break
      end
    end
  end
  if fl1 || !(r[1] > 0)
    # more complicated methods are called for...
    m = ceil(Int, log(d)/log(2))
    m += m%2
    @assert iseven(m)
    l_max = root(tr(M^m), m) #an upper bound within a factor of 2
                             #according to a paper by Victor Pan
                             #https://doi.org/10.1016/0898-1221(90)90236-D
                             #formula (1) and discussion
    pr = 128
    l_min = l_max
    if isodd(d) d+=1; end
    while true
      try
        M = inv(M)
        l_min = root(tr(M^d), d) #as above...
        if isfinite(l_min)
          z = (BigFloat(l_max), BigFloat(l_min))
          return z::Tuple{BigFloat, BigFloat}
        end
      catch e
        # should verify the correct error
        if !(e isa ErrorException)
          rethrow(e)
        end
      finally
        M = minkowski_matrix(v, pr)
        M = M*transpose(M)
        pr *= 2
      end
    end
  end

  @assert r[1]>0

  z = (BigFloat(r[end]), BigFloat(inv(r[1])))
  return z::Tuple{BigFloat, BigFloat}
end

################################################################################
#
#  Construction of orders
#
################################################################################
#the one WITHOUT K is there for rel-ext, so this is for parity

function Order(a::Vector{T}; check::Bool = true, isbasis::Bool = false,
               cached::Bool = false) where {T <: NumFieldElem{fmpq}}
  return Order(parent(a[1]), a, check = check, isbasis = isbasis, cached = cached)
end
                 
@doc Markdown.doc"""
    Order(B::Vector{nf_elem}; check::Bool = true, cached::Bool = true, isbasis::Bool = false) -> NfOrd
    Order(K::AnticNumberField, B::Vector{nf_elem}; check::Bool = true, cached::Bool = true, isbasis::Bool = false) -> NfOrd

Returns the order generated by $B$. If `check` is set, it is checked
whether $B$ defines an order. If `isbasis` is set, then elements are assumed to form
a $\mathbf{Z}$-basis.
"""
function Order(::S, a::Vector{T}; check::Bool = true, isbasis::Bool = false,
               cached::Bool = false) where {S <: NumField{fmpq}, T <: NumFieldElem{fmpq}}
  K = parent(a[1])
  @assert all(x->K == parent(x), a)
  if isbasis
    if check
      b, bmat, bmat_inv, _ = defines_order(K, a)
      if !b
        error("The elements do not define an order")
      else
        return NfAbsOrd(K, bmat, bmat_inv, deepcopy(a), cached)
      end
    else
      return NfAbsOrd(deepcopy(a), cached)
    end
  else
    return _order(K, a, cached = cached, check = check)
  end
end

function Order(K, a::Vector; check::Bool = true, isbasis::Bool = false,
               cached::Bool = true)
  local b
  try
    b = map(K, a)
  catch
    error("Cannot coerce elements from array into the number field")
  end
  return Order(K, b, check = check, cached = cached, isbasis = isbasis)
end

@doc Markdown.doc"""
    Order(K::AnticNumberField, A::FakeFmpqMat; check::Bool = true) -> NfOrd

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function Order(K::S, a::FakeFmpqMat; check::Bool = true,
               cached::Bool = false) where {S <: NumField{fmpq}}
  if check
    b, ainv, d = defines_order(K, a)
    if !b
      error("The basis matrix does not define an order")
    else
      return NfAbsOrd(K, deepcopy(a), ainv, d, cached)
    end
  else
    return NfAbsOrd(K, deepcopy(a), cached)
  end
end

@doc Markdown.doc"""
    Order(K::AnticNumberField, A::fmpq_mat; check::Bool = true) -> NfOrd

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function Order(K::S, a::fmpq_mat; check::Bool = true,
               cached::Bool = true) where {S <: Union{AnticNumberField, NfAbsNS}}
  return Order(K, FakeFmpqMat(a), cached = cached, check = check)
end

@doc Markdown.doc"""
    Order(K::AnticNumberField, A::fmpz_mat, check::Bool = true) -> NfOrd

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function Order(K::S, a::fmpz_mat, check::Bool = true,
               cached::Bool = true) where {S}
  return Order(K, FakeFmpqMat(a), check = check, cached = cached)
end

################################################################################
#
#  Any order
#
################################################################################

#Based on an idea of Lenstra. More details in
#https://www.sciencedirect.com/science/article/pii/S0019357701800392
#https://www.impan.pl/pl/wydawnictwa/czasopisma-i-serie-wydawnicze/acta-arithmetica/all/120/3/82018/decomposition-of-primes-in-non-maximal-orders
#: Denis Simon: The index of nonmonic polynomials
#    Indag Math, 2001
#: Denis Simon, Ilaria Del Corso, Roberto Dvornicich:
#    Decomposition of primes in non-maximal orders,
#    Acta Arithmetica 120 (2005), 231-244
#
@doc Markdown.doc"""
    any_order(K::NumberField)

Return some order in $K$. In case the defining polynomial for $K$
is monic and integral, this just returns the equation order.
In the other case $\mathbb Z[\alpha]\cap \mathbb Z[1/\alpha]$
is returned.
"""
function any_order(K::AnticNumberField)
  f = K.pol
  de = denominator(f)
  g = f * de

  if is_monic(g)
    return equation_order(K)
  else
    d = degree(g)
    M = zero_matrix(FlintZZ, d, d)
    M[1, 1] = 1
    for i in 2:d
      for j in i:-1:2
        M[i, j] = numerator(coeff(g, d - (i - j)))
      end
    end
    @hassert :NfOrd 1 defines_order(K, FakeFmpqMat(M))[1]
    z = NfAbsOrd{AnticNumberField, nf_elem}(K, FakeFmpqMat(M))
    z.is_equation_order = false
    return z
  end
end

function any_order(K::NfAbsNS)
  normalized_gens = Vector{NfAbsNSElem}(undef, degree(K))
  g = gens(K)
  for i in 1:ngens(K)
    f = denominator(K.pol[i]) * K.pol[i]
    if isone(coeff(f, 1))
      normalized_gens[i] = g[i]
    else
      normalized_gens[i] = coeff(f, 1) * g[i]
    end
  end

  b = Vector{NfAbsNSElem}(undef, degree(K))
  ind = 1
  it = cartesian_product_iterator([1:degrees(K)[i] for i in 1:ngens(K)], inplace = true)
  for i in it
    b[ind] = prod(normalized_gens[j]^(i[j] - 1) for j=1:length(i))
    ind += 1
  end
  return Order(K, b, check = false, cached = false)
end

################################################################################
#
#  Equation order
#
################################################################################

equation_order(K, cached::Bool = false) = EquationOrder(K, cached)

@doc Markdown.doc"""
    EquationOrder(K::NumberField) -> NumFieldOrd
    equation_order(K::NumberField) -> NumFieldOrd

Returns the equation order of the number field $K$.
"""
function EquationOrder(K::NumField{fmpq}, cached::Bool = true)
  if cached
    return get_attribute!(K, :equation_order) do
      return __equation_order(K)
    end::order_type(K)
  else
    return __equation_order(K)
  end
end

# If the numerator of the defining polynomial is not monic, then we construct
# the order as described in exercise 15, chapter 15 of Cohen's first book.
# This is due to H. Lenstra.
function __equation_order(K::AnticNumberField)
  f = K.pol
  if isone(denominator(f) * leading_coefficient(f))
    M = FakeFmpqMat(identity_matrix(FlintZZ, degree(K)))
    Minv = FakeFmpqMat(identity_matrix(FlintZZ, degree(K)))
    z = NfAbsOrd{AnticNumberField, nf_elem}(K, M, Minv, basis(K), false)
    z.is_equation_order = true
    return z
  else
    error("Primitive element must be integral")
  end
end

function __equation_order(K::NfAbsNS)
  for f in K.pol
    if !isone(denominator(f) * coeff(f, 1))
      error("Generators must be integral")
    end
  end

  M = FakeFmpqMat(identity_matrix(FlintZZ, degree(K)))
  Minv = FakeFmpqMat(identity_matrix(FlintZZ, degree(K)))
  z = NfAbsOrd{NfAbsNS, NfAbsNSElem}(K, M, Minv, basis(K), false)
  z.is_equation_order = true
  return z
end

@doc Markdown.doc"""
    EquationOrder(f::fmpz_poly; cached::Bool = true, check::Bool = true) -> NfOrd
    equation_order(f::fmpz_poly; cached::Bool = true, check::Bool = true) -> NfOrd

Returns the equation order defined by the monic polynomial $f$.
"""
function EquationOrder(f::fmpz_poly; cached::Bool = true, check::Bool = true)
  is_monic(f) || error("polynomial must be monic")
  K = number_field(f, cached = cached, check = check)[1]
  return EquationOrder(K)
end
equation_order(f::fmpz_poly; cached::Bool = true, check::Bool = true) = EquationOrder(f, cached = cached, check = check)

@doc Markdown.doc"""
    EquationOrder(f::fmpq_poly; cached::Bool = true, check::Bool = true) -> NfOrd
    equation_order(f::fmpq_poly; cached::Bool = true, check::Bool = true) -> NfOrd

Returns the equation order defined by the monic integral polynomial $f$.
"""
function EquationOrder(f::fmpq_poly; cached::Bool = true, check::Bool = true)
  is_monic(f) || error("polynomial must be integral and monic")
  isone(denominator(f)) || error("polynomial must be integral and monic")

  K = number_field(f, cached = cached, check = check)[1]
  return EquationOrder(K)
end
equation_order(f::fmpq_poly; cached::Bool = true, check::Bool = true) = EquationOrder(f, cached = cached, check = check)

@doc Markdown.doc"""
    equation_order(M::NfOrd) -> NfOrd

The equation order of the number field.
"""
equation_order(M::NfAbsOrd) = equation_order(nf(M))


function _order(K::S, elt::Vector{T}; cached::Bool = true, check::Bool = true) where {S <: NumField{fmpq}, T}
  n = degree(K)

  bas = elem_type(K)[one(K)]
  phase = 1
  local B::FakeFmpqMat = FakeFmpqMat()

  for e = elt
    if phase == 2
      if denominator(B) % denominator(e) == 0
        C = basis_matrix([e], FakeFmpqMat)
        fl, _ = can_solve_with_solution(B.num, div(B.den, denominator(e))*C.num, side = :left)
#        fl && println("elt known:", e)
        fl && continue
      end
    end
    if check
      f = minpoly(e)
      isone(denominator(f)) || error("data does not define an order, $e is non-integral")
      df = degree(f)-1
    else
      df = n-1
    end
    f = one(K)
    for i=1:df
      mul!(f, f, e)
      if phase == 2
        if denominator(B) % denominator(f) == 0
          C = basis_matrix(elem_type(K)[f], FakeFmpqMat)
          fl = is_zero_mod_hnf!(div(B.den, denominator(f))*C.num, B.num)
#          fl && println("inner abort: ", e, " ^ ", i)
          fl && break
        end
      end
      b = elem_type(K)[e*x for x in bas]
      append!(bas, b)
      if length(bas) >= n
        B = basis_matrix(bas, FakeFmpqMat)
        hnf!(B)
        rk = nrows(B) - n + 1
        while is_zero_row(B, rk)
          rk += 1
        end
        B = sub(B, rk:nrows(B), 1:n)
        phase = 2
        bas = elem_type(K)[ elem_from_mat_row(K, B.num, i, B.den) for i = 1:nrows(B) ]
        if check
          @assert isone(bas[1])
        end
      end
    end
  end

  if length(bas) >= n
    B = basis_matrix(bas, FakeFmpqMat)
    hnf!(B)
    rk = nrows(B) - n + 1
    if is_zero_row(B.num, rk)
      error("data does not define an order: dimension to small")
    end
    B = sub(B, rk:nrows(B), 1:n)
    bas = elem_type(K)[ elem_from_mat_row(K, B.num, i, B.den) for i = 1:nrows(B) ]
  end

  if !isdefined(B, :num)
    error("data does not define an order: dimension to small")
  end

  # Make an explicit check
  @hassert :NfOrd 1 defines_order(K, B)[1]
  return Order(K, B, cached = cached, check = check)
end

################################################################################
#
#  Equality
#
################################################################################

# This is the function which is used in dictionaries
function Base.isequal(R::NfOrd, S::NfOrd)
  return R === S
end

# Todo: Improve this
function ==(R::NfAbsOrd, S::NfAbsOrd)
  nf(R) != nf(S) && return false
  if discriminant(R) != discriminant(S)
    return false
  end
  assure_has_basis_matrix(R)
  assure_has_basis_matrix(S)
  return hnf(R.basis_matrix) == hnf(S.basis_matrix)
end

@doc Markdown.doc"""
    is_contained(R::NfAbsOrd, S::NfAbsOrd) -> Bool

Checks if $R$ is contained in $S$.
"""
function is_contained(R::NfAbsOrd, S::NfAbsOrd)
  return (basis_matrix(R, copy = false)*basis_mat_inv(S, copy = false)).den == 1
end

function ==(R::NfAbsOrdSet, S::NfAbsOrdSet)
  return R.nf === S.nf
end

################################################################################
#
#  Trace matrix
#
################################################################################

@doc Markdown.doc"""
    trace_matrix(O::NfAbsOrd) -> fmpz_mat

Returns the trace matrix of $\mathcal O$, that is, the matrix
$(\operatorname{tr}_{K/\mathbf Q}(b_i \cdot b_j))_{1 \leq i, j \leq d}$.
"""
function trace_matrix(O::NfAbsOrd; copy::Bool = true)
  if isdefined(O, :trace_mat)
    if copy
      return deepcopy(O.trace_mat)
    else
      return O.trace_mat
    end
  end
  K = nf(O)
  b = O.basis_nf
  n = degree(K)
  g = zero_matrix(FlintZZ, n, n)
  aux = K()
  for i = 1:n
    mul!(aux, b[i], b[i])
    t = tr(aux)
    @assert isinteger(t)
    g[i, i] = numerator(t)
    for j in (i + 1):n
      mul!(aux, b[i], b[j])
      t = tr(aux)
      @assert isinteger(t)
      g[i, j] = numerator(t)
      g[j, i] = numerator(t)
    end
  end
  O.trace_mat = g
  if copy
    return deepcopy(g)
  else
    return g
  end
end

################################################################################
#
#  Addition of orders
#
################################################################################

@doc Markdown.doc"""
    +(R::NfOrd, S::NfOrd) -> NfOrd

Given two orders $R$, $S$ of $K$, this function returns the smallest order
containing both $R$ and $S$. It is assumed that $R$, $S$ contain the ambient
equation order and have coprime index.
"""
function +(a::NfAbsOrd, b::NfAbsOrd; cached::Bool = false)
  nf(a) != nf(b) && error("Orders must have same ambient number field")
  if is_defining_polynomial_nice(nf(a)) &&
     contains_equation_order(a) && contains_equation_order(b) &&
          isone(gcd(index(a), index(b)))
    return sum_as_Z_modules_fast(a, b)
  else
    return _order(nf(a), vcat(a.basis_nf, b.basis_nf), cached = cached, check = false)
  end
end

################################################################################
#
#  Sum as Z modules of orders
#
################################################################################

function sum_as_Z_modules(O1, O2, z::fmpz_mat = zero_matrix(FlintZZ, 2 * degree(O1), degree(O1)))
  if contains_equation_order(O1) && contains_equation_order(O2)
    return sum_as_Z_modules_fast(O1, O2, z)
  else
    return O1 + O2
  end
end

function sum_as_Z_modules_fast(O1, O2, z::fmpz_mat = zero_matrix(FlintZZ, 2 * degree(O1), degree(O1)))
  @hassert :NfOrd 1 contains_equation_order(O1)
  @hassert :NfOrd 1 contains_equation_order(O2)
  K = _algebra(O1)
  R1 = basis_matrix(O1, copy = false)
  S1 = basis_matrix(O2, copy = false)
  d = degree(K)
  g = gcd(R1.den, S1.den)
  r1 = divexact(R1.den, g)
  s1 = divexact(S1.den, g)
  z1 = view(z, 1:d, 1:d)
  mul!(z1, R1.num, s1)
  z2 = view(z, (d + 1):2*d, 1:d)
  mul!(z2, S1.num, r1)
  hnf_modular_eldiv!(z, lcm(R1.den, S1.den), :lowerleft)
  M = FakeFmpqMat(view(z, (nrows(z)-ncols(z)+1):nrows(z), 1:ncols(z)), lcm(R1.den, S1.den))
  @hassert :NfOrd 1 defines_order(K, M)[1]
  OK = Order(K, M, check = false)::typeof(O1)
  if OK isa NfOrd
    OK.primesofmaximality = union(O1.primesofmaximality, O2.primesofmaximality)
  end
  OK.index = divexact(denominator(M)^d, prod(fmpz[M.num[i, i] for i in 1:d]))
  @hassert :NfOrd 1 numerator(gen_index(OK)) == OK.index
  OK.disc = divexact(discriminant(O1) * index(O1)^2, OK.index^2)
  @hassert :NfOrd 1 det(trace_matrix(OK)) == OK.disc
  return OK
end

################################################################################
#
#  Check if something defines an order
#
################################################################################

# This is not optimizied for performance.
# If false, then this returns (false, garbage, garbage).
# If true, then this return (true, basis_matrix, basis_mat_inv).
# This should also work if K is an algebra over QQ.
function defines_order(K::S, x::FakeFmpqMat) where {S}
  if nrows(x) != dim(K) || ncols(x) != dim(K)
    return false, x, Vector{elem_type(K)}()
  end
  local xinv
  try
    xinv = inv(x)
  catch
    return false, x, Vector{elem_type(K)}()
  end
  n = dim(K)
  B_K = basis(K)
  d = Vector{elem_type(K)}(undef, n)
  # Construct the basis elements from the basis matrix
  for i in 1:n
    d[i] = elem_from_mat_row(K, x.num, i, x.den)
  end

  # Check if Z-module spanned by x is closed under multiplcation
  l = Vector{elem_type(K)}(undef, n)
  for i in 1:n
    for j in 1:n
      if j < i && is_commutative(K)
        continue
      end
      l[j] = d[i]*d[j]
    end
    Ml = basis_matrix(l, FakeFmpqMat)
    dd = Ml.den*xinv.den
    R = ResidueRing(FlintZZ, dd, cached = false)
    #if !isone((Ml * xinv).den)
    if !iszero(map_entries(R, Ml.num)*map_entries(R, xinv.num))
      return false, x, Vector{elem_type(K)}()
    end
  end
  # Check if 1 is contained in the Z-module
  Ml = basis_matrix([one(K)], FakeFmpqMat)
  if !isone((Ml * xinv).den)
    return false, x, Vector{elem_type(K)}()
  end
  return true, xinv, d
end

function defines_order(K::S, A::Vector{T}) where {S, T}
  if length(A) != dim(K)
    return false, FakeFmpqMat(), FakeFmpqMat(), A
  else
    B = basis_matrix(A, FakeFmpqMat)
    b, Binv, _ = defines_order(K, B)
    return b, B, Binv, A
  end
end

################################################################################
#
#  Different
#
################################################################################

@doc Markdown.doc"""
    different(x::NfAbsOrdElem) -> NfOrdElem

The different of $x$, i.e. $0$ if $x$ is not a primitive element, or
$f'(x)$ for $f$ the minimal polynomial of $x$ otherwise.
"""
function different(x::NfAbsOrdElem)
  if iszero(x)
    return x
  end
  f = minpoly(x)
  if degree(f) < degree(parent(x))
    return parent(x)(0)
  end
  return derivative(f)(x)
end

@doc Markdown.doc"""
    different(R::NfAbsOrd) -> NfAbsOrdIdl

The differnt ideal of $R$, that is, the ideal generated by all differents
of elements in $R$.
For Gorenstein orders, this is also the inverse ideal of the co-different.
"""
function different(R::NfAbsOrd; proof::Bool = true)
#  D = ideal(R, different(R(gen(nf(R)))))
  d = abs(discriminant(R))
  D = d*R
  nt = 0
  nD = norm(D)
  while norm(D) != d
    #@show D, norm(D), d
    x = rand(R, -10:10)
    y = different(x)
    if !iszero(y)
      D += ideal(R, y)
    end
    if norm(D) == nD
      nt += 1
      if nt > 20
        if proof
          if !is_gorenstein(R)
            error("function only works for Gorenstein")
          end
        end
        return D
      end
    end
    nD = norm(D)
  end
  return D
end

@doc Markdown.doc"""
    discriminant(m::Map, R::NfOrd) -> NfOrdIdl

The discriminant ideal of $R$ over the maximal order of the domain of the map $m$,
that is, the ideal generated by all norms of differents
of elements in $R$.
"""
function discriminant(m::T, R::NfOrd) where T <: Map
  D = different(R)
  #TODO: maybe mix norm and different to only generate the discriminant ideal, not the
  #      full different first.
  return norm(m, D)
end

@doc Markdown.doc"""
    codifferent(R::NfAbsOrd) -> NfOrdIdl

The codiffernt ideal of $R$, i.e. the trace-dual of $R$.
"""
function codifferent(R::NfAbsOrd)
  t = trace_matrix(R)
  ti, d = pseudo_inv(t)
  return ideal(R, ti, true)//d
end

trace_dual(R::NfAbsOrd) = codifferent(R)

################################################################################
#
#  Conductor
#
################################################################################

# TODO: This can be improved by building the matrix N more clever and using
#       a modular HNF algorithm.
@doc Markdown.doc"""
    conductor(R::NfOrd, S::NfOrd) -> NfAbsOrdIdl

The conductor $\{x \in R | xS\subseteq R\}$
for orders $R\subseteq S$.
"""
function conductor(R::NfOrd, S::NfOrd)
  n = degree(R)
  t = basis_matrix(R, copy = false) * basis_mat_inv(S, copy = false)
  if !isone(t.den)
    error("The first order is not contained in the second!")
  end
  basis_mat_R_in_S_inv_num, d = pseudo_inv(t.num)
  M = zero_matrix(FlintZZ, n^2, n)
  B = basis(S, copy = false)
  for k in 1:n
    a = B[k]
    N = representation_matrix(S(a.elem_in_nf, false)) * basis_mat_R_in_S_inv_num
    for i in 1:n
      for j in 1:n
        M[(k - 1)*n + i, j] = N[j, i]
      end
    end
  end
  hnf!(M)
  H = sub(M, 1:n, 1:n)
  Hinv, new_den = pseudo_inv(transpose(H))
  Hinv = Hinv * basis_mat_R_in_S_inv_num
  return ideal(R, divexact(Hinv, new_den))
end

@doc Markdown.doc"""
    conductor(R::NfOrd) -> NfAbsOrdIdl

The conductor of $R$ in the maximal order.
"""
conductor(R::NfOrd) = conductor(R, maximal_order(R))
