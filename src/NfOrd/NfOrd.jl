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

export ==, +, basis, basis_mat, basis_mat_inv, contains_eqaution_order,
       discriminant, degree, den, gen_index, EquationOrder, index,
       isequation_order, isindex_divisor, lll, lll_basis, maximal_order,
       MaximalOrder, minkowski_mat, nf, norm_change_const, Order, parent,
       poverorder, pmaximal_overorder, ring_of_integers, signature,
       trace_matrix, different, codifferent, reduced_discriminant

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

Nemo.show_minus_one(::Type{NfAbsOrdElem{S, T}}) where {S, T} = true

Nemo.base_ring(::NfAbsOrd) = Union{}

Nemo.needs_parentheses(::NfAbsOrdElem) = true

Nemo.isnegative(::NfAbsOrdElem) = false

################################################################################
#
#  Basic field access
#
################################################################################

@doc Markdown.doc"""
    nf(O::NfAbsOrd) -> AnticNumberField

Returns the ambient number field of $\mathcal O$.
"""
@inline nf(O::NfAbsOrd) = O.nf

@doc Markdown.doc"""
  number_field(O::NfAbsOrd)

Return the ambient number field of $\mathcal O$.
"""
@inline function NumberField(O::NfAbsOrd)
  return O.nf
end

@doc Markdown.doc"""
    parent(O::NfAbsOrd) -> NfOrdSet

Returns the parent of $\mathcal O$, that is, the set of orders of the ambient
number field.
"""
parent(O::NfOrd) = NfAbsOrdSet(nf(O), false)

@doc Markdown.doc"""
    isequation_order(O::NfAbsOrd) -> Bool

Returns whether $\mathcal O$ is the equation order of the ambient number
field $K$.
"""
@inline isequation_order(O::NfAbsOrd) = O.isequation_order

@inline ismaximal_known(O::NfAbsOrd) = O.ismaximal != 0

@doc Markdown.doc"""
    ismaximal(R::NfAbsOrd) -> Bool
> Tests if the order $R$ is maximal. This might trigger the 
> the computation if the maximal order.
"""
function ismaximal(R::NfAbsOrd)
  if R.ismaximal == 1
    return true
  end
  if R.ismaximal == 2
    return false
  end
  S = maximal_order(R)
  if discriminant(S) == discriminant(R)
    R.ismaximal = 1
  else
    R.ismaximal = 2
  end
  return R.ismaximal == 1
end
 
contains_equation_order(O::NfAbsOrd) = isinteger(gen_index(O))

################################################################################
#
#  Degree
#
################################################################################

@doc Markdown.doc"""
    degree(O::NfOrd) -> Int

Returns the degree of $\mathcal O$.
"""
degree(O::NfAbsOrd) = degree(O.nf)

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
    v = [fmpz(0) for j in 1:d]
    one!(v[i])
    B[i] = NfAbsOrdElem(O, b[i], v)
  end
  O.basis_ord = B
  return nothing
end

function assure_has_basis_mat(O::NfAbsOrd)
  if isdefined(O, :basis_mat)
    return nothing
  end
  A = O.basis_nf
  O.basis_mat = FakeFmpqMat(basis_mat(A))
  return nothing
end

function assure_has_basis_mat_inv(O::NfAbsOrd)
  if isdefined(O, :basis_mat_inv)
    return nothing
  end
  O.basis_mat_inv = inv(basis_mat(O, Val{false}))
  return nothing
end

################################################################################
#
#  Basis
#
################################################################################

function basis_ord(O::NfAbsOrd, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis(O)
  if copy == Val{true}
    return deepcopy(O.basis_ord)::Vector{elem_type(O)}
  else
    return O.basis_ord::Vector{elem_type(O)}
  end
end

@doc Markdown.doc"""
    basis(O::NfOrd) -> Array{NfOrdElem, 1}

Returns the $\mathbf Z$-basis of $\mathcal O$.
"""
@inline basis(O::NfAbsOrd, copy::Type{Val{T}} = Val{true}) where {T} = basis_ord(O, copy)

@doc Markdown.doc"""
    basis(O::NfOrd, K::AnticNumberField) -> Array{nf_elem, 1}

Returns the $\mathbf Z$-basis elements of $\mathcal O$ as elements of the
ambient number field.
"""
function basis(O::NfAbsOrd, K::AnticNumberField)
  nf(O) != K && error()
  return deepcopy(O.basis_nf)
end

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

@doc Markdown.doc"""
    basis_mat(O::NfOrd) -> FakeFmpqMat

Returns the basis matrix of $\mathcal O$ with respect to the power basis
of the ambient number field.
"""
function basis_mat(O::NfAbsOrd, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat(O)
  if copy == Val{true}
    return deepcopy(O.basis_mat)
  else
    return O.basis_mat
  end
end

@doc Markdown.doc"""
    basis_mat_inv(O::NfOrd) -> FakeFmpqMat

Returns the inverse of the basis matrix of $\mathcal O$.
"""
function basis_mat_inv(O::NfAbsOrd, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat_inv(O)
  if copy == Val{true}
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

function show(io::IO, O::NfAbsOrd)
  if ismaximal_known(O) && ismaximal(O)
    show_maximal(io, O)
  else
    show_gen(io, O)
  end
end

function show_gen(io::IO, O::NfAbsOrd)
  print(io, "Order of ")
  println(io, nf(O))
  print(io, "with Z-basis ")
  print(io, basis(O))
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
    if isequation_order(O) && issimple(nf(O))
      O.disc = numerator(discriminant(nf(O).pol))
    else
      O.disc = discriminant(basis(O))
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
> Returns the reduced discriminant, ie. the largest elementary divisor of the 
> trace matrix of $\mathcal O$.
"""
function reduced_discriminant(O::NfOrd)
  if isequation_order(O)
    Zx = PolynomialRing(FlintZZ, cached = false)[1]
    f = Zx(nf(O).pol)
    return rres(f, derivative(f))
  end
  return maximal_elementary_divisor(trace_matrix(O))
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
    O.gen_index = inv(det(basis_mat(O, Val{false})))#FlintQQ(O.basis_mat.den^degree(O), det(O.basis_mat.num))
    return deepcopy(O.gen_index)
  end
end

@doc Markdown.doc"""
    index(O::NfOrd) -> fmpz

Assuming that the order $\mathcal O$ contains the equation order
$\mathbf Z[\alpha]$ of the ambient number field, this function returns the
index $[ \mathcal O : \mathbf Z]$.
"""
function index(O::NfAbsOrd)
  if isdefined(O, :index)
    return deepcopy(O.index)
  else
    i = gen_index(O)
    !isone(denominator(i)) && error("Order does not contain the equation order")
    O.index = numerator(i)
    return deepcopy(O.index)
  end
end

################################################################################
#
#  Index divisor
#
################################################################################

@doc Markdown.doc"""
    isindex_divisor(O::NfOrd, d::fmpz) -> Bool
    isindex_divisor(O::NfOrd, d::Int) -> Bool

Returns whether $d$ is a divisor of the index of $\mathcal O$. It is assumed
that $\mathcal O$ contains the equation order of the ambient number field.
"""
function isindex_divisor(O::NfOrd, d::Union{fmpz, Integer})
  i = index(O)
  return i % d == 0
end

################################################################################
#
#  Ramified Primes
#
################################################################################

@doc Markdown.doc"""
    ramified_primes(O::NfOrd) -> Array{fmpz, 1}

Returns the list of prime numbers that divide $\operatorname{disc}(\mathcal O)$.
"""
function ramified_primes(O::NfOrd)
  return collect(keys(factor(discriminant(O)).fac))
end

################################################################################
#
#  Deepcopy
#
################################################################################

@doc Markdown.doc"""
    deepcopy(O::NfOrd) -> NfOrd

Makes a copy of $\mathcal O$.
"""
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
#  Signature
#
################################################################################

@doc Markdown.doc"""
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

@doc Markdown.doc"""
    minkowski_mat(O::NfOrd, abs_tol::Int = 64) -> arb_mat

Returns the Minkowski matrix of $\mathcal O$.  Thus if $\mathcal O$ has degree
$d$, then the result is a matrix in $\operatorname{Mat}_{d\times d}(\mathbf
R)$. The entries of the matrix are real balls of type `arb` with radius less
then `2^-abs_tol`.
"""
function minkowski_mat(O::NfOrd, abs_tol::Int = 64)
  if isdefined(O, :minkowski_mat) && O.minkowski_mat[2] > abs_tol
    A = deepcopy(O.minkowski_mat[1])
  else
    T = Vector{Vector{arb}}(undef, degree(O))
    B = O.basis_nf
    for i in 1:degree(O)
      T[i] = minkowski_map(B[i], abs_tol)
    end
    p = maximum([ prec(parent(T[i][j])) for i in 1:degree(O), j in 1:degree(O) ])
    M = ArbMatSpace(ArbField(p, false), degree(O), degree(O), false)()
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

@doc Markdown.doc"""
    minkowski_gram_mat_scaled(O::NfOrd, prec::Int = 64) -> fmpz_mat

> Let $c$ be the Minkowski matrix as computed by {{{minkowski_mat}}} with precision $p$.
> This function computes $d = round(c 2^p)$ and returns $round(d d^t/2^p)$.
"""
function minkowski_gram_mat_scaled(O::NfOrd, prec::Int = 64)
  if isdefined(O, :minkowski_gram_mat_scaled) && O.minkowski_gram_mat_scaled[2] >= prec
    A = deepcopy(O.minkowski_gram_mat_scaled[1])
    shift!(A, prec - O.minkowski_gram_mat_scaled[2])
  else
    c = minkowski_mat(O, prec)
    d = zero_matrix(FlintZZ, degree(O), degree(O))
    A = zero_matrix(FlintZZ, degree(O), degree(O))
    round_scale!(d, c, prec)
    ccall((:fmpz_mat_gram, :libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}), A, d)
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
        v[i] = deepcopy(t.num[1, i])
      end
      return true, v
    end
  end
end

@doc Markdown.doc"""
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

@doc Markdown.doc"""
    denominator(a::nf_elem, O::NfOrd) -> fmpz

Returns the smallest positive integer $k$ such that $k \cdot a$ is contained in
$\mathcal O$.
"""
function denominator(a::Union{nf_elem, NfAbsNSElem}, O::NfAbsOrd)
  assure_has_basis_mat_inv(O)
  M = O.tcontain
  elem_to_mat_row!(M.num, 1, M.den, a)
  M = mul!(M, M, O.basis_mat_inv)
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
function norm_change_const(O::NfOrd)
  if O.norm_change_const[1] > 0
    return O.norm_change_const::Tuple{Float64, Float64}
  else
    d = degree(O)
    M = minkowski_mat(O, 64)
    # I don't think we have to swap rows,
    # since permutation matrices are orthogonal
    #r1, r2 = signature(O)
    #for i in 2:2:r2
    #  swap_rows!(M, r1 + i, r1 + 2*r2 - i + 1)
    #end

    M = M*M'

    N = Symmetric([ Float64(M[i, j]) for i in 1:nrows(M), j in 1:ncols(M) ])
    #forcing N to really be Symmetric helps julia - aparently
    r = sort(eigvals(N))
    if !(r[1] > 0)
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
            z = (Float64(l_max), Float64(l_min))
            O.norm_change_const = z
            return z::Tuple{Float64, Float64}
          end
          M = minkowski_mat(O, pr)
          M = M*M'
          pr *= 2
        catch e  # should verify the correct error
          M = minkowski_mat(O, pr)
          M = M*M'
          pr *= 2
        end
      end
    end

    @assert r[1]>0
#    N = transpose(M)*M
#    N = MatrixSpace(AcbField(prec(base_ring(N))), nrows(N), ncols(N))(N)
#    chi = charpoly(PolynomialRing(base_ring(N), "x")[1], N)
#    return chi
#    r = roots(chi)
#    # I want upper bound for the largest and lower bound for the smallest root
#
#    tm = arf_struct(0, 0, 0, 0)
#    ccall((:arf_init, :libarb), Nothing, (Ref{arf_struct}, ), tm)
#    ccall((:arb_get_abs_ubound_arf, :libarb), Nothing, (Ref{arf_struct}, Ref{arb}), tm, real(r[end]))
#    # 3 is round to infinity
#    c1 = ccall((:arf_get_d, :libarb), Cdouble, (Ref{arf_struct}, Cint), tm, 3)
#
#    ccall((:arb_get_abs_ubound_arf, :libarb), Nothing, (Ref{arf_struct}, Ref{arb}), tm, &(inv(real(r[1]))))
#    c2 = ccall((:arf_get_d, :libarb), Cdouble, (Ref{arf_struct}, Cint), tm, 3)
#
#    ccall((:arf_clear, :libarb), Nothing, (Ref{arf_struct}, ), tm)
#
#    z = (c1, c2)
    z = (r[end], inv(r[1]))
    O.norm_change_const = z
    return z::Tuple{Float64, Float64}
  end
end

################################################################################
#
#  Construction of orders
#
################################################################################

@doc Markdown.doc"""
    Order(B::Array{nf_elem, 1}, check::Bool = true) -> NfOrd

Returns the order with $\mathbf Z$-basis $B$. If `check` is set, it is checked
whether $B$ defines an order.
"""
function Order(::S, a::Array{T, 1}, check::Bool = true,
               cache::Bool = true) where {S <: Union{AnticNumberField, NfAbsNS}, T <: Union{nf_elem, NfAbsNSElem}}
  K = parent(a[1])
  if check
    b, bmat, bmat_inv, _ = defines_order(K, a)
    if !b
      error("The elements do not define an order")
    else
      return NfAbsOrd(K, bmat, bmat_inv, deepcopy(a), cache)
    end
  else
    return NfAbsOrd(deepcopy(a), cache)
  end
end

function Order(K, a::Vector, check::Bool = true,
               cache::Bool = true)
  local b
  try
    b = map(K, a)
  catch
    error("Cannot coerce elements from array into the number field")
  end
  return Order(K, b, check, cache)
end

@doc Markdown.doc"""
    Order(K::AnticNumberField, A::FakeFmpqMat, check::Bool = true) -> NfOrd

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function Order(K::S, a::FakeFmpqMat, check::Bool = true,
               cache::Bool = false) where {S <: Union{AnticNumberField, NfAbsNS}}
  if check
    b, ainv, d = defines_order(K, a)
    if !b
      error("The basis matrix does not define an order")
    else
      return NfAbsOrd(K, deepcopy(a), ainv, d, cache)
    end
  else
    return NfAbsOrd(K, deepcopy(a), cache)
  end
end

@doc Markdown.doc"""
    Order(K::AnticNumberField, A::fmpq_mat, check::Bool = true) -> NfOrd

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function Order(K::S, a::fmpq_mat, check::Bool = true,
               cache::Bool = true) where {S <: Union{AnticNumberField, NfAbsNS}}
  return Order(K, FakeFmpqMat(a), cache)
end

@doc Markdown.doc"""
    Order(K::AnticNumberField, A::fmpz_mat, check::Bool = true) -> NfOrd

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function Order(K::S, a::fmpz_mat, check::Bool = true,
               cache::Bool = true) where {S}
  return Order(K, FakeFmpqMat(a), check, cache)
end

@doc Markdown.doc"""
    Order(A::NfOrdFracIdl) -> NfOrd

Returns the fractional ideal $A$ as an order of the ambient number field.
"""
function Order(a::NfOrdFracIdl, check::Bool = true, cache::Bool = true)
  return Order(nf(order(a)), basis_mat(a)*basis_mat(order(a)), check, cache)
end

################################################################################
#
#  Any order
#
################################################################################

#based on an ideal of Lenstra, more details in
#https://www.sciencedirect.com/science/article/pii/S0019357701800392
#https://www.impan.pl/pl/wydawnictwa/czasopisma-i-serie-wydawnicze/acta-arithmetica/all/120/3/82018/decomposition-of-primes-in-non-maximal-orders
#: Denis Simon: The index of nonmonic polynomials
#    Indag Math, 2001
#: Denis Simon, Ilaria Del Corso, Roberto Dvornicich:
#    Decomposition of primes in non-maximal orders,
#    Acta Arithmetica 120 (2005), 231-244 
#
function any_order(K::AnticNumberField)
  f = K.pol
  de = denominator(f)
  g = f * de

  if ismonic(g)
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
    @hassert :NfOrd 1 defines_order(K, FakeFmpqMat(M))
    z = NfAbsOrd{AnticNumberField, nf_elem}(K, FakeFmpqMat(M))
    z.isequation_order = false
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

  b = NfAbsNSElem[]
  for i in CartesianIndices(Tuple(1:degrees(K)[i] for i in 1:ngens(K)))
    push!(b, prod(normalized_gens[j]^(i[j] - 1) for j=1:length(i)))
  end
  return Order(K, b, false, false)
end

################################################################################
#
#  Equation order
#
################################################################################

equation_order(K, cached::Bool = false) = EquationOrder(K, cached)

@doc Markdown.doc"""
    EquationOrder(K::NfAbs) -> NfAbsOrd

Returns the equation order of the absolute number field $K$.
"""
function EquationOrder(K::T, cached::Bool = true) where {T}
  if cached
    try
      M = _get_nf_equation_order(K)
      return M
    catch e
      if e isa AccessorNotSetError
        M = __equation_order(K)
        _set_nf_equation_order(K, M)
        return M
      else
        rethrow(e)
      end
    end
  else
    M = __equation_order(K)
    return M
  end
end

# If the numerator of the defining polynomial is not monic, then we construct
# the order as described in exercise 15, chapter 15 of Cohen's first book.
# This is due to H. Lenstra.
function __equation_order(K::AnticNumberField)
  f = K.pol
  if isone(denominator(f) * lead(f))
    M = FakeFmpqMat(identity_matrix(FlintZZ, degree(K)))
    Minv = FakeFmpqMat(identity_matrix(FlintZZ, degree(K)))
    z = NfAbsOrd{AnticNumberField, nf_elem}(K, M, Minv, basis(K), false)
    z.isequation_order = true
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
  z.isequation_order = true
  return z
end

@doc Markdown.doc"""
    EquationOrder(f::fmpz_poly; cached::Bool = true, check::Bool = true) -> NfOrd

> Returns the equation order defined by the monic polynomial $f$.
"""
function EquationOrder(f::fmpz_poly; cached::Bool = true, check::Bool = true)
  ismonic(f) || error("polynomial must be monic")
  K = number_field(f, cached = cached, check = check)[1]
  return EquationOrder(K)
end

@doc Markdown.doc"""
    EquationOrder(f::fmpq_poly; cached::Bool = true, check::Bool = true) -> NfOrd

> Returns the equation order defined by the monic integral polynomial $f$.
"""
function EquationOrder(f::fmpq_poly; cached::Bool = true, check::Bool = true)
  ismonic(f) || error("polynomial must be integral and monic")
  isone(denominator(f)) || error("polynomial must be integral and monic")

  K = number_field(f, cached = cached, check = check)[1]
  return EquationOrder(K)
end

@doc Markdown.doc"""
    equation_order(M::NfOrd) -> NfOrd
> The equation order of then number field.
"""
equation_order(M::NfAbsOrd) = equation_order(nf(M))

function _order(K::S, elt::Array{T, 1}) where {S, T}
  o = one(K)
  
  n = degree(K)
  if !(o in elt)
    push!(elt, o)
  end
  B = basis_mat(elt)
  B = hnf(B)
  
  elt = T[]
  if nrows(B) >= n
    for i in (nrows(B) - degree(K) + 1):nrows(B) 
      push!(elt, elem_from_mat_row(K, B.num, i, B.den))
    end
  else
    for i in 1:nrows(B) 
      push!(elt, elem_from_mat_row(K, B.num, i, B.den))
    end
    for i=1:n-1
      l=length(elt)
      for s = 1:l
        for t = i:l
          push!(elt, elt[s] * elt[t])
        end
      end
      B = hnf(basis_mat(elt))
      empty!(elt)
      if nrows(B) >= n
        for i in (nrows(B) - degree(K) + 1):nrows(B) 
          push!(elt, elem_from_mat_row(K, B.num, i, B.den))
        end
      else
        for i in 1:nrows(B) 
          push!(elt, elem_from_mat_row(K, B.num, i, B.den))
        end
      end
    end
  end
  
  closed = false

  dold = fmpq(0)

  # Since 1 is in elt, prods will contain all elements
  while !closed
    prods = T[elt[i] for i = 1:length(elt)]
    for i = 2:length(elt)
      for j = i:length(elt)
        push!(prods, elt[i]*elt[j])
      end
    end
    
    B = hnf(basis_mat(prods))
    
    dd = B.num[nrows(B) - degree(K) + 1, 1]
    for i in 2:degree(K)
      dd *= B.num[nrows(B) - degree(K) + i, i]
    end
    if iszero(dd)
      error("Elements do not define a module of full rank")
    end
    d = dd//(B.den)^n

    if dold == d
      closed = true
    else
      dold = d
      elt = Array{T, 1}(undef, n)
      for i in 1:n
        elt[i] = elem_from_mat_row(K, B.num, nrows(B) - degree(K) + i, B.den)
      end
    end
  end

  # Make an explicit check
  @hassert :NfOrd 1 defines_order(K, elt)[1]
  return Order(K, elt, false, false)
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

function ==(R::NfAbsOrd, S::NfAbsOrd)
  nf(R) != nf(S) && return false
  assure_has_basis_mat(R)
  assure_has_basis_mat(S)
  return R.basis_mat == S.basis_mat
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
    trace_matrix(O::NfOrd) -> fmpz_mat

Returns the trace matrix of `\mathcal O`, that is, the matrix
$(\operatorname{tr}_{K/\mathbf Q}(b_i \cdot b_j))_{1 \leq i, j \leq d}$.
"""
function trace_matrix(O::NfAbsOrd)
  if isdefined(O, :trace_mat)
    return deepcopy(O.trace_mat)
  end
  K = nf(O)
  b = O.basis_nf
  n = degree(K)
  g = zero_matrix(FlintZZ, n, n)
  for i=1:n
    t = tr(b[i]^2)
    @assert isinteger(t)
    g[i, i] = numerator(t)
    for j in (i + 1):n
      t = tr(b[i]*b[j])
      @assert isinteger(t)
      g[i, j] = numerator(t)
      g[j, i] = numerator(t)
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

@doc Markdown.doc"""
    +(R::NfOrd, S::NfOrd) -> NfOrd

Given two orders $R$, $S$ of $K$, this function returns the smallest order
containing both $R$ and $S$. It is assumed that $R$, $S$ contain the ambient
equation order and have coprime index.
"""
function +(a::NfAbsOrd, b::NfAbsOrd)
  nf(a) != nf(b) && error("Orders must have same ambient number field")
  if contains_equation_order(a) && contains_equation_order(b) &&
          isone(gcd(index(a), index(b)))
    aB = basis_mat(a, Val{false})
    bB = basis_mat(b, Val{false})
    d = degree(a)
    m = zero_matrix(FlintZZ, 2*d, d)
    for i=1:d
      for j=1:d
        m[i,j]=bB.den*aB.num[i,j]
        m[i+d,j]= aB.den*bB.num[i,j]
      end
    end
    mat = _hnf_modular_eldiv(m, bB.den*aB.den, :lowerleft)
    c = view(mat, d + 1:2*d, 1:d)
    O = Order(nf(a), FakeFmpqMat(c, aB.den*bB.den), false)
    O.primesofmaximality = union(a.primesofmaximality, b.primesofmaximality)
    O.disc = gcd(discriminant(a), discriminant(b))
    if a.disc<0 || b.disc<0
      O.disc=-O.disc
    end
    return O
  else
    return _order(nf(a), vcat(a.basis_nf, b.basis_nf))
  end
end

################################################################################
#
#  p-overorder
#
################################################################################

function _poverorder(O::NfAbsOrd, p::fmpz)
  @vtime :NfOrd 3 I = pradical(O, p)
  if isdefined(I, :princ_gen) && I.princ_gen == p
    return O
  end
  @vtime :NfOrd 3 R = ring_of_multipliers(I)
  return R
end

function _poverorder(O::NfAbsOrd, p::Integer)
  return _poverorder(O, fmpz(p))
end

@doc Markdown.doc"""
    poverorder(O::NfOrd, p::fmpz) -> NfOrd
    poverorder(O::NfOrd, p::Integer) -> NfOrd

This function tries to find an order that is locally larger than $\mathcal O$
at the prime $p$: If $p$ divides the index $[ \mathcal O_K : \mathcal O]$,
this function will return an order $R$ such that
$v_p([ \mathcal O_K : R]) < v_p([ \mathcal O_K : \mathcal O])$. Otherwise
$\mathcal O$ is returned.
"""
function poverorder(O::NfAbsOrd, p::fmpz)
  if isequation_order(O) && issimple(nf(O))
    #return dedekind_poverorder(O, p)
    return polygons_overorder(O, p)
  else
    return _poverorder(O, p)
  end
end

function poverorder(O::NfAbsOrd, p::Integer)
  return poverorder(O, fmpz(p))
end

################################################################################
#
#  p-maximal overorder
#
################################################################################

@doc Markdown.doc"""
    pmaximal_overorder(O::NfOrd, p::fmpz) -> NfOrd
    pmaximal_overorder(O::NfOrd, p::Integer) -> NfOrd

This function finds a $p$-maximal order $R$ containing $\mathcal O$. That is,
the index $[ \mathcal O_K : R]$ is not dividible by $p$.
"""
function pmaximal_overorder(O::NfAbsOrd, p::fmpz)
  @vprint :NfOrd 1 "computing p-maximal overorder for $p ... \n"
  if p in O.primesofmaximality
    return O
  end
  if rem(discriminant(O), p^2) != 0 
    push!(O.primesofmaximality, p)
    return O
  end

  d = discriminant(O)
  @vprint :NfOrd 1 "extending the order at $p for the first time ... \n"
  OO = poverorder(O, p)
  dd = discriminant(OO)
  if rem(discriminant(O), p^2) != 0
    push!(OO.primesofmaximality, p)
    return OO
  end
  i = 1
  while d != dd
    i += 1
    @vprint :NfOrd 1 "extending the order at $p for the $(i)th time ... \n"
    d = dd
    OO = poverorder(OO, p)
    dd = discriminant(OO)
    if rem(dd, p^2) != 0
      break
    end
  end
  push!(OO.primesofmaximality, p)
  return OO
end

function pmaximal_overorder(O::NfAbsOrd, p::Integer)
  return pmaximal_overorder(O, fmpz(p))
end

###############################################################################
#
#  Maximal Order interface
#
###############################################################################

function MaximalOrder(O::NfOrd, primes::Array{fmpz, 1})
  if length(primes) == 0
    return O
  end

  OO = O

  if !isdefining_polynomial_nice(nf(O)) || !isinteger(gen_index(O))
    for i in 1:length(primes)
      p = primes[i]
      @vprint :NfOrd 1 "Computing p-maximal overorder for $p ..."
      OO += pmaximal_overorder(OO, p)
      if !(p in OO.primesofmaximality)
        push!(OO.primesofmaximality, p)
      end
    end
    return OO
  end

  ind = index(O)
  EO = EquationOrder(nf(O))
  for i in 1:length(primes)
    p = primes[i]
    @vprint :NfOrd 1 "Computing p-maximal overorder for $p ..."
    if divisible(ind, p)
      OO = pmaximal_overorder(OO, p)
    else
      O1 = pmaximal_overorder(EO, p)
      if divisible(index(O1), p)
        OO += O1
      end
    end
    if !(p in OO.primesofmaximality)
      push!(OO.primesofmaximality, p)
    end
    @vprint :NfOrd 1 "done\n"
  end
  return OO
end

@doc Markdown.doc"""
***
    maximal_order(O::NfOrd) -> NfOrd
    MaximalOrder(O::NfOrd) -> NfOrd

Returns the maximal overorder of $O$.
"""
function MaximalOrder(O::NfAbsOrd)
  K = nf(O)
  try
    # First check if the number field knows its maximal order
    M = _get_maximal_order(K)::typeof(O)
    return M
  catch e
    if !isa(e, AccessorNotSetError) 
      rethrow(e)
    end
    M = new_maximal_order(O)::typeof(O)
    M.ismaximal = 1
    _set_maximal_order(K, M)
    return M
  end
end

function maximal_order_round_four(O::NfAbsOrd)
  OO = deepcopy(O)
  @vtime :NfOrd fac = factor(abs(discriminant(O)))
  for (p,j) in fac
    if j == 1
      continue
    end
    @vprint :NfOrd 1 "Computing p-maximal overorder for $p ..."
    O1 = pmaximal_overorder(O, p)
    if valuation(discriminant(O1), p)< valuation(discriminant(OO),p)
      OO += O1
    end 
    @vprint :NfOrd 1 "done\n"
  end
  OO.ismaximal = 1
  return OO
end

@doc Markdown.doc"""
***
    MaximalOrder(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd
    maximal_order(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd
    ring_of_integers(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd

Assuming that ``primes`` contains all the prime numbers at which the equation
order $\mathbf{Z}[\alpha]$ of $K = \mathbf{Q}(\alpha)$ is not maximal,
this function returns the maximal order of $K$.
"""
function MaximalOrder(K::AnticNumberField, primes::Array{fmpz, 1})
  O = any_order(K)
  @vprint :NfOrd 1 "Computing the maximal order ...\n"
  O = MaximalOrder(O, primes)
  @vprint :NfOrd 1 "... done\n"
  return NfOrd(K, basis_mat(O, Val{false}))
end

@doc Markdown.doc"""
    maximal_order(K::AnticNumberField) -> NfOrd
    ring_of_integers(K::AnticNumberField) -> NfOrd

> Returns the maximal order of $K$.

# Example

```julia-repl
julia> Qx, xx = FlintQQ["x"];
julia> K, a = NumberField(x^3 + 2, "a");
julia> O = MaximalOrder(K);
```
"""
function MaximalOrder(K::T) where {T}
  try
    c = _get_maximal_order(K)::NfAbsOrd{T, elem_type(T)}
    return c
  catch e
    if !isa(e, AccessorNotSetError)
      rethrow(e)
    end
    #O = MaximalOrder(K)::NfOrd
    O = new_maximal_order(any_order(K))::NfAbsOrd{T, elem_type(T)}
    O.ismaximal = 1
    _set_maximal_order(K, O)
    return O
  end
end

@doc Markdown.doc"""
***
    ring_of_integers(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd
    ring_of_integers(K::AnticNumberField, primes::Array{Integer, 1}) -> NfOrd

Assuming that ``primes`` contains all the prime numbers at which the equation
order $\mathbf{Z}[\alpha]$ of $K = \mathbf{Q}(\alpha)$ is not maximal,
this function returns the maximal order of $K$.
"""
ring_of_integers(x::AnticNumberField, primes::Array{fmpz, 1}) = maximal_order(x, primes)
ring_of_integers(x::AnticNumberField, primes::Array{Integer, 1}) = maximal_order(x, primes)

###############################################################################
#
#  Some LLL-related functions
#
###############################################################################

# don't know what this is doing
#for totally real field, the T_2-Gram matrix is the trace matrix, hence exact.

function _lll_gram(M::NfOrd)
  K = nf(M)
  @assert istotally_real(K)
  g = trace_matrix(M)

  q,w = lll_gram_with_transform(g)
  On = NfOrd(K, FakeFmpqMat(w*basis_mat(M, Val{false}).num, denominator(basis_mat(M, Val{false}))))
  On.ismaximal = M.ismaximal
  return On
end

@doc Markdown.doc"""
    lll_basis(M::NfOrd) -> Array{nf_elem, 1}
> A basis for $m$ that is reduced using the LLL algorithm for the Minkowski metric.    
"""
function lll_basis(M::NfOrd)
  I = ideal(M, parent(basis_mat(M, Val{false}).num)(1))
  return lll_basis(I)
end

@doc Markdown.doc"""
    lll(M::NfOrd) -> NfOrd
> The same order, but with the basis now being LLL reduced wrt. the Minkowski metric.
"""
function lll(M::NfOrd)
  K = nf(M)

  if istotally_real(K)
    return _lll_gram(M)
  end

  I = ideal(M, 1)

  prec = 100
  while true
    try
      q,w = lll(I, parent(basis_mat(M, Val{false}).num)(0), prec = prec)
      On = NfOrd(K, FakeFmpqMat(w*basis_mat(M, Val{false}).num, denominator(basis_mat(M, Val{false}))))
      On.ismaximal = M.ismaximal
      return On
    catch e
      if isa(e, LowPrecisionLLL) || isa(e, InexactError)
        prec = Int(round(prec*1.2))
        #if prec>1000
        #  error("precision too large in LLL");
        #end
        continue;
      else
        rethrow(e)
      end
    end
  end
end

################################################################################
#
#  Check if something defines an order
#
################################################################################

# This is not optimizied for performance.
# If false, then this returns (false, garbage, garbage).
# If true, then this return (true, basis_mat, basis_mat_inv).
function defines_order(K::S, x::FakeFmpqMat) where {S}
  if nrows(x) != degree(K) || ncols(x) != degree(K)
    return false, x, Vector{elem_type(K)}()
  end
  local xinv
  try
    xinv = inv(x)
  catch
    return false, x, Vector{elem_type(K)}()
  end
  n = degree(K)
  B_K = basis(K)
  d = Vector{elem_type(K)}(undef, n)
  # Construct the basis elements from the basis matrix
  for i in 1:n
    d[i] = elem_from_mat_row(K, x.num, i, x.den)
  end

  # Check if Z-module spanned by x is closed under multiplcation
  l = Vector{elem_type(K)}(undef, n)
  for i in 1:n
    for j in i:n
      l[j] = d[i]*d[j]
    end
    Ml = basis_mat(l)
    if !isone((Ml * xinv).den)
      return false, x, Vector{elem_type(K)}()
    end
  end
  # Check if 1 is contained in the Z-module
  Ml = basis_mat([one(K)])
  if !isone((Ml * xinv).den)
    return false, x, Vector{elem_type(K)}()
  end
  return true, xinv, d
end

function defines_order(K::S, A::Vector{T}) where {S, T}
  if length(A) != degree(K)
    return false, FakeFmpqMat(), FakeFmpqMat(), A
  else
    B = basis_mat(A)
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
    different(x::NfOrdElem) -> NfOrdElem

> The different of $x$, ie. $0$ if x is not a primitive element, or
> $f'(x)$ for $f$ the minimal polynomial of $x$ otherwise.
"""
function different(x::NfOrdElem)
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
    different(R::NfOrd) -> NfOrdIdl

> The differnt ideal of $R$, that is, the ideal generated by all differents
> of elements in $R$.
> For the maximal order, this is also the inverse ideal of the co-different.
"""
function different(R::NfOrd)
#  D = ideal(R, different(R(gen(nf(R)))))
  d = abs(discriminant(R))
  D = d*R
  while norm(D) != d
    #@show D, norm(D), d
    x = rand(R, -10:10)
    y = different(x)
    if !iszero(y)
      D += ideal(R, y)
    end
  end
  return D
end

@doc Markdown.doc"""
    discriminant(m::Map, R::NfOrd) -> NfOrdIdl

> The discriminant ideal of $R$ over the maximal order of the domain of the map $m$, 
> that is, the ideal generated by all norms of differents
> of elements in $R$.
"""
function discriminant(m::T, R::NfOrd) where T <: Map
  D = different(R)
  #TODO: maybe mix norm and different to only generate the discriminant ideal, not the
  #      full different first.
  return norm(m, D)
end

@doc Markdown.doc"""
    codifferent(R::NfOrd) -> NfOrdIdeal
> The codiffernt ideal of $R$, ie. the trace-dual of $R$.
"""
function codifferent(R::NfOrd)
  t = trace_matrix(R)
  ti, d = pseudo_inv(t)
  return ideal(R, ti, true)//d
end

###############################################################################
#
#  Code to get a new maximal order starting from any order
#
###############################################################################

# This is the non-cached version generic fallback version

function new_maximal_order(O::NfAbsOrd)
  return maximal_order_round_four(O)
end

#  Buchmann-Lenstra for simple absolute number fields.

# TODO: Ask Carlo if we need to assert that O is "the" equation order.
function new_maximal_order(O::NfOrd)

  K = nf(O)
  if degree(K) == 1
    O.ismaximal = 1
    return O  
  end

  if isdefining_polynomial_nice(K) && (isequation_order(O) || isinteger(gen_index(O)))
    Zx, x = PolynomialRing(FlintZZ, "x", cached = false)
    f1 = Zx(K.pol)
    ds = rres(f1, derivative(f1))
  else
    ds = discriminant(O)
  end

  #First, factorization of the discriminant given by the snf of the trace matrix
  M = trace_matrix(O)
  l = coprime_base(_el_divs(M,ds))
  @vprint :NfOrd 1 "Factors of the discriminant: $l\n "
  l1 = fmpz[]
  OO = O
  @vprint :NfOrd 1 "Trial division of the discriminant\n "
  for d in l
    fac = factor_trial_range(d)[1]
    rem = d
    for (p,v) in fac
      rem = divexact(rem, p^v)
    end
    @vprint :NfOrd 1 "Computing the maximal order at $(collect(keys(fac)))\n "
    O1 = MaximalOrder(O, collect(keys(fac)))
    OO += O1
    if abs(rem)!=1
      push!(l1,abs(rem))
    end
  end
  if isempty(l1)
    OO.ismaximal=1
    return OO
  end
  for i=1:length(l1)
    a, b = ispower(l1[i])
    if a>1
      l1[i]=b
    end
  end
  O1, Q = _TameOverorderBL(OO, l1)
  if !isempty(Q)
    @vprint :NfOrd 1 "I have to factor $Q\n "
    for el in Q
      d=factor(el).fac
      O1+=MaximalOrder(O1, collect(keys(d)))
    end
  end
  O1.ismaximal=1
  return O1::NfOrd
  
end

function DedekindComposite(O::NfOrd, l::Array{fmpz,1})

  O1=O
  l1=fmpz[]
  while true
    @vprint :NfOrd 1 "$l"
    if isempty(l)
      break
    end
    div, f, OO = dedekind_test_composite(O,l[1])
    if div!=1
      @show "Divisor found"
      push!(l1, div)
      push!(l,div)
      l=coprime_base(l)
      continue
    end
    if f
      @show "Can't say"
      filter!(x-> x!=l[1], l)
      continue
    else
      @show "Enlarge!"
      @show index(O1)
      O1+=OO
      filter!(x-> x!=l[1], l)
      continue
    end
  end
  return O, l1
end  


function _TameOverorderBL(O::NfOrd, lp::Array{fmpz,1})
  
  OO=O
  M=coprime_base(lp)
  Q=fmpz[]
  while !isempty(M)
    @vprint :NfOrd 1 M
    q=M[1]
    if isprime(q)
      OO1=pmaximal_overorder(O, q)
      if valuation(discriminant(OO1), q)<valuation(discriminant(OO), q)
        OO+=OO1
      end
      filter!(x-> x!=q, M)
      continue
    end
    OO, q1= _cycleBL(OO,q)
    if q1==1
      filter!(x->x!=q, M)
    elseif q1==q
      push!(Q,q)
      filter!(x-> x!=q, M)
    else
      push!(M, q1)
      push!(M, divexact(q,q1))
      M=coprime_base(M)
      continue
    end
  end
  if isempty(Q)
    OO.ismaximal=1
  end
  return OO, Q

end


function _qradical(O::NfOrd, q::fmpz)
  
  d = degree(O)
  R = ResidueRing(FlintZZ, q, cached=false)
  #First, we compute the q-radical as the kernel of the trace matrix mod q.
  #By theory, this is free if q is prime; if I get a non free module, I have found a factor of q.
  @vprint :NfOrd 1 "radical computation\n "
  #Mat = MatrixSpace(R, d, d, false)(trace_matrix(O))
  Mat = matrix(R, trace_matrix(O))
  M = nullspace(Mat)[2]
  if iszero(M)
    @vprint "The radical is equal to the ideal generated by q"
    return fmpz(1), ideal(O,q)
  end
  if ncols(M) != 0
    M = howell_form(transpose(M))     
    for i = 1:nrows(M)
      if iszero_row(M,i)
        break
      end
      j = i
      while iszero(M[i,j])
        j += 1
      end
      if !isone(M[i,j])
        @vprint :NfOrd 1 "Split: $(M[i,j])"
        return lift(M[i,j]), NfOrdIdl()
      end
    end
  end
  # Now, we have the radical.
  # We want to compute the ring of multipliers.
  # So we need to lift the matrix.
  @vprint :NfOrd 1 "Computing hnf of basis matrix \n "
  MatIdeal = zero_matrix(FlintZZ, d, d)
  for i=1:nrows(M)
    for j=1:degree(O)
      MatIdeal[i,j] = FlintZZ(M[i,j].data)
    end
  end
  gens = NfOrdElem[O(q)]
  for i=1:nrows(M)
    if !iszero_row(MatIdeal, i)
      push!(gens, elem_from_mat_row(O, MatIdeal, i))
    end       
  end
  M2=view(Hecke._hnf_modular_eldiv(MatIdeal, fmpz(q),  :lowerleft), 1:degree(O), 1:degree(O))
  I=NfOrdIdl(O, M2)
  I.gens=gens
  return fmpz(1), I
end

function _cycleBL(O::NfOrd, q::fmpz)
  
  q1,I=_qradical(O,q)
  if q1!=1
    return O,q1
  elseif isdefined(I, :princ_gens) && q==I.princ_gens
    return O, fmpz(1)
  end
  @vprint :NfOrd 1 "ring of multipliers\n"
  O1=ring_of_multipliers(I)
  @vprint :NfOrd 1 "ring of multipliers computed\n"
  if discriminant(O1)!=discriminant(O)
    if gcd(discriminant(O1), q)== 1
      return O1, fmpz(1)
    else
      return _cycleBL(O1,q)
    end
  end
  @vprint :NfOrd 1 "couldn't enlarge\n"
  # (I:I)=OO. Now, we want to prove tameness (or get a factor of q)
  # We have to test that (OO:a)/B is a free Z/qZ module.
  inva=colon(ideal(O,1),I, true)
  M1=basis_mat_inv(inva)
  @assert M1.den==1
  G1=_el_divs(M1.num,q)
  for i=1:length(G1)
    q1=gcd(q,G1[i])
    if q1!=q && q1!=1
      @vprint :NfOrd 1 "Found the factor $q1"
      return O,fmpz(q1)
    end
  end
  @vprint :NfOrd 1 "...is free\n"
  h=2
  ideals=Array{NfOrdIdl,1}(undef, 3)
  ideals[1]=I
  ideals[2]=I^2
  ideals[3]=I^3
  while true
    if h>degree(O)
      error("Not found!")
    end
    I1=(ideals[1]+ideal(O,q))*(ideals[3]+ideal(O,q))
    I2=(ideals[2]+ideal(O,q))^2
    M2=basis_mat(I2, Val{false})*basis_mat_inv(I1, Val{false})
    @assert M2.den==1
    G2=_el_divs(M2.num,q)
    if isempty(G2)
      h+=1
      ideals[1]=ideals[2]
      ideals[2]=ideals[3]
      ideals[3]=ideals[2]*I
      continue
    end
    for i=1:length(G2)
      q1=gcd(q,G2[i])
      if q1!=q && q1!=1
        return O, q1
      end
    end
    break
  end
  f,r = ispower(q,h)
  if f
    return O, r
  else
    return O, q
  end
  
end

function _el_divs(M::fmpz_mat, d::fmpz)
  M1 = _hnf_modular_eldiv(M, d)
  while !isdiag(M1)
    M1 = M1'
    hnf_modular_eldiv!(M1, d)
  end
  l = fmpz[]
  for j = 1:nrows(M1)
    if M1[j,j] != 1
      push!(l, M1[j,j])
    end
  end
  return l
end

function TameOverorderBL(O::NfOrd, lp::Array{fmpz,1}=fmpz[])
    
  # First, we hope that we can get a factorization of the discriminant by computing 
  # the structure of the group OO^*/OO
  OO=O
  list=append!(_el_divs(trace_matrix(OO)),primes_up_to(degree(O)))
  l=coprime_base(list)
  #Some trivial things, maybe useless
  for i=1:length(l)
    a,b=ispower(l[i])
    if a>1
      l[i]=b
    end
    if isprime(l[i])
      @vprint :NfOrd 1 "pmaximal order at $(l[i])\n"
      OO1=pmaximal_overorder(O, l[i])
      if valuation(discriminant(OO1), l[i])<valuation(discriminant(OO), l[i])
        OO+=OO1
      end
      l[i]=0
    end
  end
  push!(l, discriminant(OO))
  append!(l,lp)
  filter!(x-> x!=0, l)
  for i=1:length(l)
    l[i]=abs(l[i])
  end
  M=coprime_base(l)
  Q=fmpz[]
  while !isempty(M)
    @vprint :NfOrd 1 M
    q=M[1]
    if isprime(q)
      OO1=pmaximal_overorder(O, q)
      if valuation(discriminant(OO1), q)<valuation(discriminant(OO), q)
        OO+=OO1
      end
      filter!(x-> x!=q, M)
      continue
    end
    OO, q1= _cycleBL(OO,q)
    if q1==1
      filter!(x->x!=q, M)
    elseif q1==q
      push!(Q,q)
      filter!(x-> x!=q, M)
    else
      push!(M, q1)
      push!(M, divexact(q,q1))
      M=coprime_base(M)
      continue
    end
  end
  if isempty(Q)
    OO.ismaximal=1
  end
  return OO, Q

end

################################################################################
#
#  Conductor
#
################################################################################

# TODO: This can be improved by building the matrix N more clever and using
#       a modular HNF algorithm.
@doc Markdown.doc"""
    conductor(R::NfOrd, S::NfOrd) -> NfAbsOrdIdl
> The conductor $\{x \in S | xS\subseteq R\}$
> for orders $R\subseteq S$.
"""
function conductor(R::NfOrd, S::NfOrd)
  n = degree(R)
  t = basis_mat(R, Val{false}) * basis_mat_inv(S, Val{false})
  @assert isone(t.den)
  basis_mat_R_in_S_inv_num, d = pseudo_inv(t.num)
  M = zero_matrix(FlintZZ, n^2, n)
  B = basis(S, Val{false})
  for k in 1:n
    a = B[k]
    N = representation_matrix(S(a.elem_in_nf, false)) * basis_mat_R_in_S_inv_num
    for i in 1:n
      for j in 1:n
        M[(k - 1)*n + i, j] = N[j, i]
      end
    end
  end
  H = sub(hnf(M), 1:n, 1:n)
  Hinv, new_den = pseudo_inv(transpose(H))
  Hinv = Hinv * basis_mat_R_in_S_inv_num
  return ideal(R, divexact(Hinv, new_den))
end

@doc Markdown.doc"""
    conductor(R::NfOrd) -> NfAbsOrdIdl
> The conductor of $R$ in the maximal order.
"""
conductor(R::NfOrd) = conductor(R, maximal_order(R))
