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

export ==, +, basis, basis_mat, basis_mat_inv, discriminant, degree, den,
       gen_index, EquationOrder, index, isequation_order, isindex_divisor, lll,
       lll_basis, maximal_order, MaximalOrder, minkowski_mat, nf,
       norm_change_const, Order, parent, poverorder, pmaximal_overorder,
       ring_of_integers, signature, trace_matrix, different, codifferent,
       reduced_discriminant

################################################################################
#
#  Make NfOrd fully working Nemo ring
#
################################################################################

Nemo.parent_type(::Type{NfAbsOrdElem{S, T}}) where {S, T} = NfAbsOrd{S, T}

Nemo.elem_type(::Type{NfAbsOrd{S, T}}) where {S, T} = NfAbsOrdElem{S, T}

Nemo.elem_type(::NfAbsOrd{S, T}) where {S, T} = NfAbsOrdElem{S, T}

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

doc"""
    nf(O::NfOrd) -> AnticNumberField

Returns the ambient number field of $\mathcal O$.
"""
@inline nf(O::NfAbsOrd) = O.nf

doc"""
    parent(O::NfOrd) -> NfOrdSet

Returns the parent of $\mathcal O$, that is, the set of orders of the ambient
number field.
"""
parent(O::NfOrd) = NfAbsOrdSet(nf(O), false)

doc"""
    isequation_order(O::NfOrd) -> Bool

Returns whether $\mathcal O$ is the equation order of the ambient number
field.
"""
@inline isequation_order(O::NfAbsOrd) = O.isequation_order

@inline ismaximal_known(O::NfAbsOrd) = O.ismaximal != 0

# The following function should actually do more!
@inline ismaximal(O::NfAbsOrd) = O.ismaximal == 1

################################################################################
#
#  Degree
#
################################################################################

doc"""
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
  B = Vector{elem_type(O)}(d)
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

doc"""
    basis(O::NfOrd) -> Array{NfOrdElem, 1}

Returns the $\mathbf Z$-basis of $\mathcal O$.
"""
@inline basis{T}(O::NfAbsOrd, copy::Type{Val{T}} = Val{true}) = basis_ord(O, copy)

doc"""
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

doc"""
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

doc"""
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

doc"""
    discriminant(O::NfOrd) -> fmpz

Returns the discriminant of $\mathcal O$.
"""
function discriminant(O::NfAbsOrd)
  assure_has_discriminant(O)
  return O.disc
end

#TODO: compute differently in equation orders, this is the rres...
doc"""
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

doc"""
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

doc"""
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

doc"""
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
#  Deepcopy
#
################################################################################

doc"""
    deepcopy(O::NfOrd) -> NfOrd

Makes a copy of $\mathcal O$.
"""
function Base.deepcopy_internal(O::NfAbsOrd{S, T}, dict::ObjectIdDict) where {S, T}
  z = NfAbsOrd{S, T}(O.nf)
  for x in fieldnames(O)
    if x != :nf && isdefined(O, x)
      setfield!(z, x, Base.deepcopy_internal(getfield(O, x), dict))
    end
  end
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

Returns the Minkowski matrix of $\mathcal O$.  Thus if $\mathcal O$ has degree
$d$, then the result is a matrix in $\operatorname{Mat}_{d\times d}(\mathbf
R)$. The entries of the matrix are real balls of type `arb` with radius less
then `2^-abs_tol`.
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
    denominator(a::nf_elem, O::NfOrd) -> fmpz

Returns the smallest positive integer $k$ such that $k \cdot a$ is contained in
$\mathcal O$.
"""
function denominator(a::nf_elem, O::NfOrd)
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
      m = ceil(Int, log(d)/log(2))
      m += m%2
      @assert iseven(m)
      l_max = root(trace(M^m), m) #an upper bound within a factor of 2
                                    #according to a paper by Victor Pan
                                    #https://doi.org/10.1016/0898-1221(90)90236-D
                                    #formula (1) and discussion
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
function Order(::S, a::Array{T, 1}, check::Bool = true,
               cache::Bool = true) where {S <: Union{AnticNumberField, NfAbsNS}, T}
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

doc"""
    Order(K::AnticNumberField, A::FakeFmpqMat, check::Bool = true) -> NfOrd

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function Order(K::S, a::FakeFmpqMat, check::Bool = true,
               cache::Bool = false) where {S}
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

doc"""
    Order(K::AnticNumberField, A::fmpq_mat, check::Bool = true) -> NfOrd

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function Order(K::S, a::fmpq_mat, check::Bool = true,
               cache::Bool = true) where {S}
  return Order(K, FakeFmpqMat(a), cache)
end

doc"""
    Order(K::AnticNumberField, A::fmpz_mat, check::Bool = true) -> NfOrd

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function Order(K::S, a::fmpz_mat, check::Bool = true,
               cache::Bool = true) where {S}
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
function EquationOrder(K::T, cache::Bool = false) where {T}
  M = FakeFmpqMat(identity_matrix(FlintZZ, degree(K)))
  Minv = FakeFmpqMat(identity_matrix(FlintZZ, degree(K)))
  z = NfAbsOrd{T, elem_type(T)}(K, M, Minv, basis(K), cache)
  z.isequation_order = true
  return z
end

doc"""
   equation_order(M::NfOrd) -> NfOrd
> The equation order of then number field.
"""
equation_order(M::NfAbsOrd) = equation_order(nf(M))

function _order(K::AnticNumberField, elt::Array{nf_elem, 1})
  o = one(K)

  if !(o in elt)
    push!(elt, o)
  end

  n = degree(K)

  closed = false

  dold = fmpq(0)

  # Since 1 is in elt, prods will contain all elements
  
  while !closed
    prods = nf_elem[]
    for u in elt
      for v in elt
        push!(prods, u * v)
      end
    end
    
    B = basis_mat(prods)
    H = sub(hnf(B), (rows(B) - degree(K) + 1):rows(B), 1:degree(K))

    # TODO: Just take the product of the diagonal
    dd = H.num[1, 1]
    for i in 2:degree(K)
      dd *= H.num[i, i]
    end
    d = dd//H.den^degree(K)
    
    #d = prod(H.num[i,i] for i=1:degree(K))//(H.den^degree(K))
    #d = det(H)

    if iszero(d)
      error("Elements do not define a module of full rank")
    end

    if dold == d
      closed = true
    else
      dold = d
      elt = nf_elem[]
      for i in 1:n
        push!(elt, elem_from_mat_row(K, H.num, i, H.den))
      end
    end
  end

  # Make an explicit check
  @hassert :NfOrd 1 defines_order(K, elt)[1]
  return Order(K, elt, false)
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

doc"""
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
    t = trace(b[i]^2)
    @assert isinteger(t)
    g[i, i] = numerator(t)
    for j in (i + 1):n
      t = trace(b[i]*b[j])
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

doc"""
    +(R::NfOrd, S::NfOrd) -> NfOrd

Given two orders $R$, $S$ of $K$, this function returns the smallest order
containing both $R$ and $S$. It is assumed that $R$, $S$ contain the ambient
equation order and have coprime index.
"""
function +(a::NfAbsOrd, b::NfAbsOrd)
  nf(a) != nf(b) && error("Orders must have same ambient number field")
  if isone(gcd(index(a), index(b)))
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
    mat=_hnf_modular_eldiv(m, bB.den*aB.den, :lowerleft)
    c = sub(mat, d + 1:2*d, 1:d)
    O = Order(nf(a), FakeFmpqMat(c, aB.den*bB.den), false)
    O.primesofmaximality = unique(vcat(a.primesofmaximality, b.primesofmaximality))
    O.disc=gcd(discriminant(a), discriminant(b))
    if a.disc<0
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
  I= pradical(O, p)
  if isdefined(I, :princ_gen) && I.princ_gen==p
    return deepcopy(O)
  end
  R = ring_of_multipliers(I)
  return R
end

function _poverorder(O::NfAbsOrd, p::Integer)
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
function poverorder(O::NfAbsOrd, p::fmpz)
  if isequation_order(O) && issimple(nf(O))
    return dedekind_poverorder(O, p)
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

doc"""
    pmaximal_overorder(O::NfOrd, p::fmpz) -> NfOrd
    pmaximal_overorder(O::NfOrd, p::Integer) -> NfOrd

This function finds a $p$-maximal order $R$ containing $\mathcal O$. That is,
the index $[ \mathcal O_K : R]$ is not dividible by $p$.
"""
function pmaximal_overorder(O::NfAbsOrd, p::fmpz)
  @vprint :NfOrd 1 "computing p-maximal overorder for $p ... \n"
  if rem(discriminant(O), p^2) != 0
    push!(O.primesofmaximality, p)
    return O
  end

  d = discriminant(O)
  @vprint :NfOrd 1 "extending the order at $p for the first time ... \n"
  OO = poverorder(O, p)
  dd = discriminant(OO)
  v=valuation(dd,p)
  if v==0 || v==1
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
    v = valuation(dd,p)
    if v==0 || v==1
      break
    end
  end
  push!(OO.primesofmaximality, p)
  return OO
end

function pmaximal_overorder(O::NfAbsOrd, p::Integer)
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
    O1 = pmaximal_overorder(O, p)
    if valuation(discriminant(O1), p)< valuation(discriminant(OO),p)
      OO += O1
    end 
    if !(p in OO.primesofmaximality)
      push!(OO.primesofmaximality,p)
    end
    @vprint :NfOrd 1 "done\n"
  end
  return OO
end

doc"""
***
    MaximalOrder(K::NfOrd) -> NfOrd

Returns the maximal order of $K$.
"""
function MaximalOrder(O::NfAbsOrd)
  OO = deepcopy(O)
  @vtime :NfOrd fac = factor(Nemo.abs(discriminant(O)))
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
  On = NfOrd(K, FakeFmpqMat(w*basis_mat(M).num, basis_mat(M).den))
  On.ismaximal = M.ismaximal
  return On
end

doc"""
    lll_basis(M::NfOrd) -> Array{nf_elem, 1}
> A basis for $m$ that is reduced using the LLL algorithm for the Minkowski metric.    
"""
function lll_basis(M::NfOrd)
  I = ideal(M, parent(basis_mat(M).num)(1))
  return lll_basis(I)
end

doc"""
    lll(M::NfOrd) -> NfOrd
> The same order, but with the basis now being LLL reduced wrt. the Minkowski metric.
"""
function lll(M::NfOrd)
  K = nf(M)

  if istotally_real(K)
    return _lll_gram(M)
  end

  I = ideal(M, parent(basis_mat(M).num)(1))

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

# Example

```julia-repl
julia> Qx, xx = FlintQQ["x"];
julia> K, a = NumberField(x^3 + 2, "a");
julia> O = MaximalOrder(K);
```
"""
function MaximalOrder(K::AnticNumberField, cache::Bool = false)
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
    #O = MaximalOrder(K)::NfOrd
    O = new_maximal_order(K)
    _set_maximal_order_of_nf(K, O)
    return O
  end
end

doc"""
***
    maximal_order(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfOrd
    maximal_order(K::AnticNumberField, primes::Array{Integer, 1}) -> NfOrd

Assuming that ``primes`` contains all the prime numbers at which the equation
order $\mathbf{Z}[\alpha]$ of $K = \mathbf{Q}(\alpha)$ is not maximal
(e.g. ``primes`` may contain all prime divisors of the discriminant of
$\mathbf Z[\alpha]$), this function returns the maximal order of $K$.
"""
function maximal_order(K::AnticNumberField, primes::Array{fmpz, 1})
  O = MaximalOrder(K, primes)
  return O
end

maximal_order(K::AnticNumberField, primes::Array{T, 1}) where {T} =
  maximal_order(K, map(FlintZZ, primes))

doc"""
***
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

# This is not optimizied for performance.
# If false, then this returns (false, garbage, garbage).
# If true, then this return (true, basis_mat, basis_mat_inv).
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

doc"""
    different(x::NfOrdElem) -> NfOrdElem
> The different of $x$, ie. $0$ is x is not a primitive element, or
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

doc"""
    different(R::NfOrd) -> NfOrdIdeal
> The differnt ideal of $R$, ie. the ideal generated by all differents
> of elements in $R$.
> For the maximal order, this is also the inverse ideal of the co-different.
"""
function different(R::NfOrd)
  D = ideal(R, different(R(gen(nf(R)))))
  d = abs(discriminant(R))
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

doc"""
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
#  Buchmann-Lenstra for the computation of maximal orders
#
###############################################################################

function new_maximal_order(K::AnticNumberField)
  O=EquationOrder(K)
  if degree(K)==1
    O.ismaximal=1
    return O  
  end
  ds=discriminant(O)
  #First, factorization of the discriminant given by the snf of the trace matrix
  M = trace_matrix(O)
  l = coprime_base(_el_divs(M,ds))
  @vprint :NfOrd 1 "Factors of the discriminant: $l\n "
  l1=fmpz[]
  OO=O
  @vprint :NfOrd 1 "Trial division of the discriminant\n "
  for d in l
    fac = factor_trial_range(d)[1]
    rem= d
    for (p,v) in fac
      rem=divexact(rem, p^v)
    end
    @vprint :NfOrd 1 "Computing the maximal order at $(collect(keys(fac)))\n "
    O1=MaximalOrder(O, collect(keys(fac)))
    OO+=O1
    if abs(rem)!=1
      push!(l1,abs(rem))
    end
  end
  if isempty(l1)
    OO.ismaximal=1
    return OO
  end
  for i=1:length(l1)
    a,b = ispower(l1[i])
    if a>1
      l1[i]=b
    end
  end
  #=
  O1, l=DedekindComposite(O, deepcopy(l1))
  if discriminant(O1)!=discriminant(O)
    OO+=O1
    push!(l, discriminant(O1))
  end
  append!(l1,l)
  l1=coprime_base(l1)
  =#
  O1, Q=_TameOverorderBL(OO, l1)
  if !isempty(Q)
    @vprint :NfOrd 1 "I have to factor $Q\n "
    for el in Q
      d=factor(el).fac
      O1+=MaximalOrder(O1, collect(keys(d)))
    end
  end
  O1.ismaximal=1
  return O1
  
end

function DedekindComposite(O::NfOrd, l::Array{fmpz,1})

  @vprint :NfOrd 1 "Dedekind criterion with $rem \n"
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
  
  R=ResidueRing(FlintZZ, q, cached=false)
  #First, we compute the q-radical as the kernel of the trace matrix mod q.
  #By theory, this is free if q is prime; if I get a non free module, I have found a factor of q.
  @vprint :NfOrd 1 "radical computation\n "
  Mat=MatrixSpace(R, degree(O), degree(O), false)(trace_matrix(O))
  M=nullspace(Mat)[1]
  if iszero(M)
    @vprint "The radical is equal to the ideal generated by q"
    return fmpz(1), ideal(O,q)
  end
  if cols(M)!=0
    M=howell_form(transpose(M))     
    for i=1:rows(M)
      if iszero_row(M,i)
        break
      end
      j=i
      while iszero(M[i,j])
        j+=1
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
  MatIdeal=zero_matrix(FlintZZ, rows(M)+degree(O), cols(M))
  for i=1:rows(M)
    for j=1:degree(O)
      MatIdeal[i,j]=FlintZZ(M[i,j].data)
    end
  end
  for i=1:degree(O)
    MatIdeal[i+rows(M), i]=q
  end
  gens=[O(q)]
  for i=1:rows(M)
    if !iszero_row(MatIdeal, i)
      push!(gens, elem_from_mat_row(O, MatIdeal, i))
    end       
  end
  M2=sub(Hecke._hnf_modular_eldiv(MatIdeal, fmpz(q),  :lowerleft), rows(M)+1:degree(O)+rows(M), 1:degree(O))
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
  ideals=Array{NfOrdIdl,1}(3)
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
  M1=_hnf_modular_eldiv(M, d)
  while !isdiag(M1)
    M1= M1'
    hnf_modular_eldiv!(M1, d)
  end
  l=fmpz[]
  for j=1:rows(M1)
    if M1[j,j]!=1
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
