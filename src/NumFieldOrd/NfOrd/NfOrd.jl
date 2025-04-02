################################################################################
#
#    AbsSimpleNumFieldOrder/AbsSimpleNumFieldOrder.jl : Orders in absolute number fields
#
################################################################################

################################################################################
#
#  Make AbsSimpleNumFieldOrder fully working Nemo ring
#
################################################################################

parent_type(::Type{AbsNumFieldOrderElem{S, T}}) where {S, T} = AbsNumFieldOrder{S, T}

elem_type(::Type{AbsNumFieldOrder{S, T}}) where {S, T} = AbsNumFieldOrderElem{S, T}

ideal_type(::Type{AbsNumFieldOrder{S, T}}) where {S, T} = AbsNumFieldOrderIdeal{S, T}

fractional_ideal_type(::Type{AbsNumFieldOrder{S, T}}) where {S, T} = AbsSimpleNumFieldOrderFractionalIdeal

base_ring(::AbsNumFieldOrder) = ZZ

base_ring_type(::Type{<:AbsNumFieldOrder}) = ZZRing

@doc raw"""
    parent(O::AbsNumFieldOrder) -> AbsNumFieldOrderSet

Returns the parent of $\mathcal O$, that is, the set of orders of the ambient
number field.
"""
parent(O::AbsSimpleNumFieldOrder) = AbsNumFieldOrderSet(nf(O), false)

function contains_equation_order(O::AbsNumFieldOrder)
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

function assure_has_basis(O::AbsNumFieldOrder)
  if isdefined(O, :basis_ord)
    return nothing
  end
  b = O.basis_nf
  d = degree(O)
  B = Vector{elem_type(O)}(undef, d)
  for i in 1:length(b)
    v = ZZRingElem[ZZRingElem(0) for j in 1:d]
    one!(v[i])
    B[i] = AbsNumFieldOrderElem(O, b[i], v)
  end
  O.basis_ord = B
  return nothing
end

function Base.getindex(O::AbsNumFieldOrder, i::Int)
  if iszero(i)
    return zero(O)
  end
  assure_has_basis(O)
  @assert i <= degree(O) && i > 0 "Index must be a positive integer smaller than the dimension"
  return O.basis_ord[i]
end

function assure_has_basis_matrix(O::AbsNumFieldOrder)
  if isdefined(O, :basis_matrix)
    return nothing
  end
  A = O.basis_nf#::Vector{elem_type(nf(O))}
  O.basis_matrix = FakeFmpqMat(basis_matrix(A))
  return nothing
end

function assure_has_basis_mat_inv(O::AbsNumFieldOrder)
  if isdefined(O, :basis_mat_inv)
    return nothing
  end
  M = basis_matrix(FakeFmpqMat, O, copy = false)
  if isdefined(O, :index) && is_lower_triangular(M.num)
    #The order contains the equation order and the matrix is lower triangular
    #The inverse is lower triangular and it has denominator 1
    #to exploit this, I call can_solve
    I = _solve_lt(M.num, scalar_matrix(ZZ, nrows(M), M.den))
    O.basis_mat_inv = FakeFmpqMat(I)
    return nothing
  end
  O.basis_mat_inv = inv(basis_matrix(FakeFmpqMat, O, copy = false))
  return nothing
end

################################################################################
#
#  Basis
#
################################################################################

@inline function basis_ord(O::AbsNumFieldOrder; copy::Bool = true)
  assure_has_basis(O)
  if copy
    res = O.basis_ord::Vector{elem_type(O)}
    return deepcopy(res)::Vector{elem_type(O)}
  else
    return O.basis_ord::Vector{elem_type(O)}
  end
end

@doc raw"""
    basis(O::AbsNumFieldOrder) -> Vector{AbsNumFieldOrderElem}

Returns the $\mathbf Z$-basis of $\mathcal O$.
"""
@inline basis(O::AbsNumFieldOrder; copy::Bool = true) = basis_ord(O, copy = copy)

@doc raw"""
    basis(O::AbsSimpleNumFieldOrder, K::AbsSimpleNumField) -> Vector{AbsSimpleNumFieldElem}

Returns the $\mathbf Z$-basis elements of $\mathcal O$ as elements of the
ambient number field.
"""
function basis(O::AbsSimpleNumFieldOrder, K::AbsSimpleNumField; copy::Bool = true)
  nf(O) != K && error()
  if copy
    return deepcopy(O.basis_nf)
  else
    return O.basis_nf
  end
end

function basis(O::AbsNumFieldOrder{AbsNonSimpleNumField, AbsNonSimpleNumFieldElem}, K::AbsNonSimpleNumField; copy::Bool = true)
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

@doc raw"""
    basis_matrix(O::AbsNumFieldOrder) -> QQMatrix

Returns the basis matrix of $\mathcal O$ with respect to the basis
of the ambient number field.
"""
function basis_matrix(O::AbsNumFieldOrder; copy::Bool = true)
  return QQMatrix(basis_matrix(FakeFmpqMat, O, copy = false))
end

function basis_matrix(::Type{FakeFmpqMat}, O::AbsNumFieldOrder; copy::Bool = true)
  assure_has_basis_matrix(O)
  if copy
    return deepcopy(O.basis_matrix)
  else
    return O.basis_matrix
  end
end

@doc raw"""
    basis_mat_inv(O::AbsNumFieldOrder) -> FakeFmpqMat

Returns the inverse of the basis matrix of $\mathcal O$.
"""
function basis_mat_inv(::Type{FakeFmpqMat}, O::AbsNumFieldOrder; copy::Bool = true)
  assure_has_basis_mat_inv(O)
  if copy
    return deepcopy(O.basis_mat_inv)
  else
    return O.basis_mat_inv
  end
end

function basis_matrix_inverse(O::AbsNumFieldOrder; copy::Bool = true)
  return QQMatrix(basis_mat_inv(FakeFmpqMat, O, copy = false))
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, S::AbsNumFieldOrderSet)
  io = pretty(io)
  print(io, "Set of orders of the number field ")
  print(io, Lowercase(), S.nf)
end

function extra_name(O::AbsNumFieldOrder)
  s = get_name(nf(O))
  if s !== nothing
    return "O_$s"
  end
  return nothing
end

function show(io::IO, O::AbsNumFieldOrder)
  @show_name(io, O)
  @show_special(io, O)
  if is_maximal_known_and_maximal(O)
    show_maximal(io, O)
  else
    show_gen(io, O)
  end
end

function show_gen(io::IO, O::AbsNumFieldOrder)
  io = pretty(io)
  print(io, "Order of ")
  println(io, Lowercase(), nf(O))
  print(io, "with Z-basis ")
  b = basis(O, copy = false)
  # use `typeinfo` in IOContext to change e.g. `AbsSimpleNumFieldElem[1, a, a^2]`
  # to `[1, a, a^2]` when printing the base
  print(IOContext(terse(io), :typeinfo=>typeof(b)), b)
end

function show_maximal(io::IO, O::AbsNumFieldOrder)
  io = pretty(io)
  print(io, "Maximal order of ")
  println(io, Lowercase(), nf(O))
  print(io, "with basis ")
  b = O.basis_nf
    # use `typeinfo` in IOContext to change e.g. `AbsSimpleNumFieldElem[1, a, a^2]`
    # to `[1, a, a^2]` when printing the base
    print(IOContext(terse(io), :typeinfo=>typeof(b)), b)
end

################################################################################
#
#  Discriminant
#
################################################################################

function assure_has_discriminant(O::AbsNumFieldOrder)
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

@doc raw"""
    discriminant(O::AbsSimpleNumFieldOrder) -> ZZRingElem

Returns the discriminant of $\mathcal O$.
"""
function discriminant(O::AbsNumFieldOrder)
  assure_has_discriminant(O)
  return O.disc
end

#TODO: compute differently in equation orders, this is the rres...
@doc raw"""
    reduced_discriminant(O::AbsSimpleNumFieldOrder) -> ZZRingElem

Returns the reduced discriminant, that is, the largest elementary divisor of
the trace matrix of $\mathcal O$.
"""
function reduced_discriminant(O::AbsSimpleNumFieldOrder)
  if is_equation_order(O)
    Zx = polynomial_ring(ZZ, cached = false)[1]
    f = Zx(nf(O).pol)
    return reduced_resultant(f, derivative(f))
  end
  return maximal_elementary_divisor(trace_matrix(O, copy = false))
end

################################################################################
#
#  (Generalized) index
#
################################################################################

@doc raw"""
    gen_index(O::AbsSimpleNumFieldOrder) -> QQFieldElem

Returns the generalized index of $\mathcal O$ with respect to the equation
order of the ambient number field.
"""
function gen_index(O::AbsNumFieldOrder)
  if isdefined(O, :gen_index)
    return deepcopy(O.gen_index)
  else
    #TODO: Remove once the determinant checks if a matrix is upper/lower triangular.
    if is_lower_triangular(basis_matrix(FakeFmpqMat, O, copy = false).num)
      return basis_matrix(FakeFmpqMat, O, copy = false).den^degree(O)//prod_diagonal(basis_matrix(FakeFmpqMat, O, copy = false).num)
    end
    O.gen_index = inv(det(basis_matrix(FakeFmpqMat, O, copy = false)))
    return deepcopy(O.gen_index)
  end
end

@doc raw"""
    index(O::AbsSimpleNumFieldOrder) -> ZZRingElem

Assuming that the order $\mathcal O$ contains the equation order
$\mathbf Z[\alpha]$ of the ambient number field, this function returns the
index $[ \mathcal O : \mathbf Z]$.
"""
function index(O::AbsNumFieldOrder; copy::Bool = false)
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

@doc raw"""
    is_index_divisor(O::AbsSimpleNumFieldOrder, d::ZZRingElem) -> Bool
    is_index_divisor(O::AbsSimpleNumFieldOrder, d::Int) -> Bool

Returns whether $d$ is a divisor of the index of $\mathcal O$. It is assumed
that $\mathcal O$ contains the equation order of the ambient number field.
"""
function is_index_divisor(O::AbsNumFieldOrder, d::IntegerUnion)
  i = index(O, copy = false)
  return iszero(i % d)
end

################################################################################
#
#  Ramified Primes
#
################################################################################

@doc raw"""
    ramified_primes(O::AbsNumFieldOrder) -> Vector{ZZRingElem}

Returns the list of prime numbers that divide $\operatorname{disc}(\mathcal O)$.
"""
function ramified_primes(O::AbsNumFieldOrder)
  return collect(keys(factor(discriminant(O)).fac))
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(O::AbsNumFieldOrder{S, T}, dict::IdDict) where {S, T}
  z = AbsNumFieldOrder{S, T}(O.nf)
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

@doc raw"""
    minkowski_matrix(O::AbsNumFieldOrder, abs_tol::Int = 64) -> ArbMatrix

Returns the Minkowski matrix of $\mathcal O$.  Thus if $\mathcal O$ has degree
$d$, then the result is a matrix in $\operatorname{Mat}_{d\times d}(\mathbf
R)$. The entries of the matrix are real balls of type `ArbFieldElem` with radius less
then `2^-abs_tol`.
"""
function minkowski_matrix(O::AbsNumFieldOrder, abs_tol::Int = 64)
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
  T = Vector{Vector{ArbFieldElem}}(undef, length(B))
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

@doc raw"""
    minkowski_gram_mat_scaled(O::AbsNumFieldOrder, prec::Int = 64) -> ZZMatrix

Let $c$ be the Minkowski matrix as computed by `minkowski_matrix` with precision $p$.
This function computes $d = round(c 2^p)$ and returns $round(d d^t/2^p)$.
"""
function minkowski_gram_mat_scaled(O::AbsNumFieldOrder, prec::Int = 64)
  if isdefined(O, :minkowski_gram_mat_scaled) && O.minkowski_gram_mat_scaled[2] >= prec
    A = deepcopy(O.minkowski_gram_mat_scaled[1])
    shift!(A, prec - O.minkowski_gram_mat_scaled[2])
  else
    c = minkowski_matrix(O, prec+2)
    d = zero_matrix(ZZ, degree(O), degree(O))
    A = zero_matrix(ZZ, degree(O), degree(O))
    round_scale!(d, c, prec)
    ccall((:fmpz_mat_gram, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZMatrix}), A, d)
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
  d = zero_matrix(ZZ, length(B), absolute_degree(K))
  A = zero_matrix(ZZ, length(B), length(B))
  round_scale!(d, c, prec)
  ccall((:fmpz_mat_gram, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZMatrix}), A, d)
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
function _check_elem_in_order(a::T, O::AbsNumFieldOrder{S, T}, ::Val{short} = Val(false)) where {S, T, short}
  assure_has_basis_mat_inv(O)
  t = O.tcontain
  elem_to_mat_row!(t.num, 1, t.den, a)
  t = mul!(t, t, O.basis_mat_inv)
  if short
    return isone(t.den)
  else
    if !isone(t.den)
      return false, Vector{ZZRingElem}()
    else
      v = Vector{ZZRingElem}(undef, degree(O))
      for i in 1:degree(O)
        v[i] = t.num[1, i]
      end
      return true, v
    end
  end
end


function in(a::AbsNonSimpleNumFieldElem, O::AbsNumFieldOrder)
  @assert parent(a) == nf(O)
  return _check_elem_in_order(a, O, Val(true))
end

@doc raw"""
    in(a::NumFieldElem, O::NumFieldOrder) -> Bool

Checks whether $a$ lies in $\mathcal O$.
"""
function in(a::AbsSimpleNumFieldElem, O::AbsSimpleNumFieldOrder)
  @assert parent(a) == nf(O)
  if is_defining_polynomial_nice(nf(O)) && contains_equation_order(O)
    d = denominator!(O.tcontain_fmpz, a)
    if isone(d)
      return true
    end
    exp_index = basis_matrix(FakeFmpqMat, O, copy = false).den
    if !is_divisible_by(exp_index, d)
      return false
    end
    M = basis_mat_inv(FakeFmpqMat, O, copy = false)
    d2 = ppio(M.den, d)[1]
    t = O.tcontain
    elem_to_mat_row!(t.num, 1, t.den, a)
    d = mul!(d, d, d2)
    if fits(Int, d)
      R = residue_ring(ZZ, Int(d), cached = false)[1]
      return _check_containment(R, M.num, t.num)
    else
      R1 = residue_ring(ZZ, d, cached = false)[1]
      return _check_containment(R1, M.num, t.num)
    end
  end
  return _check_elem_in_order(a, O, Val(true))
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

@doc raw"""
    denominator(a::AbsSimpleNumFieldElem, O::AbsSimpleNumFieldOrder) -> ZZRingElem

Returns the smallest positive integer $k$ such that $k \cdot a$ is contained in
$\mathcal O$.
"""
function denominator(a::AbsNonSimpleNumFieldElem, O::AbsNumFieldOrder)
  M = O.tcontain
  elem_to_mat_row!(M.num, 1, M.den, a)
  M = mul!(M, M, basis_mat_inv(FakeFmpqMat, O, copy = false))
  return deepcopy(M.den)
end


function denominator(a::AbsSimpleNumFieldElem, O::AbsSimpleNumFieldOrder)
  @assert parent(a) == nf(O)
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
    M = basis_mat_inv(FakeFmpqMat, O, copy = false)
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
  M = mul!(M, M, basis_mat_inv(FakeFmpqMat, O, copy = false))
  return deepcopy(M.den)
end


function integral_split(a::AbsSimpleNumFieldElem, O::AbsSimpleNumFieldOrder)
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
@doc raw"""
    norm_change_const(O::AbsSimpleNumFieldOrder) -> (Float64, Float64)

Returns $(c_1, c_2) \in \mathbf R_{>0}^2$ such that for all
$x = \sum_{i=1}^d x_i \omega_i \in \mathcal O$ we have
$T_2(x) \leq c_1 \cdot \sum_i^d x_i^2$
and
$\sum_i^d x_i^2 \leq c_2 \cdot T_2(x)$,
where $(\omega_i)_i$ is the $\mathbf Z$-basis of $\mathcal O$.
"""
function norm_change_const(O::AbsSimpleNumFieldOrder; cached::Bool = true)
  if cached && isdefined(O, :norm_change_const)
    return O.norm_change_const::Tuple{BigFloat, BigFloat}
  end

  z = _norm_change_const(O.basis_nf)
  O.norm_change_const = z
  return z::Tuple{BigFloat, BigFloat}
end

function _norm_change_const(v::Vector{AbsSimpleNumFieldElem})
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
  #forcing N to really be Symmetric helps julia - apparently
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

function order(a::Vector{T}; check::Bool = true, isbasis::Bool = false,
               cached::Bool = false) where {T <: NumFieldElem{QQFieldElem}}
  return order(parent(a[1]), a, check = check, isbasis = isbasis, cached = cached)
end

@doc raw"""
    order(a::Vector{AbsSimpleNumFieldElem}; check::Bool = true, cached::Bool = true, isbasis::Bool = false) -> AbsSimpleNumFieldOrder
    order(K::AbsSimpleNumField, a::Vector{AbsSimpleNumFieldElem}; check::Bool = true, cached::Bool = true, isbasis::Bool = false) -> AbsSimpleNumFieldOrder

Returns the order generated by $a$. If `check` is set, it is checked
whether $a$ defines an order, in particular the integrality of the elements is
checked by computing minimal polynomials. If `isbasis` is set, then elements are
assumed to form a $\mathbf{Z}$-basis. If `cached` is set, then the constructed
order is cached for future use.
"""
function order(K::S, a::Vector{T}; check::Bool = true, isbasis::Bool = false,
               cached::Bool = false) where {S <: NumField{QQFieldElem}, T <: NumFieldElem{QQFieldElem}}
  @assert all(x->K == parent(x), a)
  if isbasis
    if check
      b, bmat, bmat_inv, _ = defines_order(K, a)
      if !b
        error("The elements do not define an order")
      else
        return AbsNumFieldOrder(K, bmat, bmat_inv, deepcopy(a), cached)
      end
    else
      return AbsNumFieldOrder(deepcopy(a), cached)
    end
  else
    return _order(K, a, cached = cached, check = check)
  end
end

function order(K, a::Vector; check::Bool = true, isbasis::Bool = false,
               cached::Bool = true)
  local b::Vector{elem_type(K)}
  try
    b = map(K, a)
    b = convert(Vector{elem_type(K)}, b)
  catch
    error("Cannot coerce elements from array into the number field")
  end
  return order(K, b, check = check, cached = cached, isbasis = isbasis)
end

@doc raw"""
    order(K::AbsSimpleNumField, A::QQMatrix; check::Bool = true) -> AbsSimpleNumFieldOrder

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function order(K::S, a::QQMatrix; check::Bool = true,
               cached::Bool = false) where {S <: NumField{QQFieldElem}}
  return order(K, FakeFmpqMat(a); check = check, cached = cached)
end

function order(K::S, a::FakeFmpqMat; check::Bool = true,
               cached::Bool = false) where {S <: NumField{QQFieldElem}}
  if check
    b, ainv, d = defines_order(K, a)
    if !b
      error("The basis matrix does not define an order")
    else
      return AbsNumFieldOrder(K, deepcopy(a), ainv, d, cached)
    end
  else
    return AbsNumFieldOrder(K, deepcopy(a), cached)
  end
end

@doc raw"""
    order(K::AbsSimpleNumField, A::QQMatrix; check::Bool = true) -> AbsSimpleNumFieldOrder

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function order(K::S, a::QQMatrix; check::Bool = true,
               cached::Bool = true) where {S <: Union{AbsSimpleNumField, AbsNonSimpleNumField}}
  return order(K, FakeFmpqMat(a), cached = cached, check = check)
end

@doc raw"""
    order(K::AbsSimpleNumField, A::ZZMatrix, check::Bool = true) -> AbsSimpleNumFieldOrder

Returns the order which has basis matrix $A$ with respect to the power basis
of $K$. If `check` is set, it is checked whether $A$ defines an order.
"""
function order(K::S, a::ZZMatrix, check::Bool = true,
               cached::Bool = true) where {S}
  return order(K, FakeFmpqMat(a), check = check, cached = cached)
end

################################################################################
#
#  Extension of orders
#
################################################################################

function extend(O::AbsNumFieldOrder, elts::Vector{T}; check::Bool = true, cached::Bool = true) where {T}
  # check = true <=> elts[i] is checked to be integral
  return _order(nf(O), elts; cached = cached, check = check, extends = O)
end

function extend(O::RelNumFieldOrder, elts::Vector{T}; check::Bool = true, cached::Bool = true) where {T}
  throw(NotImplemented())
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
@doc raw"""
    any_order(K::number_field)

Return some order in $K$. In case the defining polynomial for $K$
is monic and integral, this just returns the equation order.
In the other case $\mathbb Z[\alpha]\cap \mathbb Z[1/\alpha]$
is returned.
"""
function any_order(K::AbsSimpleNumField)
  f = K.pol
  de = denominator(f)
  g = f * de

  if is_monic(g)
    return equation_order(K)
  else
    d = degree(g)
    M = zero_matrix(ZZ, d, d)
    M[1, 1] = 1
    for i in 2:d
      for j in i:-1:2
        M[i, j] = numerator(coeff(g, d - (i - j)))
      end
    end
    @hassert :AbsNumFieldOrder 1 defines_order(K, FakeFmpqMat(M))[1]
    z = AbsSimpleNumFieldOrder(K, FakeFmpqMat(M))
    z.is_equation_order = false
    return z
  end
end

function any_order(K::AbsNonSimpleNumField)
  normalized_gens = Vector{AbsNonSimpleNumFieldElem}(undef, ngens(K))
  g = gens(K)
  for i in 1:ngens(K)
    f = denominator(K.pol[i]) * K.pol[i]
    if isone(coeff(f, 1))
      normalized_gens[i] = g[i]
    else
      normalized_gens[i] = coeff(f, 1) * g[i]
    end
  end

  b = Vector{AbsNonSimpleNumFieldElem}(undef, degree(K))
  ind = 1
  it = cartesian_product_iterator([1:degrees(K)[i] for i in 1:ngens(K)], inplace = true)
  for i in it
    b[ind] = prod(normalized_gens[j]^(i[j] - 1) for j=1:length(i))
    ind += 1
  end
  return order(K, b, check = false, cached = false)
end

################################################################################
#
#  Equation order
#
################################################################################

equation_order(K, cached::Bool = false) = equation_order(K, cached)

@doc raw"""
    equation_order(K::number_field) -> NumFieldOrder
    equation_order(K::number_field) -> NumFieldOrder

Returns the equation order of the number field $K$.
"""
function equation_order(K::NumField{QQFieldElem}, cached::Bool = true)
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
function __equation_order(K::AbsSimpleNumField)
  f = K.pol
  if isone(denominator(f) * leading_coefficient(f))
    M = FakeFmpqMat(identity_matrix(ZZ, degree(K)))
    Minv = FakeFmpqMat(identity_matrix(ZZ, degree(K)))
    z = AbsSimpleNumFieldOrder(K, M, Minv, basis(K), false)
    z.is_equation_order = true
    return z
  else
    error("Primitive element must be integral")
  end
end

function __equation_order(K::AbsNonSimpleNumField)
  for f in K.pol
    if !isone(denominator(f) * coeff(f, 1))
      error("Generators must be integral")
    end
  end

  M = FakeFmpqMat(identity_matrix(ZZ, degree(K)))
  Minv = FakeFmpqMat(identity_matrix(ZZ, degree(K)))
  z = AbsNumFieldOrder{AbsNonSimpleNumField, AbsNonSimpleNumFieldElem}(K, M, Minv, basis(K), false)
  z.is_equation_order = true
  return z
end

@doc raw"""
    equation_order(f::ZZPolyRingElem; cached::Bool = true, check::Bool = true) -> AbsSimpleNumFieldOrder
    equation_order(f::ZZPolyRingElem; cached::Bool = true, check::Bool = true) -> AbsSimpleNumFieldOrder

Returns the equation order defined by the monic polynomial $f$.
"""
function equation_order(f::ZZPolyRingElem; cached::Bool = true, check::Bool = true)
  is_monic(f) || error("polynomial must be monic")
  K = number_field(f, cached = cached, check = check)[1]
  return equation_order(K)
end

@doc raw"""
    equation_order(f::QQPolyRingElem; cached::Bool = true, check::Bool = true) -> AbsSimpleNumFieldOrder
    equation_order(f::QQPolyRingElem; cached::Bool = true, check::Bool = true) -> AbsSimpleNumFieldOrder

Returns the equation order defined by the monic integral polynomial $f$.
"""
function equation_order(f::QQPolyRingElem; cached::Bool = true, check::Bool = true)
  is_monic(f) || error("polynomial must be integral and monic")
  isone(denominator(f)) || error("polynomial must be integral and monic")

  K = number_field(f, cached = cached, check = check)[1]
  return equation_order(K)
end

@doc raw"""
    equation_order(M::AbsSimpleNumFieldOrder) -> AbsSimpleNumFieldOrder

The equation order of the number field.
"""
equation_order(M::AbsNumFieldOrder) = equation_order(nf(M))

# Construct the smallest order of K containing the elements in elt.
# If check == true, it is checked whether the given elements in elt are integral
# and whether the constructed order is actually an order.
# Via extends one may supply an order which will then be extended by the elements
# in elt.
function _order(K::S, elt::Vector{T}; cached::Bool = true, check::Bool = true, extends = nothing) where {S <: Union{NumField{QQFieldElem}, AbstractAssociativeAlgebra{QQFieldElem}}, T}
  if dim(K) == 0
    return order(K, FakeFmpqMat(zero_matrix(ZZ, 0, 0), ZZ(1)), cached = cached, check = false)::order_type(K)
  end

  elt = unique(elt)
  n = dim(K)
  is_comm = is_commutative(K)

  if extends !== nothing
    extended_order::order_type(K) = extends
    @assert K === _algebra(extended_order)

    if is_maximal_known_and_maximal(extended_order) || length(elt) == 0
      return extended_order
    end
    B = basis_matrix(FakeFmpqMat, extended_order)
    bas = basis(extended_order, K)
    full_rank = true
    m = _det_triangular(numerator(B, copy = false))//denominator(B, copy = false)
  else
    if isempty(elt)
      elt = elem_type(K)[one(K)]
    end
    bas = elem_type(K)[one(K)]
    B = basis_matrix(bas, FakeFmpqMat) # trivially in lower-left HNF
    full_rank = false
    m = QQ()
  end

  dummy_vector = elem_type(K)[K()]
  function in_span_of_B(x::T)
    if mod(denominator(B, copy = false), denominator(x)) == 0
      dummy_vector[1] = x
      C = basis_matrix(dummy_vector, FakeFmpqMat)
      return is_zero_mod_hnf!(div(denominator(B, copy = false), denominator(x))*numerator(C, copy = false), numerator(B, copy = false))
    end
    return false
  end

  for e in elt
    # Check if e is already in the multiplicatively closed module generated by
    # the previous elements of elt
    in_span_of_B(e) && continue

    # Add products of elements of bas and e; in the commutative case this just
    # means multiplying by powers of e, for the non-commutative case see below
    if check
      f = minpoly(e)
      isone(denominator(f)) || error("The elements do not define an order: $e is non-integral")
      df = degree(f) - 1
    else
      df = n - 1
    end

    start = 1
    old_length = length(bas)
    # Commutative case:
    # We only multiply the elements of index start:length(bas) by e .
    # Example: bas = [a_1, ..., a_k] with a_1 = 1. Then
    # new_bas := [e, e*a_2, ..., e*a_k] and we append this to bas and set
    # start := k + 1. In the next iteration, we then have
    # new_bas := [e^2, e^2*a_2, ..., e^2*a_k] (assuming that there was no
    # reduction of the basis in between).

    powers_of_e = 1 # count the iterations, so the power of e by which we multiply
                    # (only relevant in the commutative case)
    while true
      # In the commutative case, this behaves like a "for _ in 1:df"-loop
      if is_comm && powers_of_e == df + 1
        break
      end
      powers_of_e += 1
      new_bas = elem_type(K)[]
      for j in start:length(bas)
        e_bj = e*bas[j]
        if !in_span_of_B(e_bj)
          if is_comm
            push!(new_bas, e_bj)
          else
            # Non-commutative case:
            # If bas = [a_1, ..., a_k], so that the Z-module generated by the a_i
            # contains 1_K, we need to build all the possible words of the form
            # a_?*e*a_?*e*a_?*...*e*a_?. (Because there is a linear combination
            # of the a_i giving 1, we don't need to multiply by powers of e.)
            # In the first iteration we build
            # new_bas := [a_1*e*a_1, a_2*e*a_1, ..., a_k*e*a_1, a_1*e*a_2, ..., a_k*e*a_k]
            # This gets appended to bas and we set start := k + 1.
            # In the next iteration, we get
            # new_bas := [a_1*e*a_1*e*a_1, a_2*e*a_1*e*a_1, ..., a_k*e*a_1*e*a_1,
            #             a_1*e*a_2*e*a_1, a_2*e*a_2*e*a_1, ...
            #             ...
            #            ]
            # (assuming there is no reduction in between) and so on.
            for k in 1:old_length
              t = bas[k]*e_bj
              !in_span_of_B(t) && push!(new_bas, t)
            end
          end
        end
      end
      isempty(new_bas) && break
      start = length(bas) + 1
      append!(bas, new_bas)

      if length(bas) >= n
        # HNF reduce the basis we have so far, if B is already of full rank,
        # we can do this with the modular algorithm
        B = basis_matrix(bas, FakeFmpqMat)
        if full_rank
          # We have M \subseteq B, where M is a former incarnation of B.
          # So we have B.den * M.num/M.den \subseteq B.num \subseteq Z^n, so
          # M.d divides B.den and we can choose (B.den/M.den)*det(M.num) as
          # modulus for the HNF of B.num.
          mm = ZZ(m*denominator(B, copy = false))
          _hnf_integral_modular_eldiv!(B, mm, shape = :lowerleft)
          B = sub(B, nrows(B) - n + 1:nrows(B), 1:n)

          # Check if we have a better modulus
          new_m = _det_triangular(numerator(B, copy = false))//denominator(B, copy = false)
          if new_m < m
            m = new_m
          end
        else
          _hnf!_integral(B)
          k = findfirst(k -> !is_zero_row(B, k), nrows(B) - n + 1:nrows(B))
          B = sub(B, nrows(B) - n + k:nrows(B), 1:n)
          if nrows(B) == n
            full_rank = true
            m = _det_triangular(numerator(B, copy = false))//denominator(B, copy = false)
          end
        end
        bas = elem_type(K)[ elem_from_mat_row(K, numerator(B, copy = false), i, denominator(B, copy = false)) for i in 1:nrows(B) ]
        start = 1
        old_length = length(bas)
        if check && K isa NumField
          @assert isone(bas[1])
        end
      end
    end
  end
  if length(bas) < n
    error("The elements do not define an order: rank too small")
  end
  return order(K, B, cached = cached, check = check)::order_type(K)
end

################################################################################
#
#  Equality
#
################################################################################

# This is the function which is used in dictionaries
function Base.isequal(R::AbsSimpleNumFieldOrder, S::AbsSimpleNumFieldOrder)
  return R === S
end

# Todo: Improve this
function ==(R::AbsNumFieldOrder, S::AbsNumFieldOrder)
  nf(R) != nf(S) && return false
  if discriminant(R) != discriminant(S)
    return false
  end
  assure_has_basis_matrix(R)
  assure_has_basis_matrix(S)
  return _hnf_integral(R.basis_matrix) == _hnf_integral(S.basis_matrix)
end

function hash(R::AbsNumFieldOrder, h::UInt)
  h = hash(nf(R), h)
  h = hash(discriminant(R), h)
  assure_has_basis_matrix(R)
  h = hash(_hnf_integral(R.basis_matrix), h)
  return h
end

@doc raw"""
    is_contained(R::AbsNumFieldOrder, S::AbsNumFieldOrder) -> Bool

Checks if $R$ is contained in $S$.
"""
function is_contained(R::AbsNumFieldOrder, S::AbsNumFieldOrder)
  return (basis_matrix(FakeFmpqMat, R, copy = false)*basis_mat_inv(FakeFmpqMat, S, copy = false)).den == 1
end

function ==(R::AbsNumFieldOrderSet, S::AbsNumFieldOrderSet)
  return R.nf === S.nf
end

function Base.hash(R::AbsNumFieldOrderSet, h::UInt)
  return hash(R.nf, h)
end

################################################################################
#
#  Trace matrix
#
################################################################################

@doc raw"""
    trace_matrix(O::AbsNumFieldOrder) -> ZZMatrix

Returns the trace matrix of $\mathcal O$, that is, the matrix
$(\operatorname{tr}_{K/\mathbf Q}(b_i \cdot b_j))_{1 \leq i, j \leq d}$.
"""
function trace_matrix(O::AbsNumFieldOrder; copy::Bool = true)
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
  g = zero_matrix(ZZ, n, n)
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

@doc raw"""
    +(R::AbsSimpleNumFieldOrder, S::AbsSimpleNumFieldOrder) -> AbsSimpleNumFieldOrder

Given two orders $R$, $S$ of $K$, this function returns the smallest order
containing both $R$ and $S$. It is assumed that $R$, $S$ contain the ambient
equation order and have coprime index.
"""
function +(a::AbsNumFieldOrder, b::AbsNumFieldOrder; cached::Bool = false)
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

function sum_as_Z_modules(O1, O2, z::ZZMatrix = zero_matrix(ZZ, 2 * degree(O1), degree(O1)))
  if contains_equation_order(O1) && contains_equation_order(O2)
    return sum_as_Z_modules_fast(O1, O2, z)
  else
    return O1 + O2
  end
end

function sum_as_Z_modules_fast(O1, O2, z::ZZMatrix = zero_matrix(ZZ, 2 * degree(O1), degree(O1)))
  @hassert :AbsNumFieldOrder 1 contains_equation_order(O1)
  @hassert :AbsNumFieldOrder 1 contains_equation_order(O2)
  K = _algebra(O1)
  R1 = basis_matrix(FakeFmpqMat, O1, copy = false)
  S1 = basis_matrix(FakeFmpqMat, O2, copy = false)
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
  @hassert :AbsNumFieldOrder 1 defines_order(K, M)[1]
  OK = order(K, M, check = false)::typeof(O1)
  if OK isa AbsSimpleNumFieldOrder
    OK.primesofmaximality = union(O1.primesofmaximality, O2.primesofmaximality)
  end
  OK.index = divexact(denominator(M)^d, prod(ZZRingElem[M.num[i, i] for i in 1:d]))
  @hassert :AbsNumFieldOrder 1 numerator(gen_index(OK)) == OK.index
  OK.disc = divexact(discriminant(O1) * index(O1)^2, OK.index^2)
  @hassert :AbsNumFieldOrder 1 det(trace_matrix(OK)) == OK.disc
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
function defines_order(K::S, x::QQMatrix) where {S}
  fl, a, b = defines_order(K, FakeFmpqMat(x))
  if !fl
    return false, x, x
  else
    return true, QQMatrix(a), b
  end
end

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
    R = residue_ring(ZZ, dd, cached = false)[1]
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

@doc raw"""
    different(x::AbsNumFieldOrderElem) -> AbsSimpleNumFieldOrderElem

The different of $x$, i.e. $0$ if $x$ is not a primitive element, or
$f'(x)$ for $f$ the minimal polynomial of $x$ otherwise.
"""
function different(x::AbsNumFieldOrderElem)
  if iszero(x)
    return x
  end
  f = minpoly(x)
  if degree(f) < degree(parent(x))
    return parent(x)(0)
  end
  return derivative(f)(x)
end

@doc raw"""
    different(R::AbsNumFieldOrder) -> AbsNumFieldOrderIdeal

The different ideal of $R$, that is, the ideal generated by all differents
of elements in $R$.
For Gorenstein orders, this is also the inverse ideal of the co-different.
"""
function different(R::AbsNumFieldOrder; proof::Bool = true)
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

@doc raw"""
    discriminant(m::Map, R::AbsSimpleNumFieldOrder) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

The discriminant ideal of $R$ over the maximal order of the domain of the map $m$,
that is, the ideal generated by all norms of differents
of elements in $R$.
"""
function discriminant(m::T, R::AbsSimpleNumFieldOrder) where T <: Map
  D = different(R)
  #TODO: maybe mix norm and different to only generate the discriminant ideal, not the
  #      full different first.
  return norm(m, D)
end

@doc raw"""
    codifferent(R::AbsNumFieldOrder) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

The codifferent ideal of $R$, i.e. the trace-dual of $R$.
"""
function codifferent(R::AbsNumFieldOrder)
  t = trace_matrix(R)
  ti, d = pseudo_inv(t)
  #= if d = |det(t)|, then snf(t) = U S V for unimodular U, V and S being
     Smith, then (ti/d) = V^-1 S^-1 U^-1 and
     d*S^-1 is the Smith of ti - up to that the diagonal would need to be
     reversed. Hence d is a multiple of the largest elem. div.
     so use it!
  =#
  d = abs(d)
#  I = ideal(R, deepcopy(ti))//d  #should probably be false, true
  hnf_modular_eldiv!(ti, d, :lowerleft)
  J = ideal(R, ti; M_in_hnf=true)//d  #should probably be check=false
#  @assert I == J
  return J
end

trace_dual(R::AbsNumFieldOrder) = codifferent(R)

################################################################################
#
#  Conductor
#
################################################################################

# TODO: This can be improved by building the matrix N more clever and using
#       a modular HNF algorithm.
@doc raw"""
    conductor(R::AbsSimpleNumFieldOrder, S::AbsSimpleNumFieldOrder) -> AbsNumFieldOrderIdeal

The conductor $\{x \in R | xS\subseteq R\}$
for orders $R\subseteq S$.
"""
function conductor(R::AbsSimpleNumFieldOrder, S::AbsSimpleNumFieldOrder)
  n = degree(R)
  t = basis_matrix(FakeFmpqMat, R, copy = false) * basis_mat_inv(FakeFmpqMat, S, copy = false)
  if !isone(t.den)
    error("The first order is not contained in the second!")
  end
  basis_mat_R_in_S_inv_num, d = pseudo_inv(t.num)
  M = zero_matrix(ZZ, n^2, n)
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

@doc raw"""
    conductor(R::AbsSimpleNumFieldOrder) -> AbsNumFieldOrderIdeal

The conductor of $R$ in the maximal order.
"""
conductor(R::AbsSimpleNumFieldOrder) = conductor(R, maximal_order(R))
