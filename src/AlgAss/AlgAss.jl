add_assertion_scope(:StructureConstantAlgebra)

################################################################################
#
#  Basic field access
#
################################################################################

function denominator_of_multiplication_table(A::StructureConstantAlgebra{QQFieldElem})
  get_attribute!(A, :denominator_of_multiplication_table) do
    den = one(ZZ)
    mt = multiplication_table(A)
    d = degree(A)
    for i in 1:d
      for j in 1:d
        for k in 1:d
          den = lcm!(den, den, denominator(mt[i, j, k]))
        end
      end
    end
    return den
  end::ZZRingElem
end

base_ring(A::StructureConstantAlgebra{T}) where {T} = A.base_ring::parent_type(T)

has_one(A::StructureConstantAlgebra) = A.has_one

iszero(A::StructureConstantAlgebra) = A.iszero

function Generic.dim(A::StructureConstantAlgebra)
  if iszero(A)
    return 0
  end
  return size(multiplication_table(A, copy = false), 1)
end

degree(A::StructureConstantAlgebra) = dim(A)

elem_type(::Type{StructureConstantAlgebra{T}}) where {T} = AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}

order_type(::StructureConstantAlgebra{QQFieldElem}) = AlgAssAbsOrd{StructureConstantAlgebra{QQFieldElem}, elem_type(StructureConstantAlgebra{QQFieldElem})}
order_type(::Type{StructureConstantAlgebra{QQFieldElem}}) = AlgAssAbsOrd{StructureConstantAlgebra{QQFieldElem}, elem_type(StructureConstantAlgebra{QQFieldElem})}

order_type(::StructureConstantAlgebra{T}) where { T <: NumFieldElem } = AlgAssRelOrd{T, fractional_ideal_type(order_type(parent_type(T)))}
order_type(::Type{StructureConstantAlgebra{T}}) where { T <: NumFieldElem } = AlgAssRelOrd{T, fractional_ideal_type(order_type(parent_type(T)))}

@doc raw"""
    multiplication_table(A::StructureConstantAlgebra; copy::Bool = true) -> Array{RingElem, 3}

Given an algebra $A$ this function returns the multiplication table of $A$:
If the function returns $M$ and the basis of $A$ is $e_1,\dots, e_n$ then
it holds $e_i \cdot e_j = \sum_k M[i, j, k] \cdot e_k$.
"""
function multiplication_table(A::StructureConstantAlgebra; copy::Bool = true)
  if copy
    return deepcopy(A.mult_table)
  else
    return A.mult_table
  end
end

################################################################################
#
#  Commutativity
#
################################################################################

is_commutative_known(A::StructureConstantAlgebra) = (A.is_commutative != 0)

@doc raw"""
    is_commutative(A::StructureConstantAlgebra) -> Bool

Returns `true` if $A$ is a commutative ring and `false` otherwise.
"""
function is_commutative(A::StructureConstantAlgebra)
  if is_commutative_known(A)
    return A.is_commutative == 1
  end
  for i = 1:dim(A)
    for j = i + 1:dim(A)
      if multiplication_table(A, copy = false)[i, j, :] != multiplication_table(A, copy = false)[j, i, :]
        A.is_commutative = 2
        return false
      end
    end
  end
  A.is_commutative = 1
  return true
end

################################################################################
#
#  Construction
#
################################################################################

# This only works if base_ring(A) is a field (probably)
# Returns (true, one) if there is a one and (false, something) if not.
function find_one(A::StructureConstantAlgebra)
  if iszero(A)
    return true, elem_type(base_ring(A))[]
  end
  n = dim(A)
  M = zero_matrix(base_ring(A), n^2, n)
  c = zero_matrix(base_ring(A), n^2, 1)
  for k = 1:n
    kn = (k - 1)*n
    c[kn + k, 1] = base_ring(A)(1)
    for i = 1:n
      for j = 1:n
        M[i + kn, j] = deepcopy(multiplication_table(A, copy = false)[j, k, i])
      end
    end
  end
  Mc = hcat(M, c)
  rref!(Mc)
  if iszero(Mc[n, n])
    return false, zeros(base_ring(A), n)
  end
  if n != 1 && !iszero(Mc[n + 1, n + 1])
    return false, zeros(base_ring(A), n)
  end
  cc = _solve_ut(sub(Mc, 1:n, 1:n), sub(Mc, 1:n, (n + 1):(n + 1)))
  one = elem_type(base_ring(A))[ cc[i, 1] for i = 1:n ]
  return true, one
end

raw"""
    zero_algebra(R::Ring) -> StructureConstantAlgebra

Return the zero ring as an associative $R$-algebra.
"""
function zero_algebra(R::Ring)
  A = StructureConstantAlgebra{elem_type(R)}(R)
  A.iszero = true
  A.is_commutative = 1
  A.has_one = true
  A.one = elem_type(R)[]
  A.mult_table = Array{elem_type(R), 3}(undef, 0, 0, 0)
  return A
end

raw"""
    associative_algebra(R::Ring, mult_table::Array{T, 3}[, one::Vector{T}]; check::Bool = true) where T

    Associative Algebra over `R` with generators $e_1,\dots,e_d$ where `size(mult_table) == (d, d, d)` and $e_ie_j$ = `sum(mult_table[i,j,k]*e[k] for k in 1:d)`.
    Unless `check = false`, this includes (time consuming) associativity and distributivity checks.
    If `one` is given, record the element with the according coefficient vector as one element of the algebra.
"""
associative_algebra(R::Ring, mult_table::Array{<:Any, 3}; check::Bool = true) = StructureConstantAlgebra(R, mult_table; check)
associative_algebra(R::Ring, mult_table::Array{T, 3}, one::Vector{T}; check::Bool = true) where T = StructureConstantAlgebra(R, mult_table, one; check)

function StructureConstantAlgebra(R::Ring, mult_table::Array{T, 3}, one::Vector{T}; check::Bool = get_assertion_level(:StructureConstantAlgebra) > 0) where {T}
  @req all(isequal(size(mult_table, 1)), size(mult_table)) "Multiplication must have dimensions have same length"

  if size(mult_table, 1) == 0
    return zero_algebra(R)
  end
  A = StructureConstantAlgebra{T}(R, mult_table, one)
  if check
    @req check_associativity(A) "Multiplication table does not define associative operation"
    @req check_distributivity(A) "Multiplication table does not define distributive operation"
  end
  return A
end

function StructureConstantAlgebra(R::Ring, mult_table::Array{T, 3}; check::Bool = get_assertion_level(:StructureConstantAlgebra) > 0) where {T}
  @req all(isequal(size(mult_table, 1)), size(mult_table)) "Multiplication must have dimensions have same length"
  if size(mult_table, 1) == 0
    return zero_algebra(R)
  end
  A = StructureConstantAlgebra{T}(R)
  A.mult_table = mult_table
  A.iszero = false
  has_one, one = find_one(A)
  A.has_one = has_one
  if has_one
    A.one = one
  end
  if check
    @req check_associativity(A) "Multiplication table does not define associative operation"
    @req check_distributivity(A) "Multiplication table does not define distributive operation"
  end
  return A
end

# Does anyone actually use this?
function StructureConstantAlgebra(R::Ring, d::Int, arr::Vector{T}) where {T}
  if d == 0
    return _zero_algebra(R)
  end
  mult_table = Array{T, 3}(undef, d, d, d)
  n = d^2
  for i in 1:d
    for j in 1:d
      for k in 1:d
        mult_table[i, j, k] = arr[(i - 1) * n + (j - 1) * d + k]
      end
    end
  end
  return StructureConstantAlgebra(R, mult_table)
end

raw"""
    associative_algebra(f::PolyRingElem)

Associative algebra $R[x]/f$.
"""
associative_algebra(f::PolyRingElem) = StructureConstantAlgebra(f)
function StructureConstantAlgebra(f::PolyRingElem)
  R = base_ring(parent(f))
  n = degree(f)
  Rx = parent(f)
  x = gen(Rx)
  B = Vector{elem_type(Rx)}(undef, 2*n - 1)
  B[1] = Rx(1)
  for i = 2:2*n - 1
    B[i] = mod(B[i - 1]*x, f)
  end
  mult_table = Array{elem_type(R), 3}(undef, n, n, n)
  for i = 1:n
    for j = i:n
      for k = 1:n
        mult_table[i, j, k] = coeff(B[i + j - 1], k - 1)
        mult_table[j, i, k] = coeff(B[i + j - 1], k - 1)
      end
    end
  end
  one = map(R, zeros(Int, n))
  one[1] = R(1)
  A = StructureConstantAlgebra(R, mult_table, one)
  A.is_commutative = 1
  return A
end

function StructureConstantAlgebra(K::AbsSimpleNumField)
  A = StructureConstantAlgebra(K.pol)
  m = AbsAlgAssToNfAbsMor(A, K, identity_matrix(FlintQQ, dim(A)), identity_matrix(FlintQQ, dim(A)))
  A.maps_to_numberfields = [ (K, m) ]
  return A, m
end

# Reduces the rows of M in `rows` modulo N in place.
# Assumes that N is in lowerleft HNF.
function reduce_rows_mod_hnf!(M::ZZMatrix, N::ZZMatrix, rows::Vector{Int})
  for i in rows
    for j = ncols(M):-1:1
      if iszero(M[i, j])
        continue
      end

      t = fdiv(M[i, j], N[j, j])
      for k = 1:j
        M[i, k] = M[i, k] - t*N[j, k]
      end
    end
  end
  return M
end

function addmul!(a::AlgAssAbsOrdElem, b::ZZRingElem, c::AlgAssAbsOrdElem)
  return add!(a, a, b * c)
end

function addmul!(a::AbsNumFieldOrderElem, b::ZZRingElem, c::AbsNumFieldOrderElem)
  return add!(a, a, b * c)
end

@doc raw"""
    quo(O::AbsNumFieldOrder, I::AbsNumFieldOrderIdeal, p::Union{ Int, ZZRingElem })
    quo(O::AlgAssAbsOrd, I::AlgAssAbsOrdIdl, p::Union{ Int, ZZRingElem })
      -> StructureConstantAlgebra, AbsOrdToAlgAssMor

Given an ideal $I$ such that $p \cdot O \subseteq I \subseteq O$ this function
constructs $O/I$ as an algebra over $\mathbb F_p$ together with the projection
map $O \to O/I$.
It is assumed that $p$ is prime.
"""
quo(O::Union{AbsNumFieldOrder, AlgAssAbsOrd}, I::Union{AbsNumFieldOrderIdeal, AlgAssAbsOrdIdl}, p::IntegerUnion) = StructureConstantAlgebra(O, I, p)

function StructureConstantAlgebra(O::Union{AbsNumFieldOrder, AlgAssAbsOrd}, I::Union{AbsNumFieldOrderIdeal, AlgAssAbsOrdIdl}, p::IntegerUnion)
  @assert order(I) === O

  n = degree(O)
  bmatI = integral_basis_matrix_wrt(I, O, copy = false)

  basis_elts = Vector{Int}()
  for i = 1:n
    if is_coprime(bmatI[i, i], p)
      continue
    end

    push!(basis_elts, i)
  end

  r = length(basis_elts)
  Fp = GF(p, cached = false)

  if r == 0
    A = _zero_algebra(Fp)

    local _image_zero

    let A = A
      function _image_zero(a::Union{ AbsNumFieldOrderElem, AlgAssAbsOrdElem })
        return A()
      end
    end

    local _preimage_zero

    let O = O
      function _preimage_zero(a::AssociativeAlgebraElem)
        return O()
      end
    end

    OtoA = AbsOrdToAlgAssMor{typeof(O), elem_type(Fp)}(O, A, _image_zero, _preimage_zero)
    return A, OtoA
  end

  BO = basis(O, copy = false)
  mult_table = Array{elem_type(Fp), 3}(undef, r, r, r)
  for i = 1:r
    M = representation_matrix_mod(BO[basis_elts[i]], ZZRingElem(p))
    if r != degree(O)
      M = reduce_rows_mod_hnf!(M, bmatI, basis_elts)
    end
    for j = 1:r
      for k = 1:r
        mult_table[i, j, k] = Fp(M[basis_elts[j], basis_elts[k]])
      end
    end
  end

  if isone(BO[1])
    one = zeros(Fp, r)
    one[1] = Fp(1)
    A = StructureConstantAlgebra(Fp, mult_table, one)
  else
    A = StructureConstantAlgebra(Fp, mult_table)
  end
  if is_commutative(O)
    A.is_commutative = 1
  end

  local _image

  let I = I, A = A, basis_elts = basis_elts, Fp = Fp
    function _image(a::Union{AbsNumFieldOrderElem, AlgAssAbsOrdElem})
      c = coordinates(mod(a, I), copy = false)
      return A([ Fp(c[i]) for i in basis_elts ])
    end
  end

  local _preimage

  let BO = BO, basis_elts = basis_elts, r = r
    function _preimage(a::AssociativeAlgebraElem)
      z = zero(O)::eltype(BO)
      ca = coefficients(a, copy = false)
      for i in 1:r
        l = lift(ZZ, ca[i])
        addmul!(z, l, BO[basis_elts[i]])
      end
      return z
      #return sum(lift(coefficients(a, copy = false)[i])*BO[basis_elts[i]] for i = 1:r)
    end
  end

  OtoA = AbsOrdToAlgAssMor{typeof(O), elem_type(Fp)}(O, A, _image, _preimage)

  return A, OtoA
end

# Requires M to be in lower left HNF
function reduce_vector_mod_hnf(v::ZZMatrix, M::ZZMatrix)
  @assert ncols(v) == nrows(M) && nrows(M) == ncols(M)

  w = Vector{ZZRingElem}(undef, length(v))
  t = ZZRingElem()
  for i in length(v):-1:1
    t = fdiv(v[1, i], M[i, i])
    for j in 1:i
      w[j] = v[1, j] - t*M[i, j]
    end
  end
  return w
end

@doc raw"""
    quo(I::AbsNumFieldOrderIdeal, J::AbsNumFieldOrderIdeal, p::Union{ Int, ZZRingElem })
    quo(I::AlgAssAbsOrdIdl, J::AlgAssAbsOrdIdl, p::Union{ Int, ZZRingElem })
      -> StructureConstantAlgebra, AbsOrdToAlgAssMor

Given an ideal $J$ such that $p \cdot I \subseteq J \subseteq I$ this function
constructs $I/J$ as an algebra over $\mathbb F_p$ together with the projection
map $I \to I/J$.
It is assumed that $p$ is prime.
"""
quo(I::Union{ AbsNumFieldOrderIdeal, AlgAssAbsOrdIdl }, J::Union{ AbsNumFieldOrderIdeal, AlgAssAbsOrdIdl }, p::Union{ Integer, ZZRingElem }) = StructureConstantAlgebra(I, J, p)

function StructureConstantAlgebra(I::Union{ AbsNumFieldOrderIdeal, AlgAssAbsOrdIdl }, J::Union{AbsNumFieldOrderIdeal, AlgAssAbsOrdIdl}, p::IntegerUnion)
  @assert order(I) === order(J)

  O = order(I)

  n = degree(O)
  BmatJinI = hnf(basis_matrix(J, copy = false)*basis_mat_inv(I, copy = false), :lowerleft)
  @assert isone(BmatJinI.den) "J is not a subset of I"
  BmatJinI = BmatJinI.num
  basis_elts = Vector{Int}()
  for i = 1:n
    if valuation(BmatJinI[i, i], p) == 0
      continue
    end

    push!(basis_elts, i)
  end

  r = length(basis_elts)
  Fp = GF(p, cached = false)

  if r == 0
    A = _zero_algebra(Fp)

    local _image_zero

    let A = A
      function _image_zero(a::Union{ AbsNumFieldOrderElem, AlgAssAbsOrdElem })
        return A()
      end
    end

    local _preimage_zero

    let O = O
      function _preimage_zero(a::AssociativeAlgebraElem)
        return O()
      end
    end

    OtoA = AbsOrdToAlgAssMor{typeof(O), elem_type(Fp)}(O, A, _image_zero, _preimage_zero)
    return A, OtoA
  end

  BI = basis(I, copy = false)
  BmatI = basis_matrix(I, copy = false)
  BmatIinv = inv(BmatI)

  mult_table = Array{elem_type(Fp), 3}(undef, r, r, r)
  for i = 1:r
    M = FakeFmpqMat(representation_matrix(_elem_in_algebra(BI[basis_elts[i]], copy = false)))
    M = mul!(M, BmatI, M)
    M = mul!(M, M, BmatIinv)
    @assert M.den == 1
    M = M.num # M is now the representation matrix in the basis of I
    if r != degree(O)
      M = reduce_rows_mod_hnf!(M, BmatJinI, basis_elts)
    end
    for j = 1:r
      for k = 1:r
        mult_table[i, j, k] = Fp(M[basis_elts[j], basis_elts[k]])
      end
    end
  end

  A = StructureConstantAlgebra(Fp, mult_table)
  if is_commutative(O)
    A.is_commutative = 1
  end

  t = FakeFmpqMat(zero_matrix(FlintZZ, 1, n))

  local _image

  let BmatJinI = BmatJinI, I = I, r = r, A = A, t = t, Fp = Fp
    function _image(a::Union{AbsNumFieldOrderElem, AlgAssAbsOrdElem})
      elem_to_mat_row!(t.num, 1, t.den, _elem_in_algebra(a, copy = false))
      t = mul!(t, t, basis_mat_inv(I, copy = false))
      @assert isone(t.den) "Not an element of the domain"
      c = reduce_vector_mod_hnf(t.num, BmatJinI)
      return A([ Fp(c[i]) for i in basis_elts ])
    end
  end

  local _preimage

  let BI = BI, basis_elts = basis_elts, r = r
    function _preimage(a::AssociativeAlgebraElem)
      return O(sum(lift(ZZ, coefficients(a, copy = false)[i])*BI[basis_elts[i]] for i = 1:r))
    end
  end

  OtoA = AbsOrdToAlgAssMor{typeof(O), elem_type(Fp)}(O, A, _image, _preimage)

  return A, OtoA
end

#=
Qx, x = QQ["x"];
f = x^2 + 12*x - 92;
K, a = number_field(f, "a");
OK = maximal_order(K);
Ky, y = K["y"];
g = y^2 - 54*y - 73;
L, b = number_field(g, "b");
OL = maximal_order(L);
p = prime_decomposition(OK, 2)[1][1]
=#

# Assume that O is relative order over OK, I is an ideal of O and p is a prime
# ideal of OK with pO \subseteq I. O/I is an OK/p-algebra.
#
# The idea is to compute pseudo-basis of O and I respectively, for which the
# coefficient ideals have zero p-adic valuation. Then we can think in the
# localization at p and do as in the case of principal ideal domains.
@doc raw"""
    quo(O::RelNumFieldOrder, I::RelNumFieldOrderIdeal, p::Union{ AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal })
    quo(O::AlgAssRelOrd, I::AlgAssRelOrdIdl, p::Union{ AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal })
      -> StructureConstantAlgebra, RelOrdToAlgAssMor

Given an ideal $I$ such that $p \cdot O \subseteq I \subseteq O$ this function
constructs $O/I$ as an algebra over the finite field $R/p$, where $R$ is the
order of $p$, together with the projection map $O \to O/I$.
It is assumed that `R == base_ring(O)` and that $p$ is prime.
"""
quo(O::Union{ RelNumFieldOrder{T, S}, AlgAssRelOrd{T, S} }, I::Union{ RelNumFieldOrderIdeal{T, S}, AlgAssRelOrdIdl{T, S} }, p::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal}) where {T, S} = StructureConstantAlgebra(O, I, p)

function StructureConstantAlgebra(O::Union{ RelNumFieldOrder{T, S}, AlgAssRelOrd{T, S} }, I::Union{ RelNumFieldOrderIdeal{T, S}, AlgAssRelOrdIdl{T, S} }, p::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal}, mF = residue_field(order(p), p)[2]) where {T, S}

  K = _algebra(O)

  new_basisO, new_basisI, new_bmatO, new_bmatI = coprime_bases(O, I, p)
  new_bmatinvO = inv(new_bmatO)

  Fp = codomain(mF)
  mmF = extend(mF, _base_ring(K))
  invmmF = pseudo_inv(mmF)

  basis_elts = Int[]
  reducers = Int[]

  for i in 1:degree(O)
    v = valuation(new_bmatI[i, i], p)
    @assert v >= 0
    if v == 0
      push!(reducers, i)
    else
      push!(basis_elts, i)
    end
  end

  r = length(basis_elts)

  if r == 0
    A = _zero_algebra(Fp)

    local _image_zero

    let A = A
      function _image_zero(a::Union{ RelNumFieldOrderElem, AlgAssRelOrdElem })
        return A()
      end
    end

    local _preimage_zero

    let O = O
      function _preimage_zero(a::AssociativeAlgebraElem)
        return O()
      end
    end

    OtoA = RelOrdToAlgAssMor(O, A, _image_zero, _preimage_zero)
    return A, OtoA
  end

  reverse!(reducers)

  tmp_matrix = zero_matrix(_base_ring(K), 1, degree(O))

  function _coeff(c)
    cfcs = coefficients(c, copy = false)
    for i = 1:degree(O)
      tmp_matrix[1, i] = cfcs[i]
    end
    return tmp_matrix*new_bmatinvO
  end

  mult_table = Array{elem_type(Fp), 3}(undef, r, r, r)
  for i in 1:r
    for j in 1:r
      c = new_basisO[basis_elts[i]][1]*new_basisO[basis_elts[j]][1]
      coeffs_c = _coeff(c)

      for k in reducers
        d = -coeffs_c[k]//new_bmatI[k, k]
        c = c + d*new_basisI[k][1]
      end
      coeffs_c = _coeff(c)
      for k in 1:degree(O)
        if !(k in basis_elts)
          @assert iszero(coeffs_c[k])
        end
      end
      for k in 1:r
        mult_table[i, j, k] = mmF(coeffs_c[basis_elts[k]])
      end
    end
  end

  if isone(new_basisO[basis_elts[1]][1])
    one = zeros(Fp, length(basis_elts))
    one[1] = Fp(1)
    A = StructureConstantAlgebra(Fp, mult_table, one)
  else
    A = StructureConstantAlgebra(Fp, mult_table)
  end
  if is_commutative(O)
    A.is_commutative = 1
  end

  local _image

  let A = A, O = O
    function _image(a::Union{ RelNumFieldOrderElem, AlgAssRelOrdElem })
      c = _elem_in_algebra(a, copy = false)
      coeffs_c = _coeff(c)
      for k in reducers
        d = -coeffs_c[k]//new_bmatI[k, k]
        c = c + d*new_basisI[k][1]
      end
      coeffs_c = _coeff(c)
      for k in 1:degree(O)
        if !(k in basis_elts)
          @assert iszero(coeffs_c[k])
        end
      end
      b = A()
      for k in 1:r
        b.coeffs[k] = mmF(coeffs_c[basis_elts[k]])
      end
      return b
    end
  end

  lifted_basis_of_A = []

  for i in basis_elts
    c = coprime_to(new_basisO[i][2], p)
    b = invmmF(inv(mmF(c)))*c*new_basisO[i][1]
    @assert b in O
    push!(lifted_basis_of_A, b)
  end

  local _preimage
  let lifted_basis_of_A = lifted_basis_of_A, O = O, invmmF = invmmF
    function _preimage(v::AssociativeAlgebraElem)
      return O(sum((invmmF(v.coeffs[i]))*lifted_basis_of_A[i] for i in 1:r))
    end
  end

  OtoA = RelOrdToAlgAssMor(O, A, _image, _preimage)

  return A, OtoA
end

@doc raw"""
    quo(I::RelNumFieldOrderIdeal, J::RelNumFieldOrderIdeal, p::Union{ AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal })
    quo(I::AlgAssRelOrdIdl, J::AlgAssRelOrdIdl, p::Union{ AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal })
      -> StructureConstantAlgebra, RelOrdToAlgAssMor

Given an ideal $J$ such that $p \cdot I \subseteq J \subseteq I$ this function
constructs $I/J$ as an algebra over the finite field $R/p$, where $R$ is the
order of $p$, together with the projection map $I \to I/J$.
It is assumed that `order(I) === order(J)` and in particular both should be
defined. Further, it should hold `R == base_ring(order(I))` and $p$ should be
prime.
"""
quo(I::Union{ RelNumFieldOrderIdeal{T, S}, AlgAssRelOrdIdl{T, S} }, J::Union{ RelNumFieldOrderIdeal{T, S}, AlgAssRelOrdIdl{T, S} }, p::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal}, mF = residue_field(order(p), p)[2]) where {T, S} = StructureConstantAlgebra(I, J, p, mF)

function StructureConstantAlgebra(I::Union{ RelNumFieldOrderIdeal{T, S}, AlgAssRelOrdIdl{T, S} }, J::Union{ RelNumFieldOrderIdeal{T, S}, AlgAssRelOrdIdl{T, S} }, p::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal}, mF = residue_field(order(p), p)[2]) where {T, S}
  @assert _algebra(I) === _algebra(J)
  @assert order(I) === order(J)

  O = order(I)
  K = _algebra(I)
  new_basisI, new_basisJ, new_bmatI, new_bmatJinI = coprime_bases(I, J, p)
  bmatinvI = inv(new_bmatI)

  Fp = codomain(mF)
  mmF = extend(mF, _base_ring(K))
  invmmF = pseudo_inv(mmF)

  basis_elts = Int[]
  reducers = Int[]

  for i in 1:degree(O)
    v = valuation(new_bmatJinI[i, i], p)
    @assert v >= 0
    if v == 0
      push!(reducers, i)
    else
      push!(basis_elts, i)
    end
  end

  r = length(basis_elts)

  if r == 0
    A = _zero_algebra(Fp)

    local _image_zero

    let A = A
      function _image_zero(a::Union{ RelNumFieldOrderElem, AlgAssRelOrdElem })
        return A()
      end
    end

    local _preimage_zero

    let O = O
      function _preimage_zero(a::AssociativeAlgebraElem)
        return O()
      end
    end

    OtoA = RelOrdToAlgAssMor(O, A, _image_zero, _preimage_zero)
    return A, OtoA
  end

  reverse!(reducers)

  tmp_matrix = zero_matrix(_base_ring(K), 1, degree(O))

  function _coeff(c)
    for i = 1:degree(O)
      tmp_matrix[1, i] = coefficients(c, copy = false)[i]
    end
    return tmp_matrix*bmatinvI
  end

  mult_table = Array{elem_type(Fp), 3}(undef, r, r, r)

  for i in 1:r
    for j in 1:r
      c = new_basisI[basis_elts[i]][1]*new_basisI[basis_elts[j]][1]
      coeffs = _coeff(c)

      for k in reducers
        d = -coeffs[k]//new_bmatJinI[k, k]
        c = c + d * new_basisJ[k][1]
      end
      coeffs = _coeff(c)
      for k in 1:degree(O)
        if !(k in basis_elts)
          @assert iszero(coeffs[k])
        end
      end
      for k in 1:r
        mult_table[i, j, k] = mmF(coeffs[basis_elts[k]])
      end
    end
  end

  if isone(new_basisI[basis_elts[1]][1])
    one = zeros(Fp, length(basis_elts))
    one[1] = Fp(1)
    A = StructureConstantAlgebra(Fp, mult_table, one)
  else
    A = StructureConstantAlgebra(Fp, mult_table)
  end
  if is_commutative(O)
    A.is_commutative = 1
  end

  local _image

  let O = O, new_bmatJinI = new_bmatJinI, A = A
    function _image(a::Union{ RelNumFieldOrderElem, AlgAssRelOrdElem })
      c = _elem_in_algebra(a, copy = false)
      coeffs = _coeff(c)
      for k in reducers
        d = -coeffs[k]//new_bmatJinI[k, k]
        c = c + d*new_basisJ[k][1]
      end
      coeffs = _coeff(c)
      for k in 1:degree(O)
        if !(k in basis_elts)
          @assert iszero(coeffs[k])
        end
      end
      b = A()
      for k in 1:r
        b.coeffs[k] = mmF(coeffs[basis_elts[k]])
      end
      return b
    end
  end


  lifted_basis_of_A = []

  for i in basis_elts
    c = coprime_to(new_basisI[i][2], p)
    b = invmmF(inv(mmF(c)))*c*new_basisI[i][1]
    @assert O(b) in I
    push!(lifted_basis_of_A, b)
  end

  local _preimage

  let O = O, invmmF = invmmF, lifted_basis_of_A = lifted_basis_of_A
    function _preimage(v::AssociativeAlgebraElem)
      return O(sum((invmmF(v.coeffs[i])) * lifted_basis_of_A[i] for i in 1:r))
    end
  end

  OtoA = RelOrdToAlgAssMor(O, A, _image, _preimage)

  return A, OtoA
end

function StructureConstantAlgebra(A::Generic.MatRing{T}) where { T <: FieldElem }
  n = A.n
  K = base_ring(A)
  n2 = n^2
  # We use the matrices M_{ij} with a 1 at row i and column j and zeros everywhere else as the basis for A.
  # We sort "column major", so A[i + (j - 1)*n] corresponds to the matrix M_{ij}.
  # M_{ik}*M_{lj} = 0, if k != l, and M_{ik}*M_{kj} = M_{ij}
  mult_table = zeros(K, n2, n2, n2)
  oneK = one(K)
  for j = 0:n:(n2 - n)
    for k = 1:n
      kn = (k - 1)*n
      for i = 1:n
        mult_table[i + kn, k + j, i + j] = oneK
      end
    end
  end
  oneA = zeros(K, n2)
  for i = 1:n
    oneA[i + (i - 1)*n] = oneK
  end
  A = StructureConstantAlgebra(K, mult_table, oneA)
  A.is_commutative = ( n == 1 ? 1 : 2 )
  return A
end

function StructureConstantAlgebra(A::StructureConstantAlgebra)
  R = base_ring(A)
  d = dim(A)
  return A, hom(A, A, identity_matrix(R, d), identity_matrix(R, d))
end

###############################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::StructureConstantAlgebra)
  print(io, "Associative algebra of dimension ", dim(A), " over ", base_ring(A))
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(A::StructureConstantAlgebra{T}, dict::IdDict) where {T}
  B = StructureConstantAlgebra{T}(base_ring(A))
  for x in fieldnames(typeof(A))
    if x != :base_ring && isdefined(A, x)
      setfield!(B, x, Base.deepcopy_internal(getfield(A, x), dict))
    end
  end
  B.base_ring = A.base_ring
  return B
end

################################################################################
#
#  Subalgebra
#
################################################################################

# Builds a multiplication table for the subalgebra of A with basis matrix B.
# We assume ncols(B) == dim(A).
# A rref of B will be computed IN PLACE! If return_LU is Val{true}, a LU-factorization
# of transpose(rref(B)) is returned.
function _build_subalgebra_mult_table!(A::StructureConstantAlgebra{T}, B::MatElem{T}, ::Val{return_LU} = Val(false); is_commutative = false) where { T, return_LU }
  K = base_ring(A)
  n = dim(A)
  r = rref!(B)
  if r == 0
    if return_LU
      return Array{elem_type(K), 3}(undef, 0, 0, 0), solve_init(B)
    else
      return Array{elem_type(K), 3}(undef, 0, 0, 0)
    end
  end

  basis = Vector{elem_type(A)}(undef, r)
  for i = 1:r
    basis[i] = elem_from_mat_row(A, B, i)
  end

  Btr = transpose(B)
  #_, p, L, U = lu(Btr)
  LL = solve_init(Btr)

  iscom = is_commutative || Hecke.is_commutative(A)

  mult_table = Array{elem_type(K), 3}(undef, r, r, r)
  c = A()
  d = zero_matrix(K, n, 1)
  for i = 1:r
    for j = 1:r
      if iscom && j < i
        continue
      end
      c = mul!(c, basis[i], basis[j])
      #for i in 1:nrows(d)
      #  d[p[i], 1] = c.coeffs[i]
      #end
      #_d = deepcopy(d)
      #mc = matrix(K, length(c.coeffs), 1, c.coeffs)
      #@assert can_solve_with_solution(Btr, mc)[1]
      #d = _solve_lt(L, d)
      #d = _solve_ut(U, d)
      #@assert Btr * d == mc
      dd = solve(LL, c.coeffs, side = :right)
      for k = 1:r
        #@assert dd[k] == d[k, 1]
        mult_table[i, j, k] = dd[k]
        #mult_table[i, j, k] = d[k, 1]
        if iscom && i != j
          #@assert dd[k] == d[k, 1]
          mult_table[j, i, k] = dd[k]
          #mult_table[j, i, k] = d[k, 1]
        end
      end
    end
  end

  if return_LU
    return mult_table, LL #p, L, U, LL
  else
    return mult_table
  end
end

@doc raw"""
     subalgebra(A::StructureConstantAlgebra, e::AssociativeAlgebraElem, idempotent::Bool = false,
                action::Symbol = :left)
       -> StructureConstantAlgebra, AbsAlgAssMor

Given an algebra $A$ and an element $e$, this function constructs the algebra
$e \cdot A$ (if `action == :left`) respectively $A \cdot e$ (if `action == :right`)
and a map from this algebra to $A$.
If `idempotent` is `true`, it is assumed that $e$ is idempotent in $A$.
"""
function subalgebra(A::StructureConstantAlgebra{T}, e::AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}, idempotent::Bool = false, action::Symbol = :left) where {T}
  @assert parent(e) == A
  R = base_ring(A)
  n = dim(A)
  # This is the basis of e*A, resp. A*e
  B1 = representation_matrix(e, action)
  mult_table, LL = _build_subalgebra_mult_table!(A, B1, Val(true))

  r = size(mult_table, 1)

  if r == 0
    eA = _zero_algebra(R)
    return eA, hom(eA, A, zero_matrix(R, 0, n))
  end

  # The basis matrix of e*A resp. A*e with respect to A is
  basis_mat_of_eA = sub(B1, 1:r, 1:n)

  if idempotent
    # c = A()
    # d = zero_matrix(R, n, 1)
    # for k = 1:n
    #   d[p[k], 1] = e.coeffs[k]
    # end
    # d = _solve_lt(L, d)
    # d = _solve_ut(U, d)
    # v = Vector{elem_type(R)}(undef, r)
    # for i in 1:r
    #   v[i] = d[i, 1]
    # end
    vv = solve(LL, e.coeffs, side = :right)
    #@assert v == vv[1:r]
    eA = StructureConstantAlgebra(R, mult_table, vv[1:r])
  else
    eA = StructureConstantAlgebra(R, mult_table)
  end

  if A.is_commutative == 1
    eA.is_commutative = 1
  end

  if idempotent
    # We have the map eA -> A, given by the multiplying with basis_mat_of_eA.
    # But there is also the canonical projection A -> eA, a -> ea.
    # We compute the corresponding matrix.
    B2 = representation_matrix(e, action)
    C = zero_matrix(R, n, r)
    for i in 1:n
      #for k = 1:n
      #  d[p[k], 1] = B2[i, k]
      #end
      #d = _solve_lt(L, d)
      #d = _solve_ut(U, d)
      dd = solve(LL, [B2[i, k] for k in 1:n], side = :right)
      #@assert [d[i, 1] for i in 1:nrows(d)] == dd
      for k in 1:r
        C[i, k] = dd[k]
      end
    end
    eAtoA = hom(eA, A, basis_mat_of_eA, C)
  else
    eAtoA = hom(eA, A, basis_mat_of_eA)
  end
  return eA, eAtoA
end

@doc raw"""
    subalgebra(A::StructureConstantAlgebra, basis::Vector{AssociativeAlgebraElem}) -> StructureConstantAlgebra, AbsAlgAssMor

Returns the subalgebra of $A$ generated by the elements in `basis` and a map
from this algebra to $A$.
"""
function subalgebra(A::StructureConstantAlgebra{T}, basis::Vector{AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}}; is_commutative = false) where T
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  for i = 1:length(basis)
    elem_to_mat_row!(M, i, basis[i])
  end
  mt = _build_subalgebra_mult_table!(A, M; is_commutative = is_commutative)
  B = StructureConstantAlgebra(base_ring(A), mt)
  return B, hom(B, A, sub(M, 1:length(basis), 1:dim(A)))
end

###############################################################################
#
#  Trace Matrix
#
###############################################################################

function _assure_trace_basis(A::StructureConstantAlgebra{T}) where T
  if !isdefined(A, :trace_basis_elem)
    A.trace_basis_elem = Vector{T}(undef, dim(A))
    for i=1:length(A.trace_basis_elem)
      A.trace_basis_elem[i]=sum(multiplication_table(A, copy = false)[i,j,j] for j= 1:dim(A))
    end
  end
  return nothing
end

@doc raw"""
    trace_matrix(A::StructureConstantAlgebra) -> MatElem

Returns a matrix $M$ over the base ring of $A$ such that
$M_{i, j} = \mathrm{tr}(b_i \cdot b_j)$, where $b_1, \dots, b_n$ is the
basis of $A$.
"""
function trace_matrix(A::StructureConstantAlgebra)
  _assure_trace_basis(A)
  F = base_ring(A)
  n = dim(A)
  M = zero_matrix(F, n, n)
  for i = 1:n
    M[i,i] = tr(A[i]^2)
  end
  for i = 1:n
    for j = i+1:n
      x = tr(A[i]*A[j])
      M[i,j] = x
      M[j,i] = x
    end
  end
  return M
end

###############################################################################
#
#  Center
#
###############################################################################

function _rep_for_center!(M::T, A::StructureConstantAlgebra) where T<: MatElem
  n = dim(A)
  mt = multiplication_table(A, copy = false)
  tt = zero(base_ring(A))
  for i=1:n
    for j = 1:n
      for k = 1:n
        if tt isa QQFieldElem
          sub!(tt, mt[i, j, k], mt[j, i, k])
          M[k + (i-1)*n, j] = tt
        else
          M[k + (i-1)*n, j] = mt[i, j, k] - mt[j, i, k]
        end
      end
    end
  end
  return nothing
end

@doc raw"""
    center(A::StructureConstantAlgebra) -> StructureConstantAlgebra, AbsAlgAssMor

Returns the center $C$ of $A$ and the inclusion $C \to A$.
"""
function center(A::StructureConstantAlgebra{T}) where {T}
  if is_commutative(A)
    B, mB = StructureConstantAlgebra(A)
    return B, mB
  end
  if isdefined(A, :center)
    return A.center::Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, StructureConstantAlgebra{T})}
  end

  n = dim(A)
  M = zero_matrix(base_ring(A), n^2, n)
  # I concatenate the difference between the right and left representation matrices.
  _rep_for_center!(M, A)
  B = kernel(M, side = :right)
  k = ncols(B)
  res = Vector{elem_type(A)}(undef, k)
  for i=1:k
    res[i]= A(T[B[j,i] for j=1:n])
  end
  C, mC = subalgebra(A, res, is_commutative = true)
  A.center = C, mC

  # Store the idempotents of A if known so that the Wedderburn decompositions
  # can align

  if isdefined(A, :decomposition)
    idems = elem_type(C)[has_preimage_with_preimage(mC, StoA(one(S)))[2] for (S, StoA) in A.decomposition]
    set_attribute!(C, :central_idempotents, idems)
  end

  return C, mC
end

################################################################################
#
#  Idempotents
#
################################################################################

# See W. Eberly "Computations for Algebras and Group Representations" p. 126.
# TODO: fix the type
function _find_non_trivial_idempotent(A::StructureConstantAlgebra{T}) where { T } #<: Union{fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, FqPolyRepFieldElem, fqPolyRepFieldElem} }
  if dim(A) == 1
    error("Dimension of algebra is 1")
  end
  while true
    a = rand(A)
    if isone(a) || iszero(a)
      continue
    end
    mina = minpoly(a)
    if is_irreducible(mina)
      if degree(mina) == dim(A)
        error("Algebra is a field")
      end
      continue
    end
    if is_squarefree(mina)
      e = _find_idempotent_via_squarefree_poly(A, a, mina)
    else
      e = _find_idempotent_via_non_squarefree_poly(A, a, mina)
    end
    if isone(e) || iszero(e)
      continue
    end
    return e
  end
end

#function _find_idempotent_via_non_squarefree_poly(A::StructureConstantAlgebra{T}, a::AssociativeAlgebraElem{T}, mina::Union{fpPolyRingElem, FpPolyRingElem, FqPolyRepPolyRingElem, fqPolyRepPolyRingElem}) where { T <: Union{fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, FqPolyRepFieldElem, fqPolyRepFieldElem} }
function _find_idempotent_via_non_squarefree_poly(A::StructureConstantAlgebra{T}, a::AssociativeAlgebraElem{T}, mina) where {T}
  fac = factor(mina)
  if length(fac) == 1
    return zero(A)
  end
  sf_part = one(parent(mina))
  for (k, v) in fac
    mul!(sf_part, sf_part, k)
  end
  b = sf_part(a)
  # This is not really an algebra, only a right sided ideal
  bA, bAtoA = subalgebra(A, b, false, :left)

  # Find an element e of bA such that e*x == x for all x in bA
  M = zero_matrix(base_ring(A), dim(bA), 0)
  for i = 1:dim(bA)
    M = hcat(M, representation_matrix(bA[i], :right))
  end

  N = zero_matrix(base_ring(A), 0, 1)
  for i = 1:dim(bA)
    N = vcat(N, matrix(base_ring(A), dim(bA), 1, coefficients(bA[i])))
  end
  MN = hcat(transpose(M), N)
  r = rref!(MN)
  be = _solve_ut(sub(MN, 1:r, 1:dim(bA)), sub(MN, 1:r, (dim(bA) + 1):(dim(bA) + 1)))
  e = bAtoA(bA([ be[i, 1] for i = 1:dim(bA) ]))
  return e
end

# A should be semi-simple
# See W. Eberly "Computations for Algebras and Group Representations" p. 89.
function _extraction_of_idempotents(A::StructureConstantAlgebra, only_one::Bool = false)
  Z, ZtoA = center(A)
  if dim(Z) == 1
    error("Dimension of centre is 1")
  end

  a = ZtoA(rand(Z))
  f = minpoly(a)
  while is_irreducible(f)
    if degree(f) == dim(A)
      error("Cannot find idempotents (algebra is a field)")
    end
    a = ZtoA(rand(Z))
    f = minpoly(a)
  end

  fac = factor(f)
  fi = [ k for k in keys(fac.fac) ]
  l = length(fi)
  R = parent(f)
  if only_one
    r = zeros(R, l)
    r[1] = one(R)
    g = crt(r, fi)
    return g(a)
  else
    oneR = one(R)
    zeroR = zero(R)
    gi = Vector{elem_type(R)}(undef, l)
    r = zeros(R, l)
    for i = 1:l
      r[i] = oneR
      gi[i] = crt(r, fi)
      r[i] = zeroR
    end
    return [ g(a) for g in gi ]
  end
end

#function _find_idempotent_via_squarefree_poly(A::StructureConstantAlgebra{T}, a::AssociativeAlgebraElem{T}, mina::Union{fpPolyRingElem, FpPolyRingElem, FqPolyRepPolyRingElem, fqPolyRepPolyRingElem}) where { T <: Union{fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, FqPolyRepFieldElem, fqPolyRepFieldElem} }
# TODO: fix the type
function _find_idempotent_via_squarefree_poly(A::StructureConstantAlgebra{T}, a::AssociativeAlgebraElem{T}, mina) where {T}
  B = StructureConstantAlgebra(mina)
  idemB = _extraction_of_idempotents(B, true)

  e = dot(coefficients(idemB, copy = false), [ a^k for k = 0:(degree(mina) - 1) ])
  return e
end

# TODO: fix the type
function _primitive_idempotents(A::StructureConstantAlgebra{T}) where { T } #<: Union{fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, FqPolyRepFieldElem, fqPolyRepFieldElem} }
  if dim(A) == 1
    return [ one(A) ]
  end

  e = _find_non_trivial_idempotent(A)

  idempotents = Vector{elem_type(A)}()

  eA, m1 = subalgebra(A, e, true, :left)
  eAe, m2 = subalgebra(eA, m1\e, true, :right)
  if dim(eAe) == dim(A)
    push!(idempotents, e)
  else
    idems = _primitive_idempotents(eAe)
    append!(idempotents, [ m1(m2(idem)) for idem in idems ])
  end

  f = (1 - e)
  fA, n1 = subalgebra(A, f, true, :left)
  fAf, n2 = subalgebra(fA, n1\f, true, :right)

  if dim(fAf) == dim(A)
    push!(idempotents, f)
  else
    idems = _primitive_idempotents(fAf)
    append!(idempotents, [ n1(n2(idem)) for idem in idems ])
  end

  return idempotents
end

################################################################################
#
#  Matrix Algebra
#
################################################################################

# This computes a "matrix type" basis for A.
# See W. Eberly "Computations for Algebras and Group Representations" p. 121.
# TODO: fix the type
function _matrix_basis(A::StructureConstantAlgebra{T}, idempotents::Vector{S}) where { T, S }#<: Union{fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, FqPolyRepFieldElem, fqPolyRepFieldElem}, S <: AssociativeAlgebraElem{T, StructureConstantAlgebra{T}} }
  k = length(idempotents)
  # Compute a basis e_ij of A (1 <= i, j <= k) with
  # e_11 + e_22 + ... + e_kk = 1 and e_rs*e_tu = \delta_st*e_ru.
  new_basis = Vector{elem_type(A)}(undef, k^2) # saved column major: new_basis[i + (j - 1)*k] = e_ij
  for i = 1:k
    new_basis[i + (i - 1)*k] = idempotents[i]
  end

  a = idempotents[1]
  for i = 2:k
    b = idempotents[i]
    e = a + b
    eA, m1 = subalgebra(A, e, true, :left)
    eAe, m2 = subalgebra(eA, m1\e, true, :right)

    aa = m2\(m1\(a))
    bb = m2\(m1\(b))

    # We compute an element x of eAe which fulfils
    # aa*x == x, bb*x == 0, x*aa == 0 and x*bb == x.
    M1 = representation_matrix(aa - one(eAe), :left)
    M2 = representation_matrix(bb, :left)
    M3 = representation_matrix(aa, :right)
    M4 = representation_matrix(bb - one(eAe), :right)

    M = hcat(M1, M2, M3, M4)
    xx = eAe(kernel(M, side = :left)[1, :])
    x = m1(m2(xx))

    new_basis[1 + (i - 1)*k] = x # this is e_1i

    # We compute an element y of eAe which fulfils
    # aa*y == 0, bb*y == y, y*aa == y, y*bb == 0, y*xx == bb, xx*y == aa.
    N1 = representation_matrix(aa, :left)
    N2 = representation_matrix(bb - one(eAe), :left)
    N3 = representation_matrix(aa - one(eAe), :right)
    N4 = representation_matrix(bb, :right)
    N5 = representation_matrix(xx, :right)
    N6 = representation_matrix(xx, :left)
    N = hcat(N1, N2, N3, N4, N5, N6)
    NN = zero_matrix(base_ring(A), 4*dim(eAe), 1)
    NN = vcat(NN, matrix(base_ring(A), dim(eAe), 1, coefficients(bb)))
    NN = vcat(NN, matrix(base_ring(A), dim(eAe), 1, coefficients(aa)))
    b, yy = can_solve_with_solution(transpose(N), NN; side = :right)
    @assert b
    y = m1(m2(eAe([ yy[i, 1] for i = 1:dim(eAe) ])))

    new_basis[i] = y # this is e_i1
  end

  for j = 2:k
    jk = (j - 1)*k
    e1j = new_basis[1 + jk]
    for i = 2:k
      new_basis[i + jk] = new_basis[i]*e1j # this is e_ij
    end
  end
  return new_basis
end

# Assumes that A is central and isomorphic to a matrix algebra of base_ring(A)
# TODO: fix the type
function _as_matrix_algebra(A::StructureConstantAlgebra{T}) where { T } # <: Union{fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, FqPolyRepFieldElem, fqPolyRepFieldElem}, S <: AssociativeAlgebraElem{T, StructureConstantAlgebra{T}} }

  idempotents = _primitive_idempotents(A)
  @assert length(idempotents)^2 == dim(A)
  Fq = base_ring(A)

  B = matrix_algebra(Fq, length(idempotents))

  matrix_basis = _matrix_basis(A, idempotents)

  # matrix_basis is another basis for A. We build the matrix for the basis change.
  M = zero_matrix(Fq, dim(A), dim(A))
  for i = 1:dim(A)
    elem_to_mat_row!(M, i, matrix_basis[i])
  end
  return B, hom(A, B, inv(M), M)
end

################################################################################
#
#  Direct product
#
################################################################################

@doc raw"""
    direct_product(algebras::StructureConstantAlgebra...; task::Symbol = :sum)
      -> StructureConstantAlgebra, Vector{AbsAlgAssMor}, Vector{AbsAlgAssMor}
    direct_product(algebras::Vector{StructureConstantAlgebra}; task::Symbol = :sum)
      -> StructureConstantAlgebra, Vector{AbsAlgAssMor}, Vector{AbsAlgAssMor}

Returns the algebra $A = A_1 \times \cdots \times A_k$. `task` can be
":sum", ":prod", ":both" or ":none" and determines which canonical maps
are computed as well: ":sum" for the injections, ":prod" for the projections.
"""
function direct_product(algebras::Vector{<: StructureConstantAlgebra{T}}; task::Symbol = :sum) where T
  @req !isempty(algebras) "Must be at least one algebra for direct product (or specifiy the field)"
  return direct_product(algebras..., task = task)
end

function direct_product(K, algebras::Vector{<: StructureConstantAlgebra{T}}; task::Symbol = :sum) where T
  if length(algebras) == 0
    mt = zeros(K, 0, 0, 0)
    A = StructureConstantAlgebra(K, mt; check = false)
    return A, morphism_type(eltype(algebras), typeof(A))[]
  end
  return direct_product(algebras..., task = task)
end

function direct_product(a::StructureConstantAlgebra{T}, _algebras::StructureConstantAlgebra{T}...; task::Symbol = :sum) where T
  algebras = (a, _algebras...)
  @assert !isempty(algebras)
  @assert all( A -> base_ring(A) == base_ring(algebras[1]), algebras)
  @assert task in [ :prod, :sum, :both, :none ]

  d = sum( dim(A) for A in algebras )
  mt = zeros(base_ring(algebras[1]), d, d, d)
  offset = 0
  for B in algebras
    mtB = multiplication_table(B, copy = false)
    dd = dim(B)
    for i = 1:dd
      for j = 1:dd
        for k = 1:dd
          mt[i + offset, j + offset, k + offset] = mtB[i, j, k]
        end
      end
    end
    offset += dd
  end
  A = StructureConstantAlgebra(base_ring(algebras[1]), mt; check = false)
  if task == :none
    return A
  end

  if task == :sum || task == :both
    inj = Vector{morphism_type(typeof(A), typeof(algebras[1]))}(undef, length(algebras))
  end
  if task == :prod || task == :both
    proj = Vector{morphism_type(typeof(A), typeof(algebras[1]))}(undef, length(algebras))
  end
  offset = 0
  for i = 1:length(algebras)
    B = algebras[i]
    M = zero_matrix(base_ring(A), dim(A), dim(B))
    for i = 1:dim(B)
      M[i + offset, i] = one(base_ring(A))
    end
    Mt = transpose(M)
    if task == :sum || task == :both
      inj[i] = hom(B, A, Mt, M)
    end
    if task == :prod || task == :both
      proj[i] = hom(A, B, M, Mt)
    end
    offset += dim(B)
  end
  if task == :prod
    return A, proj
  elseif task == :sum
    return A, inj
  else
    return A, proj, inj
  end
end

@doc raw"""
    direct_product(fields::AnticNumberFields...)
      -> StructureConstantAlgebra{QQFieldElem}, Vector{AbsAlgAssToNfAbsMor}
    direct_product(fields::Vector{AnticNumberFields})
      -> StructureConstantAlgebra{QQFieldElem}, Vector{AbsAlgAssToNfAbsMor}

Returns the algebra $A = K_1 \times \cdots \times K_k$ and the projection
maps $A ->> K_i$.
"""
function direct_product(fields::Vector{AbsSimpleNumField})
  return direct_product(fields...)
end

function direct_product(_field::AbsSimpleNumField, _fields::AbsSimpleNumField...)
  fields = (_field, _fields...)
  algebras = Tuple{StructureConstantAlgebra{QQFieldElem}, AbsAlgAssToNfAbsMor{StructureConstantAlgebra{QQFieldElem}, elem_type(StructureConstantAlgebra{QQFieldElem}), AbsSimpleNumField, QQMatrix}}[ StructureConstantAlgebra(K) for K in fields ]
  A, proj, inj = direct_product([ B for (B, m) in algebras ], task = :both)
  A.decomposition = [ (algebras[i][1], inj[i]) for i = 1:length(algebras) ]
  maps_to_fields = Vector{AbsAlgAssToNfAbsMor{StructureConstantAlgebra{QQFieldElem}, elem_type(StructureConstantAlgebra{QQFieldElem}), AbsSimpleNumField, QQMatrix}}(undef, length(fields))
  for i = 1:length(fields)
    # Assumes, that the map algebras[i] -> K is given by the identity matrix
    maps_to_fields[i] = AbsAlgAssToNfAbsMor(A, fields[i], proj[i].mat, proj[i].imat)
  end
  A.maps_to_numberfields = Tuple{AbsSimpleNumField, AbsAlgAssToNfAbsMor{StructureConstantAlgebra{QQFieldElem}, elem_type(StructureConstantAlgebra{QQFieldElem}), AbsSimpleNumField, QQMatrix}}[ (fields[i], maps_to_fields[i]) for i = 1:length(fields) ]
  return A, maps_to_fields
end

################################################################################
#
#  Quaternion algebras
#
################################################################################

function quaternion_algebra2(K::Field, a::T, b::T) where { T <: FieldElem }

  M = zeros(K, 4, 4, 4)

  M[1, 1, 1] = one(K) # 1*1=1
  M[1, 2, 2] = one(K) # 1*i=i
  M[1, 3, 3] = one(K) # 1*j=j
  M[1, 4, 4] = one(K) # 1*ij=1

  M[2, 1, 2] = one(K)
  M[2, 2, 1] = a
  M[2, 3, 4] = one(K)
  M[2, 4, 3] = a

  M[3, 1, 3] = one(K)
  M[3, 2, 4] = -one(K)
  M[3, 3, 1] = b
  M[3, 4, 2] = -b

  M[4, 1, 4] = one(K)
  M[4, 2, 3] = -a
  M[4, 3, 2] = b
  M[4, 4, 1] = -a*b

  return StructureConstantAlgebra(K, M, [ one(K), zero(K), zero(K), zero(K) ])
end

quaternion_algebra2(K::Field, a::Int, b::Int) = quaternion_algebra2(K, K(a), K(b))

quaternion_algebra2(a::Int, b::Int) = quaternion_algebra2(FlintQQ, QQFieldElem(a), QQFieldElem(b))

################################################################################
#
#  Opposite algebra
#
################################################################################

function opposite_algebra(A::StructureConstantAlgebra)
  K = base_ring(A)
  B = basis(A)
  d = dim(A)
  z = Array{elem_type(K), 3}(undef, d, d, d)
  for i in 1:d
    for j in 1:d
      z[i, j, :] = A.mult_table[j, i, :]
    end
  end
  o = one(A).coeffs

  B = StructureConstantAlgebra(K, z, o)
  return B, hom(A, B, identity_matrix(K, d), identity_matrix(K, d))
end

