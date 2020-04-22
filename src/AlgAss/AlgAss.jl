export issplit, multiplication_table, restrict_scalars, center

################################################################################
#
#  Basic field access
#
################################################################################

base_ring(A::AlgAss{T}) where {T} = A.base_ring::parent_type(T)

has_one(A::AlgAss) = A.has_one

iszero(A::AlgAss) = A.iszero

function Generic.dim(A::AlgAss)
  if iszero(A)
    return 0
  end
  return size(multiplication_table(A, copy = false), 1)
end

degree(A::AlgAss) = dim(A)

elem_type(::Type{AlgAss{T}}) where {T} = AlgAssElem{T, AlgAss{T}}

order_type(::AlgAss{fmpq}) = AlgAssAbsOrd{AlgAss{fmpq}, elem_type(AlgAss{fmpq})}
order_type(::Type{AlgAss{fmpq}}) = AlgAssAbsOrd{AlgAss{fmpq}, elem_type(AlgAss{fmpq})}

order_type(::AlgAss{T}) where { T <: NumFieldElem } = AlgAssRelOrd{T, fractional_ideal_type(order_type(parent_type(T)))}
order_type(::Type{AlgAss{T}}) where { T <: NumFieldElem } = AlgAssRelOrd{T, fractional_ideal_type(order_type(parent_type(T)))}

@doc Markdown.doc"""
    multiplication_table(A::AlgAss; copy::Bool = true) -> Array{RingElem, 3}

> Given an algebra $A$ this function returns the multiplication table of $A$:
> If the function returns $M$ and the basis of $A$ is $e_1,\dots, e_n$ then
> it holds $e_i \cdot e_j = \sum_k M[i, j, k] \cdot e_k$.
"""
function multiplication_table(A::AlgAss; copy::Bool = true)
  @assert !iszero(A)
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

iscommutative_known(A::AlgAss) = (A.iscommutative != 0)

@doc Markdown.doc"""
    iscommutative(A::AlgAss) -> Bool

> Returns `true` if $A$ is a commutative ring and `false` otherwise.
"""
function iscommutative(A::AlgAss)
  if iscommutative_known(A)
    return A.iscommutative == 1
  end
  for i = 1:dim(A)
    for j = i + 1:dim(A)
      if multiplication_table(A, copy = false)[i, j, :] != multiplication_table(A, copy = false)[j, i, :]
        A.iscommutative = 2
        return false
      end
    end
  end
  A.iscommutative = 1
  return true
end

################################################################################
#
#  Construction
#
################################################################################

# This only works if base_ring(A) is a field (probably)
# Returns (true, one) if there is a one and (false, something) if not.
function find_one(A::AlgAss)
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
    return false, zeros(A, n)
  end
  if n != 1 && !iszero(Mc[n + 1, n + 1])
    return false, zeros(A, n)
  end
  cc = solve_ut(sub(Mc, 1:n, 1:n), sub(Mc, 1:n, (n + 1):(n + 1)))
  one = [ cc[i, 1] for i = 1:n ]
  return true, one
end

function _zero_algebra(R::Ring)
  A = AlgAss{elem_type(R)}(R)
  A.iszero = true
  A.iscommutative = 1
  A.has_one = true
  A.one = elem_type(R)[]
  return A
end

function AlgAss(R::Ring, mult_table::Array{T, 3}, one::Array{T, 1}) where {T}
  if size(mult_table, 1) == 0
    return _zero_algebra(R)
  end
  return AlgAss{T}(R, mult_table, one)
end

function AlgAss(R::Ring, mult_table::Array{T, 3}) where {T}
  if size(mult_table, 1) == 0
    return _zero_algebra(R)
  end
  A = AlgAss{T}(R)
  A.mult_table = mult_table
  A.iszero = false
  has_one, one = find_one(A)
  A.has_one = has_one
  if has_one
    A.one = one
  end
  return A
end

function AlgAss(R::Ring, d::Int, arr::Array{T, 1}) where {T}
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
  return AlgAss(R, mult_table)
end

# Constructs the algebra R[X]/f
function AlgAss(f::PolyElem)
  R = base_ring(parent(f))
  n = degree(f)
  Rx = parent(f)
  x = gen(Rx)
  B = Array{elem_type(Rx), 1}(undef, 2*n - 1)
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
  A = AlgAss(R, mult_table, one)
  A.iscommutative = 1
  return A
end

function AlgAss(K::AnticNumberField)
  A = AlgAss(K.pol)
  m = AbsAlgAssToNfAbsMor(A, K, identity_matrix(FlintQQ, dim(A)), identity_matrix(FlintQQ, dim(A)))
  A.maps_to_numberfields = [ (K, m) ]
  return A, m
end

# Reduces the rows of M in `rows` modulo N in place.
# Assumes that N is in lowerleft HNF.
function reduce_rows_mod_hnf!(M::fmpz_mat, N::fmpz_mat, rows::Vector{Int})
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

@doc Markdown.doc"""
    quo(O::NfAbsOrd, I::NfAbsOrdIdl, p::Union{ Int, fmpz })
    quo(O::AlgAssAbsOrd, I::AlgAssAbsOrdIdl, p::Union{ Int, fmpz })
      -> AlgAss, AbsOrdToAlgAssMor

> Given an ideal $I$ such that $p \cdot O \subseteq I \subseteq O$ this function
> constructs $O/I$ as an algebra over $\mathbb F_p$ together with the projection
> map $O \to O/I$.
> It is assumed that $p$ is prime.
"""
quo(O::Union{NfAbsOrd, AlgAssAbsOrd}, I::Union{NfAbsOrdIdl, AlgAssAbsOrdIdl}, p::Union{Integer, fmpz}) = AlgAss(O, I, p)

function AlgAss(O::Union{NfAbsOrd, AlgAssAbsOrd}, I::Union{NfAbsOrdIdl, AlgAssAbsOrdIdl}, p::Union{Integer, fmpz})
  @assert order(I) === O

  n = degree(O)
  bmatI = integral_basis_matrix_wrt(I, O, copy = false)

  basis_elts = Vector{Int}()
  for i = 1:n
    if iscoprime(bmatI[i, i], p)
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
      function _image_zero(a::Union{ NfAbsOrdElem, AlgAssAbsOrdElem })
        return A()
      end
    end

    local _preimage_zero

    let O = O
      function _preimage_zero(a::AlgAssElem)
        return O()
      end
    end

    OtoA = AbsOrdToAlgAssMor{typeof(O), elem_type(Fp)}(O, A, _image_zero, _preimage_zero)
    return A, OtoA
  end

  BO = basis(O, copy = false)
  mult_table = Array{elem_type(Fp), 3}(undef, r, r, r)
  for i = 1:r
    M = representation_matrix_mod(BO[basis_elts[i]], fmpz(p))
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
    A = AlgAss(Fp, mult_table, one)
  else
    A = AlgAss(Fp, mult_table)
  end
  if iscommutative(O)
    A.iscommutative = 1
  end

  local _image

  let I = I, A = A, basis_elts = basis_elts, Fp = Fp
    function _image(a::Union{NfAbsOrdElem, AlgAssAbsOrdElem})
      c = coordinates(mod(a, I), copy = false)
      return A([ Fp(c[i]) for i in basis_elts ])
    end
  end

  local _preimage

  let BO = BO, basis_elts = basis_elts, r = r
    function _preimage(a::AlgAssElem)
      return sum(lift(coeffs(a, copy = false)[i])*BO[basis_elts[i]] for i = 1:r)
    end
  end

  OtoA = AbsOrdToAlgAssMor{typeof(O), elem_type(Fp)}(O, A, _image, _preimage)

  return A, OtoA
end

# Requires M to be in lower left HNF
function reduce_vector_mod_hnf(v::fmpz_mat, M::fmpz_mat)
  @assert ncols(v) == nrows(M) && nrows(M) == ncols(M)

  w = Vector{fmpz}(undef, length(v))
  t = fmpz()
  for i in length(v):-1:1
    t = fdiv(v[1, i], M[i, i])
    for j in 1:i
      w[j] = v[1, j] - t*M[i, j]
    end
  end
  return w
end

@doc Markdown.doc"""
    quo(I::NfAbsOrdIdl, J::NfAbsOrdIdl, p::Union{ Int, fmpz })
    quo(I::AlgAssAbsOrdIdl, J::AlgAssAbsOrdIdl, p::Union{ Int, fmpz })
      -> AlgAss, AbsOrdToAlgAssMor

> Given an ideal $J$ such that $p \cdot I \subseteq J \subseteq I$ this function
> constructs $I/J$ as an algebra over $\mathbb F_p$ together with the projection
> map $I \to I/J$.
> It is assumed that $p$ is prime.
"""
quo(I::Union{ NfAbsOrdIdl, AlgAssAbsOrdIdl }, J::Union{ NfAbsOrdIdl, AlgAssAbsOrdIdl }, p::Union{ Integer, fmpz }) = AlgAss(I, J, p)

function AlgAss(I::Union{ NfAbsOrdIdl, AlgAssAbsOrdIdl }, J::Union{NfAbsOrdIdl, AlgAssAbsOrdIdl}, p::Union{Integer, fmpz})
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
      function _image_zero(a::Union{ NfAbsOrdElem, AlgAssAbsOrdElem })
        return A()
      end
    end

    local _preimage_zero

    let O = O
      function _preimage_zero(a::AlgAssElem)
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

  A = AlgAss(Fp, mult_table)
  if iscommutative(O)
    A.iscommutative = 1
  end

  t = FakeFmpqMat(zero_matrix(FlintZZ, 1, n))

  local _image

  let BmatJinI = BmatJinI, I = I, r = r, A = A, t = t, Fp = Fp
    function _image(a::Union{NfAbsOrdElem, AlgAssAbsOrdElem})
      elem_to_mat_row!(t.num, 1, t.den, _elem_in_algebra(a, copy = false))
      t = mul!(t, t, basis_mat_inv(I, copy = false))
      @assert isone(t.den) "Not an element of the domain"
      c = reduce_vector_mod_hnf(t.num, BmatJinI)
      return A([ Fp(c[i]) for i in basis_elts ])
    end
  end

  local _preimage

  let BI = BI, basis_elts = basis_elts, r = r
    function _preimage(a::AlgAssElem)
      return O(sum(lift(coeffs(a, copy = false)[i])*BI[basis_elts[i]] for i = 1:r))
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
@doc Markdown.doc"""
    quo(O::NfRelOrd, I::NfRelOrdIdl, p::Union{ NfAbsOrdIdl, NfRelOrdIdl })
    quo(O::AlgAssRelOrd, I::AlgAssRelOrdIdl, p::Union{ NfAbsOrdIdl, NfRelOrdIdl })
      -> AlgAss, RelOrdToAlgAssMor

> Given an ideal $I$ such that $p \cdot O \subseteq I \subseteq O$ this function
> constructs $O/I$ as an algebra over the finite field $R/p$, where $R$ is the
> order of $p$, together with the projection map $O \to O/I$.
> It is assumed that `R == base_ring(O)` and that $p$ is prime.
"""
quo(O::Union{ NfRelOrd{T, S}, AlgAssRelOrd{T, S} }, I::Union{ NfRelOrdIdl{T, S}, AlgAssRelOrdIdl{T, S} }, p::Union{NfOrdIdl, NfRelOrdIdl}) where {T, S} = AlgAss(O, I, p)

function AlgAss(O::Union{ NfRelOrd{T, S}, AlgAssRelOrd{T, S} }, I::Union{ NfRelOrdIdl{T, S}, AlgAssRelOrdIdl{T, S} }, p::Union{NfOrdIdl, NfRelOrdIdl}) where {T, S}

  K = _algebra(O)

  new_basisO, new_basisI, new_bmatO, new_bmatI = coprime_bases(O, I, p)
  new_bmatinvO = inv(new_bmatO)

  Fp, mF = ResidueField(order(p), p)
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
      function _image_zero(a::Union{ NfRelOrdElem, AlgAssRelOrdElem })
        return A()
      end
    end

    local _preimage_zero

    let O = O
      function _preimage_zero(a::AlgAssElem)
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
      tmp_matrix[1, i] = coeffs(c, copy = false)[i]
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
    A = AlgAss(Fp, mult_table, one)
  else
    A = AlgAss(Fp, mult_table)
  end
  if iscommutative(O)
    A.iscommutative = 1
  end

  function _image(a::Union{ NfRelOrdElem, AlgAssRelOrdElem })
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

  lifted_basis_of_A = []

  for i in basis_elts
    c = coprime_to(new_basisO[i][2], p)
    b = invmmF(inv(mmF(c)))*c*new_basisO[i][1]
    @assert b in O
    push!(lifted_basis_of_A, b)
  end

  function _preimage(v::AlgAssElem)
    return O(sum((invmmF(v.coeffs[i]))*lifted_basis_of_A[i] for i in 1:r))
  end

  OtoA = RelOrdToAlgAssMor(O, A, _image, _preimage)

  return A, OtoA
end

@doc Markdown.doc"""
    quo(I::NfRelOrdIdl, J::NfRelOrdIdl, p::Union{ NfAbsOrdIdl, NfRelOrdIdl })
    quo(I::AlgAssRelOrdIdl, J::AlgAssRelOrdIdl, p::Union{ NfAbsOrdIdl, NfRelOrdIdl })
      -> AlgAss, RelOrdToAlgAssMor

> Given an ideal $J$ such that $p \cdot I \subseteq J \subseteq I$ this function
> constructs $I/J$ as an algebra over the finite field $R/p$, where $R$ is the
> order of $p$, together with the projection map $I \to I/J$.
> It is assumed that `order(I) === order(J)` and in particular both should be
> defined. Further, it should hold `R == base_ring(order(I))` and $p$ should be
> prime.
"""
quo(I::Union{ NfRelOrdIdl{T, S}, AlgAssRelOrdIdl{T, S} }, J::Union{ NfRelOrdIdl{T, S}, AlgAssRelOrdIdl{T, S} }, p::Union{NfOrdIdl, NfRelOrdIdl}) where {T, S} = AlgAss(I, J, p)

function AlgAss(I::Union{ NfRelOrdIdl{T, S}, AlgAssRelOrdIdl{T, S} }, J::Union{ NfRelOrdIdl{T, S}, AlgAssRelOrdIdl{T, S} }, p::Union{NfOrdIdl, NfRelOrdIdl}) where {T, S}
  @assert _algebra(I) === _algebra(J)
  @assert order(I) === order(J)

  O = order(I)
  K = _algebra(I)
  new_basisI, new_basisJ, new_bmatI, new_bmatJinI = coprime_bases(I, J, p)
  bmatinvI = inv(new_bmatI)

  Fp, mF = ResidueField(order(p), p)
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
      function _image_zero(a::Union{ NfRelOrdElem, AlgAssRelOrdElem })
        return A()
      end
    end

    local _preimage_zero

    let O = O
      function _preimage_zero(a::AlgAssElem)
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
      tmp_matrix[1, i] = coeffs(c, copy = false)[i]
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
    A = AlgAss(Fp, mult_table, one)
  else
    A = AlgAss(Fp, mult_table)
  end
  if iscommutative(O)
    A.iscommutative = 1
  end

  function _image(a::Union{ NfRelOrdElem, AlgAssRelOrdElem })
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

  lifted_basis_of_A = []

  for i in basis_elts
    c = coprime_to(new_basisI[i][2], p)
    b = invmmF(inv(mmF(c)))*c*new_basisI[i][1]
    @assert O(b) in I
    push!(lifted_basis_of_A, b)
  end

  function _preimage(v::AlgAssElem)
    return O(sum((invmmF(v.coeffs[i])) * lifted_basis_of_A[i] for i in 1:r))
  end

  OtoA = RelOrdToAlgAssMor(O, A, _image, _preimage)

  return A, OtoA
end

function AlgAss(A::Generic.MatAlgebra{T}) where { T <: FieldElem }
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
  A = AlgAss(K, mult_table, oneA)
  A.iscommutative = ( n == 1 ? 1 : 2 )
  return A
end

function AlgAss(A::AlgAss)
  R = base_ring(A)
  d = dim(A)
  return A, hom(A, A, identity_matrix(R, d), identity_matrix(R, d))
end

###############################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::AlgAss)
  print(io, "Associative algebra of dimension ", dim(A), " over ", base_ring(A))
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(A::AlgAss{T}, dict::IdDict) where {T}
  B = AlgAss{T}(base_ring(A))
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
function _build_subalgebra_mult_table!(A::AlgAss{T}, B::MatElem{T}, return_LU::Type{Val{S}} = Val{false}) where { T, S }
  K = base_ring(A)
  n = dim(A)
  r = rref!(B)
  if r == 0
    if return_LU == Val{true}
      return Array{elem_type(K), 3}(undef, 0, 0, 0), SymmetricGroup(ncols(B))(), zero_matrix(K, 0, 0), zero_matrix(K, 0, 0)
    else
      return Array{elem_type(K), 3}(undef, 0, 0, 0)
    end
  end

  basis = Vector{elem_type(A)}(undef, r)
  for i = 1:r
    basis[i] = elem_from_mat_row(A, B, i)
  end

  _, p, L, U = lu(transpose(B))

  mult_table = Array{elem_type(K), 3}(undef, r, r, r)
  c = A()
  d = zero_matrix(K, n, 1)
  for i = 1:r
    for j = 1:r
      if iscommutative(A) && j < i
        continue
      end
      c = mul!(c, basis[i], basis[j])
      for k = 1:n
        d[p[k], 1] = c.coeffs[k]
      end
      d = solve_lt(L, d)
      d = solve_ut(U, d)
      for k = 1:r
        mult_table[i, j, k] = deepcopy(d[k, 1])
        if iscommutative(A) && i != j
          mult_table[j, i, k] = deepcopy(d[k, 1])
        end
      end
    end
  end

  if return_LU == Val{true}
    return mult_table, p, L, U
  else
    return mult_table
  end
end

@doc Markdown.doc"""
     subalgebra(A::AlgAss, e::AlgAssElem, idempotent::Bool = false,
                action::Symbol = :left)
       -> AlgAss, AbsAlgAssMor

> Given an algebra $A$ and an element $e$, this function constructs the algebra
> $e \cdot A$ (if `action == :left`) respectively $A \cdot e$ (if `action == :right`)
> and a map from this algebra to $A$.
> If `idempotent` is `true`, it is assumed that $e$ is idempotent in $A$.
"""
function subalgebra(A::AlgAss{T}, e::AlgAssElem{T, AlgAss{T}}, idempotent::Bool = false, action::Symbol = :left) where {T}
  @assert parent(e) == A
  R = base_ring(A)
  n = dim(A)
  B = representation_matrix(e, action)

  mult_table, p, L, U = _build_subalgebra_mult_table!(A, B, Val{true})
  r = size(mult_table, 1)

  if r == 0
    eA = _zero_algebra(R)
    return eA, hom(eA, A, zero_matrix(R, 0, n))
  end

  # The basis matrix of e*A resp. A*e with respect to A is
  basis_mat_of_eA = sub(B, 1:r, 1:n)

  if idempotent
    c = A()
    d = zero_matrix(R, n, 1)
    for k = 1:n
      d[p[k], 1] = e.coeffs[k]
    end
    d = solve_lt(L, d)
    d = solve_ut(U, d)
    v = Vector{elem_type(R)}(undef, r)
    for i in 1:r
      v[i] = d[i, 1]
    end
    eA = AlgAss(R, mult_table, v)
  else
    eA = AlgAss(R, mult_table)
  end

  if A.iscommutative == 1
    eA.iscommutative = 1
  end

  if idempotent
    # We have the map eA -> A, given by the multiplying with basis_mat_of_eA.
    # But there is also the canonical projection A -> eA, a -> ea.
    # We compute the corresponding matrix.
    B = representation_matrix(e, action)
    C = zero_matrix(R, n, r)
    for i in 1:n
      for k = 1:n
        d[p[k], 1] = B[i, k]
      end
      d = solve_lt(L, d)
      d = solve_ut(U, d)
      for k in 1:r
        C[i, k] = d[k, 1]
      end
    end
    eAtoA = hom(eA, A, basis_mat_of_eA, C)
  else
    eAtoA = hom(eA, A, basis_mat_of_eA)
  end
  return eA, eAtoA
end

@doc Markdown.doc"""
    subalgebra(A::AlgAss, basis::Vector{AlgAssElem}) -> AlgAss, AbsAlgAssMor

> Returns the subalgebra of $A$ generated by the elements in `basis` and a map
> from this algebra to $A$.
"""
function subalgebra(A::AlgAss{T}, basis::Vector{AlgAssElem{T, AlgAss{T}}}) where T
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  for i = 1:length(basis)
    elem_to_mat_row!(M, i, basis[i])
  end
  mt = _build_subalgebra_mult_table!(A, M)
  B = AlgAss(base_ring(A), mt)
  return B, hom(B, A, sub(M, 1:length(basis), 1:dim(A)))
end

###############################################################################
#
#  Trace Matrix
#
###############################################################################

function _assure_trace_basis(A::AlgAss{T}) where T
  if !isdefined(A, :trace_basis_elem)
    A.trace_basis_elem = Array{T, 1}(undef, dim(A))
    for i=1:length(A.trace_basis_elem)
      A.trace_basis_elem[i]=sum(multiplication_table(A, copy = false)[i,j,j] for j= 1:dim(A))
    end
  end
  return nothing
end

@doc Markdown.doc"""
    trace_matrix(A::AlgAss) -> MatElem

> Returns a matrix $M$ over the base ring of $A$ such that
> $M_{i, j} = \mathrm{tr}(b_i \cdot b_j)$, where $b_1, \dots, b_n$ is the
> basis of $A$.
"""
function trace_matrix(A::AlgAss)
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

function _rep_for_center(M::T, A::AlgAss) where T<: MatElem
  n=dim(A)
  for i=1:n
    for j = 1:n
      for k = 1:n
        M[k+(i-1)*n, j] = multiplication_table(A, copy = false)[i, j, k]-multiplication_table(A, copy = false)[j, i, k]
      end
    end
  end
  return nothing
end

@doc Markdown.doc"""
    center(A::AlgAss) -> AlgAss, AbsAlgAssMor

> Returns the center $C$ of $A$ and the inclusion $C \to A$.
"""
function center(A::AlgAss{T}) where {T}
  if iscommutative(A)
    B, mB = AlgAss(A)
    return B, mB
  end
  if isdefined(A, :center)
    return A.center::Tuple{AlgAss{T}, morphism_type(AlgAss{T}, AlgAss{T})}
  end
  n=dim(A)
  M=zero_matrix(base_ring(A), n^2, n)
  # I concatenate the difference between the right and left representation matrices.
  _rep_for_center(M,A)
  k,B=nullspace(M)
  res=Array{elem_type(A),1}(undef, k)
  for i=1:k
    res[i]= A(T[B[j,i] for j=1:n])
  end
  C, mC = subalgebra(A, res)
  A.center = C, mC
  return C, mC
end

################################################################################
#
#  Change of ring
#
################################################################################

@doc Markdown.doc"""
    restrict_scalars(A::AlgAss{nf_elem}, Q::FlintRationalField)
    restrict_scalars(A::AlgAss{fq_nmod}, Fp::GaloisField)
    restrict_scalars(A::AlgAss{fq}, Fp::Generic.ResField{fmpz})
      -> AlgAss, Function, Function

> Given an algebra $A$ over a field $L$ and the prime field $K$ of $L$, this
> function returns the restriction $B$ of $A$ to $K$ and maps from $A$ to $B$
> and from $B$ to $A$.
"""
# Top level functions to avoid "type mix-ups" (like AlgAss{fq_nmod} with FlintQQ)
function restrict_scalars(A::AlgAss{nf_elem}, Q::FlintRationalField)
  return _restrict_scalars_to_prime_field(A, Q)
end

function restrict_scalars(A::AlgAss{fq_nmod}, Fp::GaloisField)
  return _restrict_scalars_to_prime_field(A, Fp)
end

function restrict_scalars(A::AlgAss{fq}, Fp::Generic.ResField{fmpz})
  return _restrict_scalars_to_prime_field(A, Fp)
end

if Nemo.version() > v"0.15.1"
  function restrict_scalars(A::AlgAss{fq}, Fp::Nemo.GaloisFmpzField)
    return _restrict_scalars_to_prime_field(A, Fp)
  end
end

function restrict_scalars(A::AlgAss{gfp_elem}, Fp::GaloisField)
  function AtoA(x::AlgAssElem)
    return x
  end
  return A, AtoA, AtoA
end

function restrict_scalars(A::AlgAss{Generic.ResF{fmpz}}, Fp::Generic.ResField{fmpz})
  function AtoA(x::AlgAssElem)
    return x
  end
  return A, AtoA, AtoA
end

if Nemo.version() > v"0.15.1"
  function restrict_scalars(A::AlgAss{Nemo.gfp_fmpz_elem}, Fp::Nemo.GaloisFmpzField)
    function AtoA(x::AlgAssElem)
      return x
    end
    return A, AtoA, AtoA
  end

  function (R::FqFiniteField)(x::Nemo.gfp_fmpz_elem)
    return R(lift(x))
  end

  function *(a::Nemo.fq, b::Nemo.gfp_fmpz_elem)
    return a * parent(a)(b)
  end

  function *(a::Nemo.gfp_fmpz_elem, b::Nemo.fq)
    return parent(b)(a) * b
  end
end


#function _restrict_scalars_to_prime_field(A::AlgAss{T}, prime_field::Union{FlintRationalField, GaloisField, Generic.ResField{fmpz}}) where { T <: Union{nf_elem, fq_nmod, fq} }
# TODO: fix the type
function _restrict_scalars_to_prime_field(A::AlgAss{T}, prime_field) where { T }
  K = base_ring(A)
  n = dim(A)
  m = degree(K)
  nm = n*m
  a = gen(K)
  # We use A[1], a*A[1], ..., a^{m - 1}*A[1], ..., A[n], ..., a^{m - 1}*A[n] as
  # the basis for A over the prime field.
  # Precompute the powers a^k:
  powers_of_a = zeros(K, 2*m - 1)
  powers_of_a[1] = one(K)
  for k = 2:2*m - 1
    powers_of_a[k] = mul!(powers_of_a[k], powers_of_a[k - 1], a)
  end

  function _new_coeffs(x)
    y = Vector{elem_type(prime_field)}(undef, nm)
    yy = coeffs(x, copy = false)
    for i = 1:n
      for j = 1:m
        if prime_field == FlintQQ
          y[(i - 1)*m + j] = coeff(yy[i], j - 1)
        else
          y[(i - 1)*m + j] = prime_field(coeff(yy[i], j - 1))
        end
      end
    end
    return y
  end

  m1 = m - 1
  mult_table = zeros(prime_field, nm, nm, nm)
  Aij = A()
  t = A()
  for i = 1:n
    for j = 1:n
      Aij = mul!(Aij, A[i], A[j])
      if iszero(Aij)
        continue
      end

      mi = m*(i - 1)
      mj = m*(j - 1)
      for s = 0:2*m1 # all possible sums of exponents for a
        t = mul!(t, powers_of_a[s + 1], Aij)
        tcoeffs = _new_coeffs(t)
        for k = max(0, s - m1):min(s, m1)
          mult_table[mi + k + 1, mj + s - k + 1, :] = tcoeffs
        end
      end
    end
  end
  B = AlgAss(prime_field, mult_table, _new_coeffs(one(A)))
  B.iscommutative = A.iscommutative

  function AtoB(x)
    @assert parent(x) == A
    return B(_new_coeffs(x))
  end

  function BtoA(x)
    @assert parent(x) == B
    if prime_field == FlintQQ
      R = parent(K.pol)
    else
      R, z = PolynomialRing(prime_field, "z", cached = false)
    end
    y = Vector{elem_type(K)}(undef, n)
    xcoeffs = coeffs(x) # a copy
    for i = 1:n
      y[i] = K(R(xcoeffs[(i - 1)*m + 1:(i - 1)*m + m]))
    end
    return A(y)
  end

  return B, AtoB, BtoA
end

@doc Markdown.doc"""
    restrict_scalars(A::AlgAss{nf_elem}, KtoL::NfToNfMor)
      -> AlgAss, Function, Function

> Given an algebra $A$ over a number field $L$ and an inclusion map `KtoL` from
> a number field $K$ to $L$, this function returns the restriction $B$ of $A$
> to $K$ and maps from $A$ to $B$ and from $B$ to $A$.
"""
function restrict_scalars(A::AlgAss{nf_elem}, KtoL::NfToNfMor)
  K = domain(KtoL)
  L = codomain(KtoL)
  @assert L == base_ring(A)
  n = dim(A)
  m = div(degree(L), degree(K))
  nm = n*m
  a = gen(L)
  powers_of_a = zeros(L, 2*m - 1)
  powers_of_a[1] = one(L)
  for k = 2:2*m - 1
    powers_of_a[k] = mul!(powers_of_a[k], powers_of_a[k - 1], a)
  end

  basisK = basis(K)
  basisKinL = map(KtoL, basisK)
  M = zero_matrix(FlintQQ, degree(L), degree(L))
  t = L()
  for i = 1:m
    for j = 1:degree(K)
      t = mul!(t, basisKinL[j], powers_of_a[i])
      for k = 1:degree(L)
        M[k, (i - 1)*m + j] = coeff(t, k - 1)
      end
    end
  end
  M = inv(M)

  function _new_coeffs(x)
    y = zeros(K, nm)
    yy = coeffs(x, copy = false)
    for i = 1:n
      c = matrix(FlintQQ, degree(L), 1, [ coeff(yy[i], j) for j = 0:degree(L) - 1 ])
      Mc = M*c
      for j = 1:m
        for k = 1:degree(K)
          y[(i - 1)*m + j] += Mc[(j - 1)*degree(K) + k, 1]*basisK[k]
        end
      end
    end
    return y
  end

  m1 = m - 1
  mult_table = zeros(K, nm, nm, nm)
  Aij = A()
  t = A()
  for i = 1:n
    for j = 1:n
      Aij = mul!(Aij, A[i], A[j])
      if iszero(Aij)
        continue
      end

      mi = m*(i - 1)
      mj = m*(j - 1)
      for s = 0:2*m1 # all possible sums of exponents for a
        t = mul!(t, powers_of_a[s + 1], Aij)
        tcoeffs = _new_coeffs(t)
        for k = max(0, s - m1):min(s, m1)
          mult_table[mi + k + 1, mj + s - k + 1, :] = tcoeffs
        end
      end
    end
  end
  B = AlgAss(K, mult_table, _new_coeffs(one(A)))
  B.iscommutative = A.iscommutative

  function AtoB(x)
    @assert parent(x) == A
    return B(_new_coeffs(x))
  end

  function BtoA(x)
    @assert parent(x) == B
    y = zeros(L, n)
    xcoeffs = coeffs(x)
    for i = 1:n
      xx = map(KtoL, xcoeffs[(i - 1)*m + 1:(i - 1)*m + m])
      for j = 1:m
        y[i] += xx[j]*powers_of_a[j]
      end
    end
    return A(y)
  end

  return B, AtoB, BtoA
end

# TODO: Fix the types
function _as_algebra_over_center(A::AlgAss{T}) where { T } #<: Union{fmpq, gfp_elem, Generic.ResF{fmpz}, fq, fq_nmod} }
  @assert !iszero(A)

  K = base_ring(A)
  C, CtoA = center(A)

  isfq = ( T === fq_nmod || T === fq )
  iscentral = ( dim(C) == 1 )

  if iscentral && isfq
    function AtoA(x::AlgAssElem)
      return x
    end
    return A, AtoA, AtoA
  end

  if T === fmpq || T === nf_elem
    fields = as_number_fields(C)
    @assert length(fields) == 1
    L, CtoL = fields[1]
  else
    L, CtoL = _as_field_with_isomorphism(C)
  end

  if iscentral
    mult_table_B = Array{elem_type(L), 3}(undef, dim(A), dim(A), dim(A))
    for i = 1:dim(A)
      for j = 1:dim(A)
        for k = 1:dim(A)
          mult_table_B[i, j, k] = L(multiplication_table(A, copy = false)[i, j, k])
        end
      end
    end
    if has_one(A)
      B = AlgAss(L, mult_table_B, map(L, A.one))
    else
      B = AlgAss(L, mult_table_B)
    end

    function AtoB(x::AlgAssElem)
      return B(map(L, coeffs(x, copy = false)))
    end

    function BtoA(x::AlgAssElem)
      return A([ K(coeff(c, 0)) for c in coeffs(x, copy = false) ])
    end
    return B, AtoB, BtoA
  end

  basisC = basis(C)
  basisCinA = Vector{elem_type(A)}(undef, dim(C))
  basisCinL = Vector{elem_type(L)}(undef, dim(C))
  for i = 1:dim(C)
    basisCinA[i] = CtoA(basisC[i])
    basisCinL[i] = CtoL(basisC[i])
  end

  # We construct a basis of A over C (respectively L) by using the following fact:
  # A subset M of basis(A) is a C-basis of A if and only if |M| = dim(A)/dim(C)
  # and all possible products of elements of M and basisCinA form a K-basis of A,
  # with K := base_ring(A).
  AoverK = basis(A)
  AoverC = Vector{Int}()
  M = zero_matrix(K, dim(C), dim(A))
  MM = zero_matrix(K, 0, dim(A))
  r = 0
  for i = 1:dim(A)
    b = AoverK[i]

    for j = 1:dim(C)
      elem_to_mat_row!(M, j, b*basisCinA[j])
    end

    N = vcat(MM, M)
    s = rank(N)
    if s > r
      push!(AoverC, i)
      MM = N
      r = s
    end
    if r == dim(A)
      break
    end
  end

  m = div(dim(A), dim(C))

  @assert length(AoverC) == m
  @assert nrows(MM) == dim(A)

  iMM = inv(MM)

  local _new_coeffs
  let L = L, K = K, iMM = iMM, basisCinL = basisCinL, C = C, m = m, isfq = isfq
    _new_coeffs = x -> begin
      y = zeros(L, m)
      xx = matrix(K, 1, dim(A), coeffs(x, copy = false))
      Mx = xx*iMM
      for i = 1:m
        for j = 1:dim(C)
          if isfq
            t = CtoL.RtoFq(CtoL.R(Mx[1, (i - 1)*dim(C) + j]))
            y[i] = addeq!(y[i], basisCinL[j]*t)
          else
            y[i] = addeq!(y[i], basisCinL[j]*Mx[1, (i - 1)*dim(C) + j])
          end
        end
      end
      return y
    end
  end

  mult_table = zeros(L, m, m, m)
  Aij = A()
  for i = 1:m
    for j = 1:m
      Aij = mul!(Aij, A[AoverC[i]], A[AoverC[j]])
      if iszero(Aij)
        continue
      end

      mult_table[i, j, :] = _new_coeffs(Aij)
    end
  end

  B = AlgAss(L, mult_table, _new_coeffs(one(A)))
  B.iscommutative = A.iscommutative

  local AtoB
  let B = B, _new_coeffs = _new_coeffs
    AtoB = x -> begin
      @assert parent(x) == A
      return B(_new_coeffs(x))
    end
  end

  local BtoA
  let K = K, MM = MM, CtoA = CtoA, CtoL = CtoL, AoverC = AoverC, B = B, m = m
    BtoA = x -> begin
      @assert parent(x) == B
      y = zeros(K, dim(A))
      xx = A()
      for i = 1:dim(B)
        t = CtoA(CtoL\coeffs(x, copy = false)[i])
        xx = add!(xx, xx, t*A[AoverC[i]])
      end
      return xx
    end
  end

  return B, AtoB, BtoA
end

################################################################################
#
#  Idempotents
#
################################################################################

# See W. Eberly "Computations for Algebras and Group Representations" p. 126.
# TODO: fix the type
function _find_non_trivial_idempotent(A::AlgAss{T}) where { T } #<: Union{gfp_elem, Generic.ResF{fmpz}, fq, fq_nmod} }
  if dim(A) == 1
    error("Dimension of algebra is 1")
  end
  while true
    a = rand(A)
    if isone(a) || iszero(a)
      continue
    end
    mina = minpoly(a)
    if isirreducible(mina)
      if degree(mina) == dim(A)
        error("Algebra is a field")
      end
      continue
    end
    if issquarefree(mina)
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

#function _find_idempotent_via_non_squarefree_poly(A::AlgAss{T}, a::AlgAssElem{T}, mina::Union{gfp_poly, gfp_fmpz_poly, fq_poly, fq_nmod_poly}) where { T <: Union{gfp_elem, Generic.ResF{fmpz}, fq, fq_nmod} }
function _find_idempotent_via_non_squarefree_poly(A::AlgAss{T}, a::AlgAssElem{T}, mina) where {T}
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
    N = vcat(N, matrix(base_ring(A), dim(bA), 1, coeffs(bA[i])))
  end
  MN = hcat(transpose(M), N)
  r = rref!(MN)
  be = solve_ut(sub(MN, 1:r, 1:dim(bA)), sub(MN, 1:r, (dim(bA) + 1):(dim(bA) + 1)))
  e = bAtoA(bA([ be[i, 1] for i = 1:dim(bA) ]))
  return e
end

# A should be semi-simple
# See W. Eberly "Computations for Algebras and Group Representations" p. 89.
function _extraction_of_idempotents(A::AlgAss, only_one::Bool = false)
  Z, ZtoA = center(A)
  if dim(Z) == 1
    error("Dimension of centre is 1")
  end

  a = ZtoA(rand(Z))
  f = minpoly(a)
  while isirreducible(f)
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

#function _find_idempotent_via_squarefree_poly(A::AlgAss{T}, a::AlgAssElem{T}, mina::Union{gfp_poly, gfp_fmpz_poly, fq_poly, fq_nmod_poly}) where { T <: Union{gfp_elem, Generic.ResF{fmpz}, fq, fq_nmod} }
# TODO: fix the type
function _find_idempotent_via_squarefree_poly(A::AlgAss{T}, a::AlgAssElem{T}, mina) where {T}
  B = AlgAss(mina)
  idemB = _extraction_of_idempotents(B, true)

  e = dot(coeffs(idemB, copy = false), [ a^k for k = 0:(degree(mina) - 1) ])
  return e
end

# TODO: fix the type
function _primitive_idempotents(A::AlgAss{T}) where { T } #<: Union{gfp_elem, Generic.ResF{fmpz}, fq, fq_nmod} }
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
function _matrix_basis(A::AlgAss{T}, idempotents::Vector{S}) where { T, S }#<: Union{gfp_elem, Generic.ResF{fmpz}, fq, fq_nmod}, S <: AlgAssElem{T, AlgAss{T}} }
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
    xx = eAe(left_kernel_basis(M)[1])
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
    NN = vcat(NN, matrix(base_ring(A), dim(eAe), 1, coeffs(bb)))
    NN = vcat(NN, matrix(base_ring(A), dim(eAe), 1, coeffs(aa)))
    b, yy = can_solve(transpose(N), NN)
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
function _as_matrix_algebra(A::AlgAss{T}) where { T } # <: Union{gfp_elem, Generic.ResF{fmpz}, fq, fq_nmod}, S <: AlgAssElem{T, AlgAss{T}} }

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
#  Schur Index at real place
#
################################################################################

function trace_signature(A::AlgAss, P::InfPlc)
  M = trred_matrix(basis(A))
  Ky, y = PolynomialRing(base_ring(A), "y", cached = false)
  f = charpoly(Ky, M)
  npos = number_positive_roots(f, P)
  return (npos, degree(f) - npos)
end

function trace_signature(A::AlgAss{fmpq})
  M = trred_matrix(basis(A))
  Ky, y = PolynomialRing(base_ring(A), "y", cached = false)
  f = charpoly(Ky, M)
  Zx = Globals.Zx
  d = denominator(f)
  npos = number_positive_roots(change_base_ring(FlintZZ, d * f))
  return (npos, degree(f) - npos)
end

function schur_index_at_real_plc(A::AlgAss{fmpq})
  if dim(A) % 4 != 0
    return 1
  end
  x = trace_signature(A)
  n = root(dim(A),2)
  if x[1] == divexact(n*(n+1),2)
    return 1
  else
    return 2
  end
end

function schur_index_at_real_plc(A::AlgAss, P::InfPlc)
  if dim(A) % 4 != 0
    return 1
  end
  x = trace_signature(A, P)
  n = root(dim(A),2)
  if x[1] == divexact(n*(n+1),2)
    return 1
  else
    return 2
  end
end

################################################################################
#
#  Is split
#
################################################################################

@doc Markdown.doc"""
    issplit(A::AlgAss{fmpq}) -> Bool

> Given a $\mathbb Q$-algebra $A$, this function returns `true` if $A$ splits
> over $\mathbb Q$ and `false` otherwise.
"""
function issplit(A::AlgAss{fmpq})
  O = Order(A, basis(A))
  i = schur_index_at_real_plc(O)
  if i==2
    @vprint :AlgAssOrd 1 "Not split at the infinite prime\n"
    return false
  end
  fac = factor(root(abs(discriminant(O)),2))
  for (p,j) in fac
    O1 = pmaximal_overorder(O, Int(p))
    if valuation(discriminant(O1), Int(p)) != 0
      @vprint :AlgAssOrd 1 "Not split at $p\n"
      return false
    end
  end
  return true
end

function issplit(A::AlgAss, P::InfPlc)
  if iscomplex(P)
    return true
  end
  return schur_index_at_real_plc(A, P) == 1
end

################################################################################
#
#  Eichler condition
#
################################################################################

function ramified_infinite_places(A::AlgAss{nf_elem})
  K = base_ring(A)
  inf_plc = Vector{InfPlc}()
  places = real_places(K)
  for p in places
    if !issplit(A, p)
      push!(inf_plc, p)
    end
  end

  return inf_plc
end

# Tests whether A fulfils the Eichler condition relative to the maximal Z-order
# of base_ring(A)
function iseichler(A::AlgAss{nf_elem})
  @assert issimple(A)
  @assert iscentral(A)
  if dim(A) != 4
    return true
  end
  K = base_ring(A)
  places = real_places(K)
  for p in places
    if issplit(A, p)
      return true
    end
  end
  return false
end

function iseichler(A::AlgAss{fmpq})
  @assert issimple(A)
  @assert iscentral(A)
  if dim(A) != 4
    return true
  end
  O = Order(A, basis(A))
  return schur_index_at_real_plc(O) == 1
end

################################################################################
#
#  Direct product
#
################################################################################

@doc Markdown.doc"""
    direct_product(algebras::AlgAss...; task::Symbol = :sum)
      -> AlgAss, Vector{AbsAlgAssMor}, Vector{AbsAlgAssMor}
    direct_product(algebras::Vector{AlgAss}; task::Symbol = :sum)
      -> AlgAss, Vector{AbsAlgAssMor}, Vector{AbsAlgAssMor}

> Returns the algebra $A = A_1 \times \cdots \times A_k$. `task` can be
> ":sum", ":prod", ":both" or ":none" and determines which canonical maps
> are computed as well: ":sum" for the injections, ":prod" for the projections.
"""
function direct_product(algebras::Vector{ <: AlgAss{T} }; task::Symbol = :sum) where T
  return direct_product(algebras..., task = task)
end

function direct_product(algebras::AlgAss{T}...; task::Symbol = :sum) where T
  @assert !isempty(algebras)
  @assert all( A -> base_ring(A) == base_ring(algebras[1]), algebras)
  @assert task in [ :prod, :sum, :both, :none ]

  d = sum( dim(A) for A in algebras )
  mt = zeros(base_ring(algebras[1]), d, d, d)
  offset = 0
  for B in algebras
    dd = dim(B)
    mtB = multiplication_table(B)
    for i = 1:dd
      for j = 1:dd
        for k = 1:dd
          mt[i + offset, j + offset, k + offset] = multiplication_table(B)[i, j, k]
        end
      end
    end
    offset += dd
  end
  A = AlgAss(base_ring(algebras[1]), mt)
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

@doc Markdown.doc"""
    direct_product(fields::AnticNumberFields...)
      -> AlgAss{fmpq}, Vector{AbsAlgAssToNfAbsMor}
    direct_product(fields::Vector{AnticNumberFields})
      -> AlgAss{fmpq}, Vector{AbsAlgAssToNfAbsMor}

> Returns the algebra $A = K_1 \times \cdots \times K_k$ and the projection
> maps $A ->> K_i$.
"""
function direct_product(fields::Vector{AnticNumberField})
  return direct_product(fields...)
end

function direct_product(fields::AnticNumberField...)
  algebras = [ AlgAss(K) for K in fields ]
  A, proj, inj = direct_product([ B for (B, m) in algebras ], task = :both)
  A.decomposition = [ (algebras[i][1], inj[i]) for i = 1:length(algebras) ]
  maps_to_fields = Vector{AbsAlgAssToNfAbsMor}(undef, length(fields))
  for i = 1:length(fields)
    # Assumes, that the map algebras[i] -> K is given by the identity matrix
    maps_to_fields[i] = AbsAlgAssToNfAbsMor(A, fields[i], proj[i].mat, proj[i].imat)
  end
  A.maps_to_numberfields = [ (fields[i], maps_to_fields[i]) for i = 1:length(fields) ]
  return A, maps_to_fields
end

################################################################################
#
#  Quaternion algebras
#
################################################################################

function quaternion_algebra(K::Field, a::T, b::T) where { T <: FieldElem }

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

  return AlgAss(K, M, [ one(K), zero(K), zero(K), zero(K) ])
end

quaternion_algebra(K::Field, a::Int, b::Int) = quaternion_algebra(K, K(a), K(b))

quaternion_algebra(a::Int, b::Int) = quaternion_algebra(FlintQQ, fmpq(a), fmpq(b))
