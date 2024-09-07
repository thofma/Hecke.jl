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
    A = zero_algebra(Fp)

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

  temp = zero(O)

  let BO = BO, basis_elts = basis_elts, r = r, temp = temp
    function _preimage(a::AssociativeAlgebraElem)
      z = zero(O)::eltype(BO)
      ca = coefficients(a, copy = false)
      for i in 1:r
        l = lift(ZZ, ca[i])
        addmul!(z, l, BO[basis_elts[i]], temp)
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
  Oalgebra = _algebra(O)

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
    A = zero_algebra(Fp)

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

  temppp = zero(Oalgebra)

  let BI = BI, basis_elts = basis_elts, r = r, Oalgebra = Oalgebra, temppp = temppp
    function _preimage(a::AssociativeAlgebraElem)
      acoords = map(x -> QQ(lift(ZZ, x)), coefficients(a, copy = false))
      z = zero(Oalgebra)
      for i in 1:r
        if is_zero(acoords[i])
          continue
        end
        temppp = mul!(temppp, acoords[i], BI[basis_elts[i]])
        z = add!(z, z, temppp)
      end
      _zz = O(z)
      return _zz
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
    A = zero_algebra(Fp)

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
    A = zero_algebra(Fp)

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
