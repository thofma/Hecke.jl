###############################################################################
#
#  ICM / is_isomorphic_with_map
#
###############################################################################

# Stefano Marseglia "Computing the ideal class monoid of an order"
@doc raw"""
    ideal_class_monoid(R::AbsNumFieldOrder)
      -> Vector{FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}}
    ideal_class_monoid(R::AlgAssAbsOrd)
      -> Vector{FacElem{AlgAssAbsOrdIdl, AlgAssAbsOrdIdlSet}}

Given an order $R$ in a number field or a finite product of number fields, this
function returns representatives of the isomorphism classes of fractional
ideals in $R$.
"""
function ideal_class_monoid(R::T) where { T <: Union{ AbsNumFieldOrder, AlgAssAbsOrd } }
  @assert is_commutative(R)
  orders = overorders(R)
  result = Vector{FacElem{fractional_ideal_type(R)}}()
  for S in orders
    append!(result, _icm_bar(R, S))
  end
  return result
end

# Stefano Marseglia "Computing the ideal class monoid of an order", Prop. 4.1
@doc raw"""
    is_locally_isomorphic(I::AbsNumFieldOrderIdeal, J::AbsNumFieldOrderIdeal) -> Bool
    is_locally_isomorphic(I::NfFracOrdIdl, J::NfFracOrdIdl) -> Bool
    is_locally_isomorphic(I::AlgAssAbsOrdIdl, J::AlgAssAbsOrdIdl) -> Bool

Given two (fractional) ideals $I$ and $J$ of an order $R$ of an $Q$-étale
algebra, this function returns `true` if $I_p$ and $J_p$ are isomorphic for
all primes $p$ of $R$ and `false` otherwise.
"""
function is_locally_isomorphic(I::T, J::T) where { T <: Union{ AbsNumFieldOrderIdeal, AbsSimpleNumFieldOrderFractionalIdeal, AlgAssAbsOrdIdl } }
  IJ = colon(I, J)
  JI = colon(J, I)
  return one(_algebra(order(I))) in IJ*JI
end

# Stefano Marseglia "Computing the ideal class monoid of an order", Cor. 4.5
@doc raw"""
    is_isomorphic_with_map(I::AbsNumFieldOrderIdeal, J::AbsNumFieldOrderIdeal) -> Bool, AbsSimpleNumFieldElem
    is_isomorphic_with_map(I::NfFracOrdIdl, J::NfFracOrdIdl) -> Bool, AbsSimpleNumFieldElem
    is_isomorphic_with_map(I::AlgAssAbsOrdIdl, J::AlgAssAbsOrdIdl) -> Bool, AbstractAssociativeAlgebraElem

Given two (fractional) ideals $I$ and $J$ of an order $R$ of an $Q$-étale
algebra $A$, this function returns `true` and an element $a \in A$ such that
$I = aJ$ if such an element exists and `false` and $0$ otherwise.
"""
function is_isomorphic_with_map(I::T, J::T) where { T <: Union{ AbsNumFieldOrderIdeal, AbsSimpleNumFieldOrderFractionalIdeal, AlgAssAbsOrdIdl}}
  A = _algebra(order(I))
  if !is_locally_isomorphic(I, J)
    return false, zero(A)
  end

  S = ring_of_multipliers(I)
  IS = extend(I, S)
  JS = extend(J, S)
  IJ = colon(IS, JS)
  IJ.order = S
  t, a = is_principal_with_data(numerator(IJ, copy = false))
  if !t
    return false, zero(A)
  end

  return true, divexact(_elem_in_algebra(a, copy = false), A(denominator(IJ, copy = false)))
end

@doc raw"""
    is_isomorphic(I::AbsNumFieldOrderIdeal, J::AbsNumFieldOrderIdeal) -> Bool, AbsSimpleNumFieldElem
    is_isomorphic(I::NfFracOrdIdl, J::NfFracOrdIdl) -> Bool, AbsSimpleNumFieldElem
    is_isomorphic(I::AlgAssAbsOrdIdl, J::AlgAssAbsOrdIdl) -> Bool, AbstractAssociativeAlgebraElem

Given two (fractional) ideals $I$ and $J$ of an order $R$ of an $Q$-étale
algebra $A$, this function returns `true` if an element $a \in A$ exists such that
$I = aJ$ and `false` otherwise.
"""
function is_isomorphic(I::T, J::T) where { T <: Union{ AbsNumFieldOrderIdeal, AbsSimpleNumFieldOrderFractionalIdeal, AlgAssAbsOrdIdl}}
  return is_isomorphic_with_map(I, J)[1]
end

function ring_of_multipliers(I::AbsSimpleNumFieldOrderFractionalIdeal)
  return ring_of_multipliers(numerator(I, copy = false))
end

###############################################################################
#
#  Internals
#
###############################################################################

# Computes representatives of the weak equivalence classes of fractional ideals
# of R with ring of multipliers S.
# Algorithm 2 in Marseglia: "Computing the ideal class monoid of an order"
function _wicm_bar(R::T, S::T) where { T <: Union{ AbsNumFieldOrder, AlgAssAbsOrd } }
  K = _algebra(S)
  oneS = one(K)*S
  St = trace_dual(S)
  reps = Vector{fractional_ideal_type(R)}()
  I = St*colon(oneS, St)
  if one(K) in I
    push!(reps, _as_fractional_ideal_of_smaller_order(R, oneS))
    return reps
  end

  orders = overorders(S)
  for O in orders
    if O == S
      continue
    end

    StO = St*O
    if !(one(K) in StO*colon(one(K)*O, StO))
      continue
    end
    f = conductor(S, O)
    fO = f*O

    ideals = ideals_containing(O, fO, S)
    for I in ideals
      if colon(I, I) != oneS
        continue
      end
      I = _as_fractional_ideal_of_smaller_order(R, I)
      new_class = true
      for J in reps
        if is_locally_isomorphic(I, J)
          new_class = false
          break
        end
      end
      if new_class
        push!(reps, I)
      end
    end
    break # We only need to do this with one over-order
  end
  return reps
end

# Computes the fractional ideals I in ICM(R) with (I:I) = S
# Part of Algorithm 3 in Marseglia: "Computing the ideal class monoid of an order"
function _icm_bar(R::T, S::T) where { T <: Union{ AbsNumFieldOrder, AlgAssAbsOrd } }
  ideals = _wicm_bar(R, S)
  P, mP = picard_group(S)
  fac_elem_mon = FacElemMon(FracIdealSet(R))
  result = Vector{elem_type(fac_elem_mon)}()
  gens_of_P = [ _as_fractional_ideal_of_smaller_order(R, mP(P[i])) for i = 1:ngens(P) ]
  last_p = P()
  for (i, p) in enumerate(P)
    fac_elem = fac_elem_mon()
    for j = 1:ngens(P)
      if p.coeff[1, j] == last_p.coeff[1, j]
        # Avoid some dictionary operations
        continue
      end
      if iszero(p.coeff[1, j])
        continue
      end

      fac_elem.fac[gens_of_P[j]] = p.coeff[1, j]
    end
    last_p = p
    for I in ideals
      fac_elem2 = copy(fac_elem)
      if haskey(fac_elem2.fac, I)
        fac_elem2.fac[I] += ZZRingElem(1)
      else
        fac_elem2.fac[I] = ZZRingElem(1)
      end
      push!(result, fac_elem2)
    end
  end
  return result
end

# Computes all subgroups of S/a as fractional ideals of R.
function ideals_containing(S::T, a::T2, R::T) where { T <: Union{ AbsNumFieldOrder, AlgAssAbsOrd }, T2 <: Union{ AbsNumFieldOrderIdeal, AlgAssAbsOrdIdl } }
  Q, mQ = quo(S, a, FinGenAbGroup)
  if order(Q) == 1
    return [ a ]
  end

  K = _algebra(S)
  d = degree(S)

  potential_basis = Vector{elem_type(_algebra(S))}(undef, d)
  ideals = fractional_ideal_type(R)[]

  for i = 1:mQ.offset
    potential_basis[i] = mQ.bottom_snf_basis[i]
  end

  offset = mQ.offset
  subs = subgroups(Q)

  function group_to_ideal(s::Tuple{FinGenAbGroup, FinGenAbGroupHom})
    H, HtoQ = image(s[2], false)
    for i = 1:(d - offset)
      v = HtoQ(H[i]).coeff
      if iszero(v)
        potential_basis[i + offset] = mQ.bottom_snf_basis[i + offset]
      else
        @assert ncols(v) == d - offset
        potential_basis[i + offset] = sum( v[1, j]*mQ.top_snf_basis[j + offset] for j = 1:(d - offset) )
      end
    end
    if typeof(R) <: AlgAssAbsOrd
      M = basis_matrix(potential_basis)
      return ideal(algebra(R), R, M)
    else
      M = basis_matrix(potential_basis, FakeFmpqMat)*basis_mat_inv(FakeFmpqMat, R, copy = false)
      return fractional_ideal(R, M)
    end
  end

  return ( group_to_ideal(s) for s in subs )
end

###############################################################################
#
#  Conjugacy classes of integral matrices
#
###############################################################################

function ideal_to_matrix(I::AlgAssAbsOrdIdl)
  O = order(I)
  A = algebra(O)
  a = primitive_element_via_number_fields(A)
  M = FakeFmpqMat(representation_matrix(a, :left))
  M = mul!(M, basis_matrix(I, copy = false), M)
  M = mul!(M, M, basis_mat_inv(I, copy = false))
  @assert isone(M.den)
  return M.num
end

function ideal_to_matrix(I::Union{ AbsNumFieldOrderIdeal, AbsSimpleNumFieldOrderFractionalIdeal })
  O = order(I)
  K = nf(O)
  a = gen(K)
  M = FakeFmpqMat(representation_matrix(a))
  B = basis_matrix(I, copy = false)*basis_matrix(FakeFmpqMat, O, copy = false)
  C = inv(B)
  M = mul!(M, B, M)
  M = mul!(M, M, C)
  @assert isone(M.den)
  return M.num
end

function matrix_to_ideal(O::AlgAssAbsOrd, M::ZZMatrix)
  f = charpoly(M)
  A = algebra(O)
  @assert dim(A) == degree(f) # Actually A == Q[x]/f
  fields_and_maps = as_number_fields(A)
  result = zeros(A, dim(A))
  for (K, AtoK) in fields_and_maps
    MK = change_base_ring(K, M) - gen(K)*identity_matrix(K, dim(A))
    B = kernel(MK, side = :right)
    for j = 1:ncols(B)
      for i = 1:dim(A)
        result[i] += AtoK\B[i, j]
      end
    end
  end
  return ideal_from_lattice_gens(algebra(O), O, result), result
end

function matrix_to_ideal(O::AbsNumFieldOrder, M::ZZMatrix)
  f = charpoly(M)
  K = nf(O)
  @assert K.pol == parent(K.pol)(f)
  result = zeros(K, degree(K))
  MK = change_base_ring(K, M) - gen(K)*identity_matrix(K, degree(K))
  B = kernel(MK, side = :right)
  for j = 1:ncols(B)
    for i = 1:degree(K)
      result[i] += B[i, j]
    end
  end
  return fractional_ideal_from_z_gens(O, result), result
end

# Stefano Marseglia "Computing the ideal class monoid of an order"
@doc raw"""
    is_conjugate(M::ZZMatrix, N::ZZMatrix) -> Bool, ZZMatrix

Returns `true` and a matrix $U$ with $M = U\cdot N\cdot U^{-1}$ if such a
matrix exists and `false` and $0$ otherwise.
The characteristic polynomial of $M$ is required to be square-free.
"""
function is_conjugate(M::ZZMatrix, N::ZZMatrix)
  Zx, x = ZZ["x"]
  f = charpoly(Zx, M)
  if f != charpoly(Zx, N)
    return false, zero_matrix(ZZ, nrows(M), ncols(M))
  end

  fac = factor(f)
  fields = Vector{AbsSimpleNumField}()
  for (g, e) in fac
    e != 1 ? error("The characteristic polynomial must be square-free") : nothing
    push!(fields, number_field(g)[1])
  end

  if length(fields) == 1
    return _isconjugate(equation_order(fields[1]), M, N)
  end

  A, AtoK = direct_product(fields)::Tuple{StructureConstantAlgebra{QQFieldElem}, Vector{AbsAlgAssToNfAbsMor{StructureConstantAlgebra{QQFieldElem}, elem_type(StructureConstantAlgebra{QQFieldElem}), AbsSimpleNumField, QQMatrix}}}
  O = _equation_order(A)
  return _isconjugate(O, M, N)
end

function _isconjugate(O::Union{ AbsNumFieldOrder, AlgAssAbsOrd }, M::ZZMatrix, N::ZZMatrix)
  I, basisI = matrix_to_ideal(O, M)
  J, basisJ = matrix_to_ideal(O, N)
  t, a = is_isomorphic_with_map(J, I)
  if !t
    return false, zero_matrix(ZZ, nrows(M), ncols(M))
  end
  @assert J == a*I

  aBI = basis_matrix([ a*b for b in basisI ], FakeFmpqMat)
  BJ = basis_matrix(basisJ, FakeFmpqMat)
  UU = aBI*inv(BJ)
  @assert isone(UU.den)
  return true, UU.num
end
