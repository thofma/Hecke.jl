export ideal_class_monoid, islocally_isomorphic

###############################################################################
#
#  ICM / isisomorphic
#
###############################################################################

# Stefano Marseglia "Computing the ideal class monoid of an order"
@doc Markdown.doc"""
    ideal_class_monoid(R::NfAbsOrd) -> Vector{NfOrdFracIdl}
    ideal_class_monoid(R::AlgAssAbsOrd) -> Vector{AlgAssAbsOrdFracIdl}

> Given an order $R$ in a number field or a finite product of number fields this
> function returns representatives of the isomorphism classes of fractional
> ideals in $R$.
"""
function ideal_class_monoid(R::T) where { T <: Union{ NfAbsOrd, AlgAssAbsOrd } }
  orders = overorders(R)
  result = Vector{FacElem{frac_ideal_type(R)}}()
  for S in orders
    append!(result, _icm_bar(R, S))
  end
  return result
end

# Stefano Marseglia "Computing the ideal class monoid of an order", Prop. 4.1
@doc Markdown.doc"""
    islocally_isomorphic(I::NfAbsOrdIdl, J::NfAbsOrdIdl) -> Bool
    islocally_isomorphic(I::NfFracOrdIdl, J::NfFracOrdIdl) -> Bool
    islocally_isomorphic(I::AlgAssAbsOrdIdl, J::AlgAssAbsOrdIdl) -> Bool
    islocally_isomorphic(I::AlgAssAbsOrdFracIdl, J::AlgAssAbsOrdFracIdl) -> Bool

> Given two (fractional) ideals $I$ and $J$ of an order $R$ of an $Q$-étale
> algebra, this function returns `true` if $I_p$ and $J_p$ are isomorphic for
> all primes $p$ of $R$ and `false` otherwise.
"""
function islocally_isomorphic(I::T, J::T) where { T <: Union{ NfAbsOrdIdl, NfOrdFracIdl, AlgAssAbsOrdFracIdl, AlgAssAbsOrdIdl } }
  IJ = colon(I, J)
  JI = colon(J, I)
  return one(_algebra(order(I))) in IJ*JI
end

# Stefano Marseglia "Computing the ideal class monoid of an order", Cor. 4.5
@doc Markdown.doc"""
    isisomorphic(I::NfAbsOrdIdl, J::NfAbsOrdIdl) -> Bool, nf_elem
    isisomorphic(I::NfFracOrdIdl, J::NfFracOrdIdl) -> Bool, nf_elem
    isisomorphic(I::AlgAssAbsOrdIdl, J::AlgAssAbsOrdIdl) -> Bool, AbsAlgAssElem
    isisomorphic(I::AlgAssAbsOrdFracIdl, J::AlgAssAbsOrdFracIdl) -> Bool, AbsAlgAssElem

> Given two (fractional) ideals $I$ and $J$ of an order $R$ of an $Q$-étale
> algebra $A$, this function returns `true` and an element $a \in A$ such that
> $I = aJ$ if such an element exists and `false` and $0$ otherwise.
"""
function isisomorphic(I::T, J::T) where { T <: Union{ NfAbsOrdIdl, NfOrdFracIdl, AlgAssAbsOrdIdl, AlgAssAbsOrdFracIdl } }
  A = _algebra(order(I))
  if !islocally_isomorphic(I, J)
    return false, zero(A)
  end

  S = ring_of_multipliers(I)
  IS = extend(I, S)
  JS = extend(J, S)
  IJ = colon(IS, JS)
  t, a = isprincipal(numerator(IJ, copy = false))
  if !t
    return false, zero(A)
  end
  return true, divexact(_elem_in_algebra(a, copy = false), A(denominator(IJ, copy = false)))
end

function ring_of_multipliers(I::Union{ NfOrdFracIdl, AlgAssAbsOrdFracIdl })
  return ring_of_multipliers(numerator(I, copy = false)*denominator(I, copy = false))
end

###############################################################################
#
#  Internals
#
###############################################################################

# Computes representatives of the weak equivalence classes of fractional ideals
# of R with ring of multipliers S.
# Algorithm 2 in Marseglia: "Computing the ideal class monoid of an order"
function _wicm_bar(R::T, S::T) where { T <: Union{ NfAbsOrd, AlgAssAbsOrd } }
  K = _algebra(S)
  oneS = one(K)*S
  St = trace_dual(S)
  reps = Vector{frac_ideal_type(R)}()
  I = St*colon(oneS, St)
  if one(K) in I
    push!(reps, _as_frac_ideal_of_smaller_order(R, oneS))
    return reps
  end

  orders = overorders(S)
  for T in orders
    if T == S
      continue
    end

    StT = St*T
    if !(one(K) in StT*colon(frac_ideal(T, one(K)), StT))
      continue
    end
    f = conductor(S, T)
    fT = f*T
    @assert isone(colon(fT, fT))

    ideals = ideals_containing(T, fT, S)
    for I in ideals
      if colon(I, I) != oneS
        continue
      end
      I = _as_frac_ideal_of_smaller_order(R, I)
      new_class = true
      for J in reps
        if islocally_isomorphic(I, J)
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
function _icm_bar(R::T, S::T) where { T <: Union{ NfAbsOrd, AlgAssAbsOrd } }
  ideals = _wicm_bar(R, S)
  P, mP = picard_group(S)
  fac_elem_mon = FacElemMon(FracIdealSet(R))
  result = Vector{elem_type(fac_elem_mon)}()
  gens_of_P = [ _as_frac_ideal_of_smaller_order(R, mP(P[i])) for i = 1:ngens(P) ]
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
        fac_elem2.fac[I] += fmpz(1)
      else
        fac_elem2.fac[I] = fmpz(1)
      end
      push!(result, fac_elem2)
    end
  end
  return result
end

# Computes all subgroups of S/a as fractional ideals of R.
function ideals_containing(S::T, a::T2, R::T) where { T <: Union{ NfAbsOrd, AlgAssAbsOrd }, T2 <: Union{ NfAbsOrdIdl, AlgAssAbsOrdIdl } }
  Q, mQ = quo(S, a, type = :group)
  if order(Q) == 1
    return [ a ]
  end

  K = _algebra(S)
  d = degree(S)

  potential_basis = Vector{elem_type(_algebra(S))}(undef, d)
  ideals = frac_ideal_type(R)[]

  for i = 1:mQ.offset
    potential_basis[i] = mQ.bottom_snf_basis[i]
  end

  offset = mQ.offset
  subs = subgroups(Q)

  function group_to_ideal(s::Tuple{GrpAbFinGen, GrpAbFinGenMap})
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
    M = basis_mat(potential_basis, FakeFmpqMat)*basis_mat_inv(R, copy = false)
    return frac_ideal(R, M)
  end

  return ( group_to_ideal(s) for s in subs )
end
