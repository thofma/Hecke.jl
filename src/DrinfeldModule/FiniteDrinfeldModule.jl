################################################################################
#
#  DrinfeldModule/FiniteDrinfeldModule.jl : Methods for Drinfeld modules
#  over finite fields
#
#  These methods apply when the base field K of the Drinfeld module is a
#  finite extension of the constants field F_q.
#
################################################################################

################################################################################
#
#  Frobenius endomorphism
#
#  The Frobenius endomorphism is the morphism given by tau^n in K{tau},
#  where n = [K : F_q] is the degree of K over the constants field.
#
################################################################################

@doc raw"""
    frobenius_endomorphism(phi::DrinfeldModule) -> DrinfeldModuleMorphism

Return the Frobenius endomorphism of `phi`, i.e., the endomorphism given
by the Ore polynomial `tau^n`, where `n = [K : F_q]` is the degree of the
base field `K` over the constants field `F_q = base_ring(function_ring(phi))`.
"""
function frobenius_endomorphism(phi::DrinfeldModule{T}) where {T}
  K = base_ring(phi)
  Fq = base_ring(function_ring(phi))
  n = divexact(degree(K), degree(Fq))  # [K : F_q]
  R = ore_polynomial_ring(phi)
  frob_poly = gen(R)^n
  return DrinfeldModuleMorphism{T}(phi, phi, frob_poly)
end

################################################################################
#
#  Ordinary and supersingular
#
################################################################################

@doc raw"""
    is_ordinary(phi::DrinfeldModule) -> Bool

Return `true` if `phi` is ordinary, i.e., if its height equals 1.
"""
function is_ordinary(phi::DrinfeldModule)
  return height(phi) == 1
end

@doc raw"""
    is_supersingular(phi::DrinfeldModule) -> Bool

Return `true` if `phi` is supersingular, i.e., if its height equals its rank.
"""
function is_supersingular(phi::DrinfeldModule)
  return height(phi) == rank(phi)
end

################################################################################
#
#  Frobenius characteristic polynomial
#
#  We implement the CSA (Central Simple Algebra) algorithm due to Gekeler.
#  The result is a monic polynomial of degree r = rank(phi) in A[X] = F_q[T][X].
#
#  For base fields F_q with degree > 1 over the prime field, projection of
#  K-elements back to F_q requires a compatible embedding; if it fails, an
#  error is raised.
#
################################################################################

# Helper: project an element c of K (which must lie in F_q) to F_q.
function _project_to_base_field(c, Fq)
  q = order(Fq)
  @req iszero(c^q - c) "element is not in the base field F_q"
  if degree(Fq) == 1
    # F_q is the prime field GF(p); coeff(c, 0) gives the GF(p)-element
    return Fq(coeff(c, 0))
  end
  # For higher-degree F_q, try direct coercion
  try
    return Fq(c)
  catch
    error("Cannot project K-element to F_q automatically; ensure K was constructed as an extension of F_q")
  end
end

@doc raw"""
    frobenius_charpoly(phi::DrinfeldModule; var::VarName = :X)
      -> PolyRingElem

Return the characteristic polynomial of the Frobenius endomorphism of `phi`.
This is a monic polynomial of degree `rank(phi)` in `F_q[T][X]`, where
`F_q[T]` is the function ring of `phi`.

Uses the CSA (central simple algebra) algorithm.
"""
function frobenius_charpoly(phi::DrinfeldModule{T}; var::VarName = :X) where {T}
  K = base_ring(phi)
  A = function_ring(phi)
  Fq = base_ring(A)
  r = rank(phi)
  n_zz = divexact(ZZRingElem(degree(K)), ZZRingElem(degree(Fq)))  # [K:F_q]
  n = Int(n_zz)

  # Build the n x n matrix over K[Z] (Z will correspond to T in A after
  # extracting F_q-coefficients).
  KZ, Z = polynomial_ring(K, :Z; cached = false)

  phi_T = gen(phi)
  R_ore = ore_polynomial_ring(phi)
  tau = gen(R_ore)

  # Row i (1-indexed) corresponds to f = tau^{i-1} * phi_T.
  f = phi_T
  mat_entries = elem_type(KZ)[]
  for i in 1:n
    d = degree(f)
    for j in 0:n - 1
      # KZ-polynomial: sum_{k >= 0} coeff(f, j + k*n) * Z^k
      kz_coeffs = T[]
      k = 0
      while j + k * n <= d
        push!(kz_coeffs, coeff(f, j + k * n))
        k += 1
      end
      push!(mat_entries, KZ(kz_coeffs))
    end
    if i < n
      f = tau * f
    end
  end

  M = matrix(KZ, n, n, mat_entries)

  # Characteristic polynomial of M over KZ: degree n in X
  KZX, _ = polynomial_ring(KZ, Symbol(var); cached = false)
  chi = charpoly(KZX, M)

  # Normalization constant: Z^r-coefficient of the X^0-coefficient of chi.
  chi0 = AbstractAlgebra.coeff(chi, 0)  # element of KZ
  lc = AbstractAlgebra.coeff(chi0, r)   # element of K

  # Extract the Frobenius charpoly as a polynomial in A[X] = F_q[T][X].
  # The j-th coefficient (of X^j) of the Frobenius charpoly is:
  #   a_j(T) = sum_{i=0}^{floor((r-j)*n/r)} coeff(chi[i], j) / lc * T^i
  AX, _ = polynomial_ring(A, Symbol(var); cached = false)
  result_coeffs = elem_type(A)[]

  for j in 0:r
    chi_j_in_Z = AbstractAlgebra.coeff(chi, j)  # element of KZ
    deg_bound = div((r - j) * n, r)              # max degree in T
    a_coeffs = elem_type(Fq)[]
    for i in 0:deg_bound
      # chi[i] is the X^i-coeff of chi; we want its Z^j-coeff.
      chi_i = AbstractAlgebra.coeff(chi, i)      # element of KZ
      c_ij = AbstractAlgebra.coeff(chi_i, j)     # element of K
      c_norm = c_ij * inv(lc)
      push!(a_coeffs, _project_to_base_field(c_norm, Fq))
    end
    push!(result_coeffs, A(a_coeffs))
  end

  return AX(result_coeffs)
end

################################################################################
#
#  Frobenius trace and norm
#
################################################################################

@doc raw"""
    frobenius_trace(phi::DrinfeldModule) -> PolyRingElem

Return the trace of the Frobenius endomorphism of `phi`, i.e., the negation
of the coefficient of `X^{r-1}` in the Frobenius characteristic polynomial.
"""
function frobenius_trace(phi::DrinfeldModule)
  chi = frobenius_charpoly(phi)
  r = rank(phi)
  return -AbstractAlgebra.coeff(chi, r - 1)
end

@doc raw"""
    frobenius_norm(phi::DrinfeldModule) -> PolyRingElem

Return the norm of the Frobenius endomorphism of `phi`, i.e., the constant
term of the Frobenius characteristic polynomial (up to sign).
"""
function frobenius_norm(phi::DrinfeldModule)
  chi = frobenius_charpoly(phi)
  return AbstractAlgebra.coeff(chi, 0)
end

################################################################################
#
#  Isogenous modules
#
################################################################################

@doc raw"""
    is_isogenous(phi::DrinfeldModule, psi::DrinfeldModule) -> Bool

Return `true` if `phi` and `psi` are isogenous over the base field, i.e.,
if they have the same rank and the same Frobenius characteristic polynomial.
"""
function is_isogenous(phi::DrinfeldModule, psi::DrinfeldModule)
  @req function_ring(phi) === function_ring(psi) "modules must have the same function ring"
  @req base_ring(phi) === base_ring(psi) "modules must have the same base ring"
  rank(phi) == rank(psi) || return false
  chi1 = frobenius_charpoly(phi)
  chi2 = frobenius_charpoly(psi)
  return collect(coefficients(chi1)) == collect(coefficients(chi2))
end
