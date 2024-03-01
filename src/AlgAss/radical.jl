################################################################################
#
#  Radical
#
################################################################################
#
# We do characteristic zero or finite fields, mainly following
# W. Eberly: Computations for Algebras and Group Representations (Section 2.3)
#
#  Dispatch strategy
#
#  radical(A) -> _radical(A) which is supposed to return a basis of the radical
#  _radical(A) --> _radical_zero(A) (characteristic zero)
#              \-> _radical_finite(A) -> _radical_finite(A) (finite fields)
#  (via runtime dispatch)
#
#  TODO:
#  - make the finite field case fast for non-prime fields
#    (by directly implementing it for matrix algebras as in the prime field
#    case)
#  - Implement for algebras over F_q(X_1,...X_m), following Ivanyos,
#    Ronyai, Szanto, "Decomposition of Algebras over Fq(Xl,... , Xm)",
#    (doi:10.1007/bf01438277).
#  - Use Cohen-Ivanyos-Wales
#    "Finding the radical of an algebra of linear transformations"
#    for all finite fields
#  - distinguish between the p <= n and p > n case

@doc raw"""
     radical(A::AbstractAssociativeAlgebra) -> AbsAlgAssIdl

Returns the Jacobson radical of $A$.
"""
function radical(A::AbstractAssociativeAlgebra)
  return ideal_from_gens(A, _radical(A), :twosided)
end

function _radical(A::AbstractAssociativeAlgebra)
  K = base_ring(A)
  if is_zero(characteristic(K))
    return _radical_zero(A)
  elseif is_finite(K)
    return _radical_finite(A)
  else
    throw(NotImplemented())
  end
end

################################################################################
#
#  Characteristic zero
#
################################################################################

function _radical_zero(A::AbstractAssociativeAlgebra{T}) where { T <: Union{ QQFieldElem, NumFieldElem } }
  M = trace_matrix(A)
  N = kernel(M; side = :right)
  n = ncols(N)
  b = Vector{elem_type(A)}(undef, n)
  t = zeros(base_ring(A), dim(A))
  # the construct A(t) will make a copy (hopefully :))
  for i = 1:n
    for j = 1:dim(A)
      t[j] = N[j, i]
    end
    b[i] = A(t)
  end
  return b
end

################################################################################
#
#  Finite fields
#
################################################################################

# Section 2.3.2 in W. Eberly: Computations for Algebras and Group Representations

# Strategy
#
# _radical_finite(::AbstractAssociativeAlgebra)
#   -> _radical_finite(::MatAlgebra)
#     -> _radical_finite_generic(::AbstractAssociativeAlgebra)
#       -> _radical_finite_prime_field(::AbstractAssociativeAlgebra)
#     -> _radical_finite(::MatAlgebra{Native})
#       -> _radical_finite_generic(::AbstractAssociativeAlgebra)
#
# _radical_finite_generic(::AbstractAssociativeAlgebra)
#   -> _radical_finite_prime_field(::AbstractAssociativeAlgebra)
#   -> _radical_finite_prime_field(::MatAlgebra) is fast for Native!
#
# _radical_finite_prime_field(::MatAlgebra)
# is optimized for fpField and FpField

function _radical_finite(A::AbstractAssociativeAlgebra)
  # First thing we do is to consider the regular representation
  B, BtoA = regular_matrix_algebra(A)
  return BtoA.(_radical_finite(B))
end

function _radical_finite(A::MatAlgebra)
  F = base_ring(A)
  if order(F) == characteristic(F) && !(F isa FqPolyRepField) && !(F isa fqPolyRepField)
    return _radical_finite_prime_field(A)
  else
    return _radical_finite_generic(A)
  end
end

function _radical_finite(A::MatAlgebra{FqFieldElem})
  # FqField misses a lot of inplace functions and optimiziations
  # We first pass to a 'native' type (except in the Zech representation)
  F = base_ring(A)
  type = Nemo._fq_default_ctx_type(F)
  if type == 2
    f = Nemo.canonical_raw_type(fqPolyRepField, F)
    FF = codomain(f)
    AA = matrix_algebra(FF, [f.(matrix(m)) for m in basis(A)], isbasis = true)
    RR = _radical_finite(AA)
    return [A(map_entries(c -> preimage(f, c), matrix(a)), check = false) for a in RR]
  elseif type == 3
    f = Nemo.canonical_raw_type(FqPolyRepField, F)
    FF = codomain(f)
    AA = matrix_algebra(FF, [f.(matrix(m)) for m in basis(A)], isbasis = true)
    RR = _radical_finite(AA)
    return [A(map_entries(c -> preimage(f, c), matrix(a)), check = false) for a in RR]
  elseif type == 4
    f = Nemo.canonical_raw_type(fpField, F)
    FF = codomain(f)
    AA = matrix_algebra(FF, [f.(matrix(m)) for m in basis(A)], isbasis = true)
    RR = _radical_finite(AA)
    return [A(map_entries(c -> preimage(f, c), matrix(a)), check = false) for a in RR]
  elseif type == 5
    f = Nemo.canonical_raw_type(FpField, F)
    FF = codomain(f)
    AA = matrix_algebra(FF, [f.(matrix(m)) for m in basis(A)], isbasis = true)
    RR = _radical(AA)
    return [A(map_entries(c -> preimage(f, c), matrix(a)), check = false) for a in RR]
  else
    # this is a Zech representation, so use the generic fallback
    return _radical_finite_generic(A)
  end
end

function _radical_finite_prime_field(A::MatAlgebra{<:Union{fpFieldElem, FpFieldElem}})
  F = base_ring(A)
  p = characteristic(F)
  @assert p == order(F)
  k = flog(ZZRingElem(dim(A)), p)

  # We have to take the matrix trace : M_n(K) -> K
  # and not the "algebra" trace
  MF = trace_matrix(A, x -> tr(matrix(x, copy = false)))
  B = kernel(MF; side = :right)
  d = ncols(B)
  if d == 0
    return elem_type(A)[]
  end

  C = transpose(B)
  # Now, iterate: we need to find the kernel of tr((xy)^(p^i))/p^i mod p
  # on the subspace generated by C
  # Hard to believe, but this is linear!!!!
  pl = 1
  # if k > 0, then p < dim(A) <= typemax(Int)
  Mtemp = zero_matrix(ZZ, degree(A), degree(A))
  if k > 0 
    _p = Int(p)
    R, mR = residue_ring(ZZ, _p^(k + 1))
    MR = zero_matrix(R, degree(A), degree(A))
    a = A()
    for l = 1:k
      pl = pl * _p
      M = zero_matrix(F, dim(A), nrows(C))
      for i = 1:nrows(C)
        c = elem_from_mat_row(A, C, i)
        for j = 1:dim(A)
          a = mul!(a, c, A[j])
          MF = matrix(a, copy = false)
          # this is suboptimal
          _lift!(MR, MF, Mtemp)
          t = preimage(mR, tr(MR^pl))
          @assert iszero(mod(t, pl))
          M[j, i] = F(divexact(t, pl))
        end
      end
      B = kernel(M; side = :right)
      d = ncols(B)
      if d == 0
        return elem_type(A)[]
      end
      C = transpose(B)*C
    end
  end

  return elem_type(A)[ elem_from_mat_row(A, C, i) for i = 1:nrows(C) ]
end

function _radical_finite_prime_field(A::AbstractAssociativeAlgebra)
  F = base_ring(A)
  p = characteristic(F)
  @assert p == order(F)
  k = flog(ZZRingElem(dim(A)), p)

  MF = trace_matrix(A)
  B = kernel(MF; side = :right)
  d = ncols(B)
  if d == 0
    return elem_type(A)[]
  end

  C = transpose(B)
  # Now, iterate: we need to find the kernel of tr((xy)^(p^i))/p^i mod p
  # on the subspace generated by C
  # Hard to believe, but this is linear!!!!
  MZ = zero_matrix(ZZ, dim(A), dim(A))
  pl = ZZRingElem(1)
  a = A()
  for l = 1:k
    pl = p*pl
    M = zero_matrix(F, dim(A), nrows(C))
    for i = 1:nrows(C)
      c = elem_from_mat_row(A, C, i)
      for j = 1:dim(A)
        a = mul!(a, c, A[j])
        MF = representation_matrix(a)
        for m = 1:nrows(MF)
          for n = 1:ncols(MF)
            MZ[m, n] = lift(ZZ, MF[m, n])
          end
        end
        t = tr(MZ^Int(pl))
        @assert iszero(mod(t, pl))
        M[j, i] = F(divexact(t, pl))
      end
    end
    B = kernel(M; side = :right)
    if ncols(B) == 0
      return elem_type(A)[]
    end
    C = transpose(B)*C
  end

  return elem_type(A)[ elem_from_mat_row(A, C, i) for i = 1:nrows(C) ]
end

function _radical_finite_generic(A::AbstractAssociativeAlgebra{T}) where {T <: Union{fqPolyRepFieldElem, FqPolyRepFieldElem, FqFieldElem}}
  F = base_ring(A)

  p = characteristic(F)
  if T === fqPolyRepFieldElem
    Fp = Native.GF(Int(p))
  elseif T === FqFieldElem
    Fp = GF(p)
  else
    Fp = Native.GF(p)
  end

  if T === FqFieldElem
    n = absolute_degree(F)
  else
    n = degree(F)
  end

  if n == 1
    if T === FqFieldElem
      return _radical_finite_prime_field(A)
    else
      A2, A2toA = restrict_scalars(A, Fp)
      J = _radical_finite_prime_field(A2)
      return elem_type(A)[ A2toA(b) for b in J ]
    end
  end

  A2, A2toA = restrict_scalars(A, Fp)

  if T === FqFieldElem
    absgenF =  Nemo._gen(F)
  else
    absgenF = gen(F)
  end

  k = flog(ZZRingElem(dim(A)), p)
  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = Qx(push!(QQFieldElem[ -QQFieldElem(T === FqFieldElem ? Nemo._coeff(absgenF^n, i) : coeff(absgenF^n, i)) for i = 0:(n - 1) ], QQFieldElem(1)))
  K, a = number_field(f, "a")

  MF = trace_matrix(A2)
  B = kernel(MF; side = :right)
  if ncols(B) == 0
    return elem_type(A)[]
  end

  C = transpose(B)
  pl = ZZRingElem(1)
  MK = zero_matrix(K, dim(A), dim(A))
  MQx = zero_matrix(Qx, dim(A), dim(A))
  a = A()
  for l = 1:k
    pl = p*pl
    M = zero_matrix(Fp, dim(A2), nrows(C))
    for i = 1:nrows(C)
      c = A2toA(elem_from_mat_row(A2, C, i))
      for j = 1:dim(A)
        a = mul!(a, c, A[j])
        MF = representation_matrix(a)
        MK = _lift_fq_mat!(MF, MK, MQx)
        t = tr(MK^Int(pl))
        @assert all([ iszero(mod(coeff(t, s), pl)) for s = 0:(n - 1) ])
        jn = (j - 1)*n
        for s = 1:n
          M[jn + s, i] = Fp(divexact(numerator(coeff(t, s - 1)), pl))
        end
      end
    end
    B = kernel(M; side = :right)
    if ncols(B) == 0
      return elem_type(A)[]
    end
    C = transpose(B)*C
  end

  return elem_type(A)[ A2toA(elem_from_mat_row(A2, C, i)) for i = 1:nrows(C) ]
end

################################################################################
#
#  Helper
#
################################################################################

function _lift_fq_mat!(M1::MatElem{T}, M2::MatElem{AbsSimpleNumFieldElem}, M3::MatElem{QQPolyRingElem}) where { T <: Union{ fqPolyRepFieldElem, FqPolyRepFieldElem, FqFieldElem } }
  @assert ncols(M1) == ncols(M2) && ncols(M1) == ncols(M3)
  @assert nrows(M1) == nrows(M2) && nrows(M1) == nrows(M3)
  n = degree(base_ring(M1))
  K = base_ring(M2)
  R = base_ring(M3)
  for i = 1:nrows(M1)
    for j = 1:ncols(M1)
      # Sadly, there is no setcoeff! for AbsSimpleNumFieldElem...
      for k = 0:(n - 1)
        if T === FqFieldElem
          M3[i, j] = setcoeff!(M3[i, j], k, QQFieldElem(Nemo._coeff(M1[i, j], k)))
        else
          M3[i, j] = setcoeff!(M3[i, j], k, QQFieldElem(coeff(M1[i, j], k)))
        end
      end
      ccall((:nf_elem_set_fmpq_poly, libantic), Nothing, (Ref{AbsSimpleNumFieldElem}, Ref{QQPolyRingElem}, Ref{AbsSimpleNumField}), M2[i, j], M3[i, j], K)
    end
  end
  return M2
end

function lift!(A::ZZMatrix, B::FqMatrix)
  for i in 1:nrows(A)
    for j in 1:ncols(A)
      A[i, j] = lift(ZZ, B[i, j])
    end
  end
  return A
end

function _lift!(A::zzModMatrix, B::fpMatrix, Mtemp)
  ccall((:nmod_mat_set, libflint), Cvoid, (Ref{zzModMatrix}, Ref{fpMatrix}), A, B)
  return A
end

function _lift!(A::zzModMatrix, B::FpMatrix, Mtemp::ZZMatrix)
  ccall((:fmpz_mod_mat_get_fmpz_mat, libflint), Cvoid, (Ref{ZZMatrix}, Ref{FpMatrix}), Mtemp, B)
  ccall((:fmpz_mat_get_nmod_mat, libflint), Cvoid, (Ref{zzModMatrix}, Ref{ZZMatrix}), A, Mtemp)
  return A
end
