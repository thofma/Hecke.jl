################################################################################
#
#  Decomposition
#
################################################################################

# Assume that A is a commutative algebra over a finite field of cardinality q.
# This functions computes a basis for ker(x -> x^q).
function kernel_of_frobenius(A::AbstractAssociativeAlgebra)
  F = base_ring(A)
  q = order(F)

  b = A()
  B = zero_matrix(F, dim(A), dim(A))
  for i = 1:dim(A)
    b.coeffs[i] = one(F)
    if i > 1
      b.coeffs[i - 1] = zero(F)
    end
    c = b^q - b
    for j = 1:dim(A)
      B[j, i] = c.coeffs[j]
    end
  end

  V = kernel(B, side = :right)
  return [ A(V[:, i]) for i in 1:ncols(V) ]
end

@doc raw"""
    decompose(A::AbstractAssociativeAlgebra) -> Array{Tuple{StructureConstantAlgebra, AbsAlgAssMor}}

Given a semisimple algebra $A$, return a decomposition of $A$ as a direct sum
of simple algebras and maps from these
components to $A$.
"""
function decompose(A::StructureConstantAlgebra{T}) where {T}
  if isdefined(A, :decomposition)
    return A.decomposition::Vector{Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}}
  end

  if is_simple_known(A) && A.is_simple == 1
    B, mB = StructureConstantAlgebra(A)
    return Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}[(B, mB)]
  end

  res = _decompose(A)
  A.decomposition = res
  return res
end

# Generic function for everything besides StructureConstantAlgebra
function decompose(A::AbstractAssociativeAlgebra{T}) where T
  return __decompose(A)
end

function __decompose(A::AbstractAssociativeAlgebra{T}) where {T}
  if isdefined(A, :decomposition)
    return A.decomposition::Vector{Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}}
  end

  B, mB = StructureConstantAlgebra(A)

  if is_simple_known(A) && A.is_simple == 1
    return Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}[ (B, mB) ]
  end

  D = _decompose(B)::Vector{Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, StructureConstantAlgebra{T})}}
  res = Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}[]
  for (S, mS) in D
    mD = compose_and_squash(mB, mS)
    push!(res, (S, mD))
  end
  A.decomposition = res
  Z, ZtoB = center(B)
  if dim(Z) != dim(B)
    if isdefined(A, :center)
      @assert A.center[1] === Z
    end
    A.center = (Z, compose_and_squash(mB, ZtoB))
  end
  return res
end

function _decompose(A::AbstractAssociativeAlgebra{T}) where {T}
  @assert _issemisimple(A) != 2 "Algebra is not semisimple"
  if is_commutative(A)
    return _dec_com(A)::Vector{Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}}
  else
    return _dec_via_center(A)::Vector{Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}}
  end
end

function _dec_via_center(A::S) where {T, S <: AbstractAssociativeAlgebra{T}}
  ZA, mZA = center(A)
  Algs = _dec_com(ZA)
  ZA.decomposition = Algs
  res = Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, S)}[ _subalgebra(A, mZA(BtoZA(one(B))), true) for (B, BtoZA) in Algs]
  for i in 1:length(res)
    res[i][1].is_simple = 1
    B, BtoZA = Algs[i] # B is the centre of res[i][1]
    # Build a map from B to res[i][1] via B -> ZA -> A -> res[i][1]
    M = zero_matrix(base_ring(A), dim(B), dim(res[i][1]))
    for j = 1:dim(B)
      t = mZA(BtoZA(B[j]))
      s = res[i][2]\t
      elem_to_mat_row!(M, j, s)
    end
    if dim(res[i][1]) != dim(B)
      res[i][1].center = (B, hom(B, res[i][1], M))
    else
      # res[i][1] is commutative, so we do not cache the centre
      iM = inv(M)
      BtoA = hom(B, A, M*res[i][2].mat, res[i][2].imat*iM)
      res[i] = (B, BtoA)
    end
  end
  A.decomposition = res
  return res
end

function _dec_com(A::AbstractAssociativeAlgebra{T}) where {T}
  v = get_attribute(A, :central_idempotents)
  if v !== nothing
    w = v::Vector{elem_type(A)}
    return _dec_com_given_idempotents(A, w)
  end

  # There are two options
  if is_finite(base_ring(A))
    # the base ring is finite
    # use a special implementation for this
    return _dec_com_finite(A)::Vector{Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}}
  else
    return _dec_com_gen(A)::Vector{Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}}
  end
end

function _dec_com_given_idempotents(A::AbstractAssociativeAlgebra{T}, v::Vector) where {T}
  dec = Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}[]
  for idem in v
    S, StoA = _subalgebra(A, idem, true)
    push!(dec, (S, StoA))
  end
  return dec
end

function _dec_com_gen(A::AbstractAssociativeAlgebra{T}) where {T <: FieldElem}
  @assert !is_finite(base_ring(A))
  if dim(A) == 0
    # The zero-dimensional algebra is the zero ring, which is semisimple, but not simple
    # It has *no* simple components.
    A.is_simple = -1
    return Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}[]
  end

  if dim(A) == 1
    A.is_simple = 1
    B, mB = StructureConstantAlgebra(A)
    return Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}[(B, mB)]
  end

  if !is_separable(A)
    # I am not sure we can/need to find *the* maximal separable subalgebra
    # (it exists, see Roos, "Maximal Separable Subalgebras")
    # B, mB = _separable_subalgebra(...)
    throw(NotImplemented())
  end

  # we are separable and commutative, and the base field is not finite
  # "Efficient decomposition of separable algebras", Eberly, Giesbrecht, 2004,
  # Section 5 claims that we can then do the "normal" trick that always works
  # for large base fields.

  F = base_ring(A)

  k = dim(A)

  V = elem_type(A)[A[i] for i in 1:k]

  cnt = 0

  while true
    cnt += 1
    if cnt > 10000
      error("something is wrong, please report this")
      # either something is really wrong, or we need to adjust the randomization
    end
    c = elem_type(F)[ rand(F, -10:10) for i = 1:k ]
    a = dot(c, V)
    f = minpoly(a)

    if degree(f) < 2
      continue
    end
    if is_irreducible(f)
      if degree(f) == dim(A)
        A.is_simple = 1
        B, mB = StructureConstantAlgebra(A)
        return Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}[(B, mB)]
      end
      continue
    end

    @assert is_squarefree(f)

    fac = factor(f)
    R = parent(f)
    factors = Vector{elem_type(R)}()
    for ff in keys(fac.fac)
      push!(factors, ff)
    end
    sols = Vector{elem_type(R)}()
    right_side = elem_type(R)[ R() for i = 1:length(factors) ]
    max_deg = 0
    for i = 1:length(factors)
      right_side[i] = R(1)
      if i != 1
        right_side[i - 1] = R(0)
      end
      s = crt(right_side, factors)
      push!(sols, s)
      max_deg = max(max_deg, degree(s))
    end
    x = one(A)
    powers = Vector{elem_type(A)}()
    for i = 1:max_deg + 1
      push!(powers, x)
      x *= a
    end
    idems = Vector{elem_type(A)}()
    for s in sols
      idem = A()
      for i = 0:degree(s)
        idem += coeff(s, i)*powers[i + 1]
      end
      push!(idems, idem)
    end

    A.is_simple = 2

    res = Vector{Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}}()
    for idem in idems
      S, StoA = _subalgebra(A, idem, true)
      decS = _dec_com_gen(S)::Vector{Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(S))}}
      for (B, BtoS) in decS
        BtoA = compose_and_squash(StoA, BtoS)
        push!(res, (B, BtoA))
      end
    end
    return res
  end
end

function _dec_com_finite(A::AbstractAssociativeAlgebra{T}) where T
  if dim(A) == 1
    A.is_simple = 1
    B, mB = StructureConstantAlgebra(A)
    return Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}[(B, mB)]
  end

  F = base_ring(A)
  @assert !iszero(characteristic(F))
  V = kernel_of_frobenius(A)
  k = length(V)

  if k == 1
    A.is_simple = 1
    B, mB = StructureConstantAlgebra(A)
    return Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}[(B, mB)]
  end

  A.is_simple = 2
  c = elem_type(F)[ rand(F) for i = 1:k ]
  M = zero_matrix(F, dim(A), dim(A))
  a = dot(c, V)
  representation_matrix!(a, M)
  f = minpoly(M)
  while degree(f) < 2
    for i = 1:length(c)
      c[i] = rand(F)
    end
    a = dot(c, V)
    zero!(M)
    representation_matrix!(a, M)
    f = minpoly(M)
  end

  #@assert is_squarefree(f)
  fac = factor(f)
  R = parent(f)
  factorss = collect(keys(fac.fac))
  sols = Vector{typeof(f)}(undef, length(factorss))
  right_side = typeof(f)[ zero(R) for i = 1:length(factorss) ]
  max_deg = 0
  for i = 1:length(factorss)
    right_side[i] = one(R)
    if 1 != i
      right_side[i - 1] = zero(R)
    end
    sols[i] = crt(right_side, factorss)
    max_deg = max(max_deg, degree(sols[i]))
  end
  powers = Vector{elem_type(A)}(undef, max_deg+1)
  powers[1] = one(A)
  powers[2] = a
  x = a
  for i = 3:max_deg + 1
    x *= a
    powers[i] = x
  end

  idems = Vector{elem_type(A)}()
  for s in sols
    idem = A()
    for i = 0:degree(s)
      idem += coeff(s, i)*powers[i + 1]
    end
    push!(idems, idem)
  end

  res = Vector{Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}}()
  for idem in idems
    S, StoA = _subalgebra(A, idem, true)
    decS = _dec_com_finite(S)
    for (B, BtoS) in decS
      BtoA = compose_and_squash(StoA, BtoS)
      push!(res, (B, BtoA))
    end
  end
  return res
end

################################################################################
#
#  Decomposition as number fields
#
################################################################################

@doc raw"""
    components(::Type{Field}, A::AbstractAssociativeAlgebra)
      -> Vector{Tuple{Field, Morphism}}

Given an étale algebra $A$, return the simple components of $A$
as fields $K$ together with the projection $A \to K$.
"""
function components(::Type{Field}, A::AbstractAssociativeAlgebra)
  @assert is_commutative(A)
  return as_number_fields(A)
end

@doc raw"""
    component(::Type{Field}, A::AbstractAssociativeAlgebra, i::Int)
      -> Vector{Tuple{Field, Morphism}}

Given an étale algebra $A$ and index $i$, return the $i$-th simple components
of $A$ as a field $K$ together with the projection $A \to K$.
"""
function component(::Type{Field}, A::AbstractAssociativeAlgebra, i::Int)
  nf = as_number_fields(A)
  return nf[i]
end

@doc raw"""
    as_number_fields(A::AbstractAssociativeAlgebra{QQFieldElem})
      -> Vector{Tuple{AbsSimpleNumField, AbsAlgAssToNfAbsMor}}

Given a commutative algebra $A$ over $\mathbb Q$, this function returns a
decomposition of $A$ as direct sum of number fields and maps from $A$ to
these fields.
"""
function as_number_fields(A::AbstractAssociativeAlgebra{T}) where {T}
  return __as_number_fields(A)
end

function __as_number_fields(A::AbstractAssociativeAlgebra{T}; use_maximal_order::Bool = true) where {T}
  if isdefined(A, :maps_to_numberfields)
    NF = A.maps_to_numberfields::Vector{Tuple{_ext_type(T), _abs_alg_ass_to_nf_abs_mor_type(A)}}
    return NF
  end

  result = _as_number_fields(A, use_maximal_order = use_maximal_order)
  @assert all(domain(AtoK) === A for (_, AtoK) in result)
  A.maps_to_numberfields = result
  return result
end

_ext_type(::Type{QQFieldElem}) = AbsSimpleNumField

_ext_type(::Type{AbsSimpleNumFieldElem}) = RelSimpleNumField{AbsSimpleNumFieldElem}

function _as_number_fields(A::AbstractAssociativeAlgebra{T}; use_maximal_order::Bool = true) where {T}
  d = dim(A)

  Adec = decompose(A)

  fields_not_cached = false
  for i = 1:length(Adec)
    if !isdefined(Adec[i][1], :maps_to_numberfields)
      fields_not_cached = true
    end
  end

  if fields_not_cached && T === QQFieldElem && use_maximal_order
    # Compute a LLL reduced basis of the maximal order of A to find "small"
    # polynomials for the number fields.
    OA = maximal_order(A)
    L = lll(basis_matrix(FakeFmpqMat, OA, copy = false).num)
    n = basis_matrix(FakeFmpqMat, OA, copy = false).den
    basis_lll = elem_type(A)[ elem_from_mat_row(A, L, i, n) for i = 1:d ]
  elseif fields_not_cached
    basis_lll = basis(A)
  end

  KK = base_ring(A)

  M = zero_matrix(KK, 0, d)
  matrices = Vector{dense_matrix_type(T)}()
  fields = Vector{_ext_type(T)}()
  for i = 1:length(Adec)
    # For each small algebra construct a number field and the isomorphism
    B, BtoA = Adec[i]
    dB = dim(B)
    if !isdefined(B, :maps_to_numberfields)
      local K, BtoK
      found_field = false # Only for debugging
      for j = 1:d
        t = BtoA\basis_lll[j]
        mint = minpoly(t)
        if degree(mint) == dB
          found_field = true
          K, BtoK = _as_field_with_isomorphism(B, t, mint)
          B.maps_to_numberfields = Tuple{_ext_type(T), _abs_alg_ass_to_nf_abs_mor_type(B)}[(K, BtoK)]
          push!(fields, K)
          break
        end
      end
      @assert found_field "This should not happen..."
    else
      K, BtoK = B.maps_to_numberfields[1]::Tuple{_ext_type(T), _abs_alg_ass_to_nf_abs_mor_type(B)}
      push!(fields, K)
    end

    # TODO: We can do a short cut, but the map must be BtoK \circ inv(BtoA)
    #if length(Adec) == 1
    #  res = Tuple{_ext_type(T), _abs_alg_ass_to_nf_abs_mor_type(A)}[(K, BtoK)]
    #  A.maps_to_numberfields = res
    #  return res
    #end

    # Construct the map from K to A
    N = zero_matrix(KK, degree(K), d)
    for j = 1:degree(K)
      t = BtoA(BtoK\basis(K)[j])
      elem_to_mat_row!(N, j, t)
    end
    push!(matrices, N)
    M = vcat(M, N)
  end
  @assert nrows(M) == d

  invM = inv(M)
  matrices2 = Vector{dense_matrix_type(T)}(undef, length(matrices))
  offset = 1
  for i = 1:length(matrices)
    r = nrows(matrices[i])
    N = sub(invM, 1:d, offset:(offset + r - 1))
    matrices2[i] = N
    offset += r
  end

  result = Vector{Tuple{_ext_type(T), _abs_alg_ass_to_nf_abs_mor_type(A)}}()
  for i = 1:length(fields)
    push!(result, (fields[i], AbsAlgAssToNfAbsMor(A, fields[i], matrices2[i], matrices[i])))
  end

  return result
end


