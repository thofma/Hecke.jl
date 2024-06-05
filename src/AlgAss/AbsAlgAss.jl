_base_ring(A::AbstractAssociativeAlgebra) = base_ring(A)

################################################################################
#
#  Morphism types
#
################################################################################

morphism_type(::Type{T}, ::Type{S}) where {R, T <: AbstractAssociativeAlgebra{R}, S <: AbstractAssociativeAlgebra{R}} = AbsAlgAssMor{T, S, Generic.MatSpaceElem{R}}

morphism_type(::Type{T}, ::Type{S}) where {T <: AbstractAssociativeAlgebra{QQFieldElem}, S <: AbstractAssociativeAlgebra{QQFieldElem}} = AbsAlgAssMor{T, S, QQMatrix}

morphism_type(::Type{T}, ::Type{S}) where {T <: AbstractAssociativeAlgebra{FqPolyRepFieldElem}, S <: AbstractAssociativeAlgebra{FqPolyRepFieldElem}} = AbsAlgAssMor{T, S, FqPolyRepMatrix}

morphism_type(::Type{T}, ::Type{S}) where {T <: AbstractAssociativeAlgebra{fqPolyRepFieldElem}, S <: AbstractAssociativeAlgebra{fqPolyRepFieldElem}} = AbsAlgAssMor{T, S, fqPolyRepMatrix}

morphism_type(::Type{T}, ::Type{S}) where {T <: AbstractAssociativeAlgebra{zzModRingElem}, S <: AbstractAssociativeAlgebra{zzModRingElem}} = AbsAlgAssMor{T, S, zzModMatrix}

morphism_type(::Type{T}, ::Type{S}) where {T <: AbstractAssociativeAlgebra{fpFieldElem}, S <: AbstractAssociativeAlgebra{fpFieldElem}} = AbsAlgAssMor{T, S, fpMatrix}

morphism_type(::Type{T}, ::Type{S}) where {T <: AbstractAssociativeAlgebra{FpFieldElem}, S <: AbstractAssociativeAlgebra{FpFieldElem}} = AbsAlgAssMor{T, S, FpMatrix}

morphism_type(::Type{T}, ::Type{S}) where {T <: AbstractAssociativeAlgebra{FqFieldElem}, S <: AbstractAssociativeAlgebra{FqFieldElem}} = AbsAlgAssMor{T, S, FqMatrix}

morphism_type(A::Type{T}) where {T <: AbstractAssociativeAlgebra} = morphism_type(A, A)

################################################################################
#
#  Basis
#
################################################################################

@doc raw"""
    basis(A::AbstractAssociativeAlgebra) -> Vector{AbstractAssociativeAlgebraElem}

Returns the basis of $A$.
"""
function basis(A::AbstractAssociativeAlgebra)
  if isdefined(A, :basis)
    return A.basis::Vector{elem_type(A)}
  end
  B = Vector{elem_type(A)}(undef, dim(A))
  for i in 1:dim(A)
    z = Vector{elem_type(base_ring(A))}(undef, dim(A))
    for j in 1:dim(A)
      z[j] = zero(base_ring(A))
    end
    z[i] = one(base_ring(A))
    B[i] = A(z)
  end
  A.basis = B
  return B::Vector{elem_type(A)}
end

################################################################################
#
#  Associativity, Distributivity test
#
################################################################################

function check_associativity(A::AbstractAssociativeAlgebra)
  for i = 1:dim(A)
    for j = 1:dim(A)
      el = A[i] * A[j]
      for k = 1:dim(A)
        if el * A[k] != A[i] * (A[j] * A[k])
          return false
        end
      end
    end
  end
  return true
end

function check_distributivity(A::AbstractAssociativeAlgebra)
  for i = 1:dim(A)
    for j = 1:dim(A)
      el = A[i]*A[j]
      for k = 1:dim(A)
        if A[i] * (A[j] + A[k]) != el + A[i] * A[k]
          return false
        end
      end
    end
  end
  return true
end

################################################################################
#
#  Dimension of/over center
#
################################################################################

@attr Int function dimension_of_center(A::AbstractAssociativeAlgebra)
  C, _ = center(A)
  return dim(C)
end

@attr Int function dimension_over_center(A::AbstractAssociativeAlgebra)
  return divexact(dim(A), dimension_of_center(A))
end

@attr Int function degree_as_central_simple_algebra(A::AbstractAssociativeAlgebra)
  return isqrt(dimension_over_center(A))
end

@attr Bool is_central(A::AbstractAssociativeAlgebra) = dimension_of_center(A) == 1

################################################################################
#
#  Subalgebras
#
################################################################################

# This is the generic fallback which constructs an associative algebra
@doc raw"""
    subalgebra(A::AbstractAssociativeAlgebra, e::AbstractAssociativeAlgebraElem, idempotent::Bool = false,
               action::Symbol = :left)
      -> StructureConstantAlgebra, AbsAlgAssMor

Given an algebra $A$ and an element $e$, this function constructs the algebra
$e \cdot A$ (if `action == :left`) respectively $A \cdot e$ (if `action == :right`)
and a map from this algebra to $A$.
If `idempotent` is `true`, it is assumed that $e$ is idempotent in $A$.
"""
function subalgebra(A::AbstractAssociativeAlgebra{T}, e::AbstractAssociativeAlgebraElem{T}, idempotent::Bool = false, action::Symbol = :left) where {T}
  @assert parent(e) == A
  B, mB = StructureConstantAlgebra(A)
  C, mC = subalgebra(B, mB\e, idempotent, action)
  mD = compose_and_squash(mB, mC)
  @assert domain(mD) == C
  return C, mD
end

@doc raw"""
    subalgebra(A::AbstractAssociativeAlgebra, basis::Vector{AbstractAssociativeAlgebraElem})
      -> StructureConstantAlgebra, AbsAlgAssMor

Returns the subalgebra $A$ generated by the elements in `basis` and a map
from this algebra to $A$.
"""
function subalgebra(A::AbstractAssociativeAlgebra{T}, basis::Vector{ <: AbstractAssociativeAlgebraElem{T} }) where T
  B, mB = StructureConstantAlgebra(A)
  basis_pre = elem_type(B)[mB\(basis[i]) for i in 1:length(basis)]
  C, mC = subalgebra(B, basis_pre)
  mD = compose_and_squash(mB, mC)
  @assert domain(mD) == C
  return C, mD
end

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

Given a semisimple algebra $A$ over a field, this function returns a
decomposition of $A$ as a direct sum of simple algebras and maps from these
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
  res = Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, S)}[ subalgebra(A, mZA(BtoZA(one(B))), true) for (B, BtoZA) in Algs]
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

  if characteristic(base_ring(A)) > 0
    return _dec_com_finite(A)::Vector{Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}}
  else
    return _dec_com_gen(A)::Vector{Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}}
  end
end

function _dec_com_given_idempotents(A::AbstractAssociativeAlgebra{T}, v::Vector) where {T}
  dec = Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}[]
  for idem in v
    S, StoA = subalgebra(A, idem, true)
    push!(dec, (S, StoA))
  end
  return dec
end

function _dec_com_gen(A::AbstractAssociativeAlgebra{T}) where {T <: FieldElem}
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

  F = base_ring(A)

  k = dim(A)

  V = elem_type(A)[A[i] for i in 1:k]

  while true
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
      S, StoA = subalgebra(A, idem, true)
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
    S, StoA = subalgebra(A, idem, true)
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

################################################################################
#
#  Random elements
#
################################################################################

Random.gentype(::Type{T}) where {T<:AbstractAssociativeAlgebra} = elem_type(T)

function rand(rng::AbstractRNG, Asp::SamplerTrivial{S}) where {T, S <: AbstractAssociativeAlgebra{T}}
  A = Asp[]
  c = [rand(rng, base_ring(A)) for i in 1:dim(A)]
#  c = rand(rng, base_ring(A), dim(A))
#  Using the above makes @inferred Random.rand(Random.GLOBAL_RNG, -1:1, 10) fail
  return A(c)
end

function rand(A::AbstractAssociativeAlgebra{AbsSimpleNumFieldElem}, rng::AbstractUnitRange{Int} = -10:10)
  c = AbsSimpleNumFieldElem[rand(base_ring(A), rng) for i = 1:dim(A)]
  return A(c)
end

function rand(A::AbstractAssociativeAlgebra{T}, rng::AbstractUnitRange{Int}) where T
  c = T[rand(base_ring(A), rng) for i = 1:dim(A)]
  return A(c)
end

function rand(A::StructureConstantAlgebra{QQFieldElem}, rng::AbstractUnitRange{Int} = -20:20)
  c = [QQFieldElem(rand(FlintZZ, rng)) for i = 1:dim(A)]
  return A(c)
end

################################################################################
#
#  Generators
#
################################################################################

# Reduces the vector v w. r. t. M and writes it in the i-th row of M.
# M should look like this:
#     (0 1 * 0 *)
#     (1 0 * 0 *)
# M = (0 0 0 1 *)
#     (0 0 0 0 0)
#     (0 0 0 0 0),
# i. e. "almost" in rref, but the rows do not have to be sorted.
# For a column c of M pivot_rows[c] should be the row with the pivot or 0.
# The function changes M, v and pivot_rows in place!
function _add_row_to_rref!(M::MatElem{T}, v::Vector{T}, pivot_rows::Vector{Int}, i::Int) where { T <: FieldElem }
  @assert ncols(M) == length(v)
  @assert ncols(M) == length(pivot_rows)
  @assert 1 <= i && i <= nrows(M)

  pivot_found = false
  pivot_col = 0
  s = one(base_ring(M))
  for c = 1:ncols(M)
    if iszero(v[c])
      continue
    end
    if pivot_rows[c] == 0
      # We found an entry in a column of v, where no other row of M has the pivot.
      if pivot_found
        # We already found a pivot
        continue
      end

      pivot_found = true
      pivot_col = c
      pivot_rows[c] = i
      continue
    end

    r = pivot_rows[c]
    # Reduce the entries of v by the row r of M
    t = -v[c] # we assume M[r, c] == 1 (it is the pivot)
    for j = c + 1:ncols(M)
      Mrj = M[r, j]
      if iszero(Mrj)
        continue
      end

      s = mul!(s, t, Mrj)
      v[j] = addeq!(v[j], s)
    end
    v[c] = zero!(v[c])
  end
  if !pivot_found
    return false
  end

  # Make the pivot 1
  t = inv(v[pivot_col])
  for j = pivot_col + 1:ncols(M)
    if iszero(v[j])
      continue
    end

    v[j] = mul!(v[j], v[j], t)
  end
  v[pivot_col] = one(base_ring(M))

  # Reduce the rows above the newly inserted one
  for r = 1:i - 1
    Mrp = M[r, pivot_col]
    if iszero(Mrp)
      continue
    end

    t = -Mrp
    for c = pivot_col + 1:ncols(M)
      s = mul!(s, t, v[c])
      M[r, c] = addeq!(M[r, c], s)
    end
    M[r, pivot_col] = zero(base_ring(M))
  end

  for c = 1:ncols(M)
    M[i, c] = deepcopy(v[c])
  end

  return true
end

@doc raw"""
    gens(A::AbstractAssociativeAlgebra, return_full_basis::Val = Val(false);
         thorough_search::Bool = false) where T
      -> Vector{AbstractAssociativeAlgebraElem}

Returns a subset of `basis(A)`, which generates $A$ as an algebra over
`base_ring(A)`.
If `return_full_basis` is set to `Val(true)`, the function also returns a
`Vector{AbstractAssociativeAlgebraElem}` containing a full basis consisting of monomials in
the generators and a `Vector{Vector{Tuple{Int, Int}}}` containing the
information on how these monomials are built. E. g.: If the function returns
`g`, `full_basis` and `v`, then we have
`full_basis[i] = prod( g[j]^k for (j, k) in v[i] )`.
If `thorough_search` is `true`, the number of returned generators is possibly
smaller. This will in general increase the runtime. It is not guaranteed that
the number of generators is minimal in any case.
"""
function gens(A::AbstractAssociativeAlgebra, ::Val{return_full_basis} = Val(false); thorough_search::Bool = false) where return_full_basis
  d = dim(A)
  if !return_full_basis
    if isdefined(A, :gens)
      return A.gens::Vector{elem_type(A)}
    end
  end

  if thorough_search
    # Sort the basis by the degree of the minpolys (hopefully those with higher
    # degree generate a "bigger" subalgebra)
    minpoly_degrees = [ (i, degree(minpoly(A[i]))) for i = 1:d ]
    sort!(minpoly_degrees, by = x -> x[2], rev = true)
  else
    is_gen = falses(d)
  end

  generators = Vector{elem_type(A)}()
  full_basis = elem_type(A)[ one(A) ] # Contains products of generators which form a full basis
  elts_in_gens = Vector{Tuple{Int, Int}}[ Tuple{Int, Int}[] ]
  B = zero_matrix(base_ring(A), d, d)
  pivot_rows = zeros(Int, d)
  new_elements = Set{Int}()

  s = one(A)
  t = one(A)

  cur_dim = 0
  cur_basis_elt = 1
  while cur_dim != d
    if isempty(new_elements)
      # We have to add a generator
      new_gen = A()
      new_elt = false
      while true
        if thorough_search
          i = minpoly_degrees[cur_basis_elt][1]
        else
          i = rand(1:dim(A))
          while is_gen[i]
            i = rand(1:dim(A))
          end
          is_gen[i] = true
        end
        new_gen = A[i]
        cur_basis_elt += 1
        new_elt = _add_row_to_rref!(B, coefficients(new_gen), pivot_rows, cur_dim + 1)
        if new_elt
          break
        end
      end
      push!(generators, new_gen)
      b = new_gen
      power = 1
      # Compute the powers of new_gen
      while new_elt
        cur_dim += 1
        push!(full_basis, b)
        if power == 1 && length(generators) != 1
          push!(new_elements, length(full_basis))
        end
        ind = Tuple{Int, Int}[ (length(generators), power) ]
        push!(elts_in_gens, ind)
        cur_dim == d ? break : nothing
        mul!(b, b, new_gen)
        power += 1
        new_elt = _add_row_to_rref!(B, coefficients(b), pivot_rows, cur_dim + 1)
      end
      continue
    else
      i = pop!(new_elements)
      b = full_basis[i]
    end

    # Compute all possible products involving b
    n = length(full_basis)
    for r = 1:n
      s = mul!(s, b, full_basis[r])
      for l = 1:n
        if !is_commutative(A)
          t = mul!(t, full_basis[l], s)
        else
          t = s
        end
        new_elt = _add_row_to_rref!(B, coefficients(t), pivot_rows, cur_dim + 1)
        if !new_elt
          continue
        end
        push!(full_basis, deepcopy(t))
        cur_dim += 1
        coord = _merge_elts_in_gens!(elts_in_gens[l], deepcopy(elts_in_gens[i]), elts_in_gens[r])
        push!(elts_in_gens, coord)
        if thorough_search && coord[1][2] == 1 && coord[end][2] == 1
          push!(new_elements, length(full_basis))
        end
        if is_commutative(A)
          break
        end
        cur_dim == d ? break : nothing
      end
      cur_dim == d ? break : nothing
    end
  end

  # Remove the one
  popfirst!(full_basis)
  popfirst!(elts_in_gens)

  if !isdefined(A, :gens)
    A.gens = generators
  end

  if return_full_basis
    return generators, full_basis, elts_in_gens
  else
    return generators
  end
end

################################################################################
#
#  Primitive elements
#
################################################################################

function primitive_element(A::AbstractAssociativeAlgebra)
  a, _ = _primitive_element(A)
  return a
end

function primitive_element(A::AbstractAssociativeAlgebra{QQFieldElem})
  if isdefined(A, :maps_to_numberfields)
    return primitive_element_via_number_fields(A)
  end
  a, _ = _primitive_element(A)
  return a
end

# TODO: Fix this with the types once a new version is released
#function _primitive_element(A::AbstractAssociativeAlgebra)
#  error("Not implemented yet")
#  return nothing
#end

# If T == QQFieldElem, we try to find a small primitive element by
# going "via number fields". There a procedure using LLL
# is implemented to find primitive elements with small minimal
# polynomial. Note that this could be improved by calling into
# simplify for number fields. But it is a bit tricky.
function _primitive_element(A::AbstractAssociativeAlgebra{QQFieldElem})
  a = primitive_element_via_number_fields(A)
  return a, minpoly(a)
end

function __primitive_element(A::S) where {T <: FinFieldElem, S <: AbstractAssociativeAlgebra{T}} #<: Union{zzModRingElem, FqPolyRepFieldElem, fqPolyRepFieldElem, EuclideanRingResidueRingElem{ZZRingElem}, QQFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, fpFieldElem}
  d = dim(A)
  a = rand(A)
  f = minpoly(a)
  while degree(f) < d
    a = rand(A)
    f = minpoly(a)
  end
  return a, f
end

function primitive_element_via_number_fields(A::AbstractAssociativeAlgebra{QQFieldElem})
  fields_and_maps = as_number_fields(A)
  a = A()
  for (K, AtoK) in fields_and_maps
    a += AtoK\gen(K)
  end
  return a
end

function _as_field(A::AbstractAssociativeAlgebra{T}) where T
  d = dim(A)
  a, mina = __primitive_element(A)
  b = one(A)
  M = zero_matrix(base_ring(A), d, d)
  elem_to_mat_row!(M, 1, b)
  for i in 1:(d - 1)
    b = mul!(b, b, a)
    elem_to_mat_row!(M, i + 1, b)
  end
  B = inv(M)
  N = zero_matrix(base_ring(A), 1, d)
  local f
  let N = N, B = B
    f = function(x)
      for i in 1:d
        N[1, i] = x.coeffs[i]
      end
      return N * B
    end
  end
  return a, mina, f
end

function _as_field_with_isomorphism(A::AbstractAssociativeAlgebra{QQFieldElem}) #<: Union{QQFieldElem, fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, fqPolyRepFieldElem, FqPolyRepFieldElem} }
  return _as_field_with_isomorphism(A, _primitive_element(A)...)
end

function _as_field_with_isomorphism(A::AbstractAssociativeAlgebra{S}) where { S } #<: Union{QQFieldElem, fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, fqPolyRepFieldElem, FqPolyRepFieldElem} }
  return _as_field_with_isomorphism(A, __primitive_element(A)...)
end

# Assuming a is a primitive element of A and mina its minimal polynomial, this
# functions constructs the field base_ring(A)/mina and the isomorphism between
# A and this field.
function _as_field_with_isomorphism(A::AbstractAssociativeAlgebra{S}, a::AbstractAssociativeAlgebraElem{S}, mina::T) where {S, T} # where { S <: Union{QQFieldElem, fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, fqPolyRepFieldElem, FqPolyRepFieldElem}, T <: Union{QQPolyRingElem, fpPolyRingElem, FpPolyRingElem, fqPolyRepPolyRingElem, FqPolyRepPolyRingElem} }
  s = one(A)
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  elem_to_mat_row!(M, 1, s)
  for i = 2:dim(A)
    s = mul!(s, s, a)
    elem_to_mat_row!(M, i, s)
  end

  return __as_field_with_isomorphism(A, mina, M)
end

function __as_field_with_isomorphism(A::AbstractAssociativeAlgebra{S}, f, M) where {S <: Union{QQFieldElem, AbsSimpleNumFieldElem}}
  K = number_field(f, cached = false)[1]
  return K, AbsAlgAssToNfAbsMor(A, K, inv(M), M)
end

function __as_field_with_isomorphism(A::AbstractAssociativeAlgebra{fpFieldElem}, f::fpPolyRingElem, M::fpMatrix)
  Fq = fqPolyRepField(f, Symbol("a"), false)
  return Fq, AbsAlgAssToFqMor(A, Fq, inv(M), M, parent(f))
end

function __as_field_with_isomorphism(A::AbstractAssociativeAlgebra{FpFieldElem}, f::FpPolyRingElem, M)
  Fq = FqPolyRepField(f, Symbol("a"), false)
  return Fq, AbsAlgAssToFqMor(A, Fq, inv(M), M, parent(f))
end

function __as_field_with_isomorphism(A::AbstractAssociativeAlgebra{FqFieldElem}, f::FqPolyRingElem, M::FqMatrix)
  Fr, = Nemo._residue_field(f)
  RtoFr = FqPolyRingToFqMor{typeof(parent(f)), typeof(Fr), typeof(f), Any}(Fr, f)
  return Fr, AbsAlgAssToFqMor(A, Fr, inv(M), M, parent(f), RtoFr)
end

function __as_field_with_isomorphism(A::AbstractAssociativeAlgebra{S}, f::T, M::U) where { S <: Union{fqPolyRepFieldElem, FqPolyRepFieldElem }, T <: Union{ fqPolyRepPolyRingElem, FqPolyRepPolyRingElem }, U <: Union{ fqPolyRepMatrix, FqPolyRepMatrix } }
  Fr, RtoFr = field_extension(f)
  return Fr, AbsAlgAssToFqMor(A, Fr, inv(M), M, parent(f), RtoFr)
end

################################################################################
#
#  Regular matrix algebra
#
################################################################################

@doc raw"""
    regular_matrix_algebra(A::Union{ StructureConstantAlgebra, GroupAlgebra }) -> MatAlgebra, AbsAlgAssMor

Returns the matrix algebra $B$ generated by the right representation matrices
of the basis elements of $A$ and a map from $B$ to $A$.
"""
function regular_matrix_algebra(A::Union{ StructureConstantAlgebra, GroupAlgebra })
  K = base_ring(A)
  B = matrix_algebra(K, [ representation_matrix(A[i], :right) for i = 1:dim(A) ], isbasis = true)
  return B, hom(B, A, identity_matrix(K, dim(A)), identity_matrix(K, dim(A)))
end

###############################################################################
#
#  Construction of a crossed product algebra
#
###############################################################################

function find_elem(G::Vector{T}, el::T) where T
  i=1
  while true
    if image_primitive_element(el) == image_primitive_element(G[i])
      return i
    end
    i+=1
  end
end


#K/Q is a Galois extension.
function CrossedProductAlgebra(K::AbsSimpleNumField, G::Vector{T}, cocval::Matrix{AbsSimpleNumFieldElem}) where T

  n=degree(K)
  m=length(G)
  #=
  Multiplication table
  I order the basis in this way:
  First, I put the basis of the Galois Group, then the product of them with the first
  element of basis of the order and so on...
  =#

  M=Array{QQFieldElem,3}(undef, n*m, n*m, n*m)
  for i=1:n*m
    for j=1:n*m
      for s=1:n*m
        M[i,j,s]=QQFieldElem(0)
      end
    end
  end
  B=basis(K)
  for i=1:n
    for j=1:m
      #I have the element B[i]*G[j]
      for k=1:n
        for h=1:m
          # I take the element B[k]*G[h]
          # and I take the product
          # B[i]*G[j]* B[k]*G[h]=B[i]*G[j](B[k])*c[j,h]*(G[j]*G[h])
          ind=find_elem(G,G[h] * G[j])
          x=B[i]*G[j](B[k])*cocval[j,h]
          #@show i, j, k,h,  ind,B[i],G[j](B[k]),cocval[j,h],  x
          for s=0:n-1
            M[j+(i-1)*n, h+(k-1)*n, ind+s*n]=coeff(x,s)
          end
          #@show M
        end
      end
    end
  end
  return StructureConstantAlgebra(FlintQQ, M)

end

function CrossedProductAlgebra(O::AbsSimpleNumFieldOrder, G::Vector{T}, cocval::Matrix{AbsSimpleNumFieldElem}) where T

  n=degree(O)
  m=length(G)
  K=nf(O)
  #=
  Multiplication table
  I order the basis in this way:
  First, I put the basis of the Galois Group, then the product of them with the first
  element of basis of the order and so on...
  =#

  M=Array{QQFieldElem,3}(undef, n*m, n*m, n*m)
  for i=1:n*m
    for j=1:n*m
      for s=1:n*m
        M[i,j,s]=QQFieldElem(0)
      end
    end
  end
  B = basis(O, copy = false)
  el = O(0)
  for j=1:m
    for k=1:n
      l =O(G[j](K(B[k])), false)
      for h=1:m
        ind = find_elem(G, G[h] * G[j])
        t = O(cocval[j,h], false)
        for i=1:n
          #I have the element B[i]*G[j]
          # I take the element B[k]*G[h]
          # and I take the product
          # B[i]*G[j]* B[k]*G[h]=B[i]*G[j](B[k])*c[j,h]*(G[j]*G[h])
          mul!(el, B[i], l)
          mul!(el, el, t)
          y = coordinates(el)
          for s=0:n-1
            M[j+(i-1)*m, h+(k-1)*m, ind+s*m] = y[s+1]
          end
        end
      end
    end
  end
  j1 = find_identity(G, *)
  j = find_elem(G, j1)
  O1 = QQFieldElem[0 for i=1:n*m]
  O1[j] = QQFieldElem(1)
  A = StructureConstantAlgebra(FlintQQ, M, O1)
  A.is_simple = 1
  return A

end

###############################################################################
#
#  Trace Matrix
#
###############################################################################

function _assure_trace_basis(A::AbstractAssociativeAlgebra{T}) where T
  if isdefined(A, :trace_basis_elem)
    return nothing
  end

  mt = multiplication_table(A, copy = false)
  A.trace_basis_elem = Vector{T}(undef, dim(A))
  for i = 1:dim(A)
    A.trace_basis_elem[i] = sum(mt[i, j, j] for j = 1:dim(A))
  end
  return nothing
end

@doc raw"""
    trace_matrix(A::AbstractAssociativeAlgebra) -> MatElem

Returns a matrix $M$ over the base ring of $A$ such that
$M_{i, j} = \mathrm{tr}(b_i \cdot b_j)$, where $b_1, \dots, b_n$ is the
basis of $A$.
"""
function trace_matrix(A::AbstractAssociativeAlgebra, tr = tr)
  F = base_ring(A)
  n = dim(A)
  M = zero_matrix(F, n, n)
  for i = 1:n
    M[i, i] = tr(A[i]^2)
  end
  for i = 1:n
    for j = i + 1:n
      x = tr(A[i]*A[j])
      M[i, j] = x
      M[j, i] = x
    end
  end
  return M
end

################################################################################
#
#  Change of ring
#
################################################################################

# This is the generic fallback which constructs an associative algebra
@doc raw"""
    restrict_scalars(A::AbstractAssociativeAlgebra{AbsSimpleNumFieldElem}, Q::QQField)
    restrict_scalars(A::AbstractAssociativeAlgebra{fqPolyRepFieldElem}, Fp::fpField)
    restrict_scalars(A::AbstractAssociativeAlgebra{FqPolyRepFieldElem}, Fp::EuclideanRingResidueField{ZZRingElem})
      -> StructureConstantAlgebra, Function, Function

Given an algebra $A$ over a field $L$ and the prime field $K$ of $L$, this
function returns the restriction $B$ of $A$ to $K$ and maps from $A$ to $B$
and from $B$ to $A$.
"""
function restrict_scalars(A::AbstractAssociativeAlgebra{T}, K::Field) where {T}
  #K == base_ring(A) && error("Not yet implemented")
  B, BtoA = StructureConstantAlgebra(A)::Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}
  C, BtoC, CtoB = restrict_scalars(B, K)

  function CtoA(x::AbstractAssociativeAlgebraElem)
    @assert parent(x) === C
    return BtoA(CtoB(x))
  end

  function AtoC(x::AbstractAssociativeAlgebraElem)
    @assert parent(x) === A
    return BtoC(BtoA\x)
  end

  return C, AtoC, CtoA
end

################################################################################
#
#  is_simple
#
################################################################################

function is_semisimple(A::AbstractAssociativeAlgebra)
  b = _issemisimple(A)
  @assert b == 1 || b == 2
  return b == 1
end

function _issemisimple(A::AbstractAssociativeAlgebra{T}) where { T } #<: Union{ fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, FqPolyRepFieldElem, fqPolyRepFieldElem, QQFieldElem, AbsSimpleNumFieldElem } }
  if A.issemisimple == 0
    if isempty(_radical(A))
      A.issemisimple = 1
    else
      A.issemisimple = 2
    end
  end

  return A.issemisimple
end

is_simple_known(A::AbstractAssociativeAlgebra) = A.is_simple != 0

function is_simple(A::AbstractAssociativeAlgebra)
  if A.is_simple != 0
    return A.is_simple == 1
  end

  if _issemisimple(A) == 2
    A.is_simple = 2
    return false
  end
  # Still can't be certain that A is semisimple, since _issemisimple does not
  # always work...

  Adec = decompose(A)
  if length(Adec) == 1
    A.is_simple = 1
    return true
  end
  A.is_simple = 2
  return false
end

################################################################################
#
#  Etale
#
################################################################################

function is_etale(A::AbstractAssociativeAlgebra)
  return is_commutative(A) && is_semisimple(A)
end

################################################################################
#
#  Trace signature
#
################################################################################

function trace_signature(A::AbstractAssociativeAlgebra{AbsSimpleNumFieldElem}, P::InfPlc)
  M = trred_matrix(basis(A))
  Ky, y = polynomial_ring(base_ring(A), "y", cached = false)
  f = charpoly(Ky, M)
  npos = n_positive_roots(f, _embedding(P); multiplicities = true)
  return (npos, degree(f) - npos)
end

function trace_signature(A::AbstractAssociativeAlgebra{QQFieldElem})
  O = get_attribute(A, :any_order)
  if O === nothing
    M = trred_matrix(basis(A))
  else
    _M = trred_matrix(O::order_type(A))
    M = change_base_ring(QQ, _M)
  end

  Ky, y = polynomial_ring(base_ring(A), "y", cached = false)
  f = charpoly(Ky, M)
  npos = n_positive_roots(f, multiplicities = true)
  return npos, degree(f) - npos
end

################################################################################
#
#  Transport of Wedderburn decompositions
#
################################################################################

# Given epimorphism h : A -> B, transport the refined wedderburn decomposition
# of A to B
function _transport_refined_wedderburn_decomposition_forward(h::AbsAlgAssMor; is_anti::Bool = false)
  # is_anti = h is anti-morphism
  A = domain(h)
  B = codomain(h)

  if get_attribute(B, :refined_wedderburn, false)
    return true
  end

  _assert_has_refined_wedderburn_decomposition(A)
  dec = decompose(A)
  T = StructureConstantAlgebra{elem_type(base_ring(B))}
  new_dec = Tuple{T, morphism_type(T, typeof(B))}[]
  k = 0
  # We have to be very careful not to change the decomposition of B if it
  # already has one
  if !isdefined(B, :decomposition)
    _ = decompose(B)
  end
  #for (C, CtoA) in dec
  #  e = h(CtoA(one(C)))
  #  if !iszero(e)
  #    CtoB = compose_and_squash(h, CtoA)
  #    push!(new_dec, (C, CtoB))
  #    k += dim(C)
  #  end
  #end
  #@assert dim(B) == k
  #B.decomposition = new_dec

  for (Bc, BctoB) in B.decomposition
    for (C, CtoA) in dec
      e = BctoB\(h(CtoA(one(C))))
      if !iszero(e)
        M = basis_matrix([BctoB\(h(CtoA(b))) for b in basis(C)])
        CtoBc = hom(C, Bc, M, inv(M))
        if isdefined(C, :isomorphic_full_matrix_algebra)
          CM, CtoCM = C.isomorphic_full_matrix_algebra
          #bmat = basis_matrix([CM(transpose(matrix(x)), check = false) for x in basis(CM)])
          #ff = hom(CM, CM, bmat, inv(bmat))
          f = AbsAlgAssMorGen(Bc, CM, inv(CtoBc).mat * CtoCM.M, CtoCM.Minv * CtoBc.mat)
          if is_anti
            BB = matrix([coefficients(CM(transpose(matrix(f(b))), check = false)) for b in basis(Bc)])
            BBinv = matrix([coefficients(preimage(CtoCM, CM(transpose(matrix(b)), check = false))) for b in _absolute_basis(CM)])
            #BBinv = inv(BB)
            f = AbsAlgAssMorGen(Bc, CM, BB, BBinv)
          end
          Bc.isomorphic_full_matrix_algebra = CM, f
        end
      end
    end
  end
  set_attribute!(B, :refined_wedderburn, true)
  return true
end

################################################################################
#
#  Projection onto component
#
################################################################################

@doc raw"""
    product_of_components_with_projection(A::AbstractAssociativeAlgebra, a::Vector{Int})
                                                               -> AbstractAssociativeAlgebra, Map

Return the direct product of the simple components of $A$ specified by `a`
together with the canonical projection, where the ordering is with respect to
the ordering returned by `decompose(A)`.
"""
function product_of_components_with_projection(A::AbstractAssociativeAlgebra, a::Vector{Int})
  dec = decompose(A)
  l = length(dec)
  @req all(i -> 1 <= i <= l, a) "Indices ($a) must satisfy >= 1 and <= $l"
  algs = [dec[i][1] for i in a]
  injs = [dec[i][2] for i in a]
  r = length(a)
  B, injstoB = direct_product(base_ring(A), algs)
  imgs = elem_type(B)[]
  for b in basis(A)
    push!(imgs, sum(injstoB[i](injs[i]\b) for i in eachindex(a); init = zero(B)))
  end
  p = hom(A, B, basis_matrix(imgs))
  _transport_refined_wedderburn_decomposition_forward(p)
  return B, p
end
#function product_of_components(A::AbstractAssociativeAlgebra)

@doc raw"""
    product_of_components_with_projection(A::AbstractAssociativeAlgebra, a::Vector{Int})
                                                                   -> AbstractAssociativeAlgebra

Return the direct product of the simple components of $A$ specified by `a`, where
the ordering is with respect to the ordering returned by `decompose(A)`.
"""
function product_of_components(A::AbstractAssociativeAlgebra, a::Vector{Int})
  B, = product_of_components(A, a)
  return B
end

@doc raw"""
    maximal_eichler_quotient_with_projection(A::AbstractAssociativeAlgebra) -> AbstractAssociativeAlgebra, Map
"""
function maximal_eichler_quotient_with_projection(A::AbstractAssociativeAlgebra)
  v = Int[]
  dec = decompose(A)
  for i in 1:length(dec)
    B, = Hecke._as_algebra_over_center(dec[i][1])
    if !is_eichler(B)
      push!(v, i)
    end
  end
  return product_of_components_with_projection(A, v)
end

################################################################################
#
#  Central primitive idempotents
#
################################################################################

@doc raw"""
    central_primitive_idempotents(A::AbstractAssociativeAlgebra) -> Vector

Returns the central primitive idempotents of `A`.

```jldoctest
julia> G = small_group(5, 1);

julia> QG = QQ[G];

julia> length(central_primitive_idempotents(QG))
2
```
"""
function central_primitive_idempotents(A::AbstractAssociativeAlgebra)
  dec = decompose(A)
  res = Vector{elem_type(A)}(undef, length(dec))
  for i in 1:length(dec)
    B, BtoA = dec[i]
    res[i] = BtoA(one(B))
  end
  return res
end
