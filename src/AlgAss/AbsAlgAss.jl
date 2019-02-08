################################################################################
#
#  Morphism types
#
################################################################################

morphism_type(::Type{T}, ::Type{S}) where {R, T <: AbsAlgAss{R}, S <: AbsAlgAss{R}} = AbsAlgAssMor{T, S, Generic.Mat{R}}

morphism_type(::Type{T}, ::Type{S}) where {R, T <: AbsAlgAss{fmpq}, S <: AbsAlgAss{fmpq}} = AbsAlgAssMor{T, S, fmpq_mat}

morphism_type(::Type{T}, ::Type{S}) where {R, T <: AbsAlgAss{fq}, S <: AbsAlgAss{fq}} = AbsAlgAssMor{T, S, fq_mat}

morphism_type(::Type{T}, ::Type{S}) where {R, T <: AbsAlgAss{fq_nmod}, S <: AbsAlgAss{fq_nmod}} = AbsAlgAssMor{T, S, fq_nmod_mat}

morphism_type(::Type{T}, ::Type{S}) where {R, T <: AbsAlgAss{nmod}, S <: AbsAlgAss{nmod}} = AbsAlgAssMor{T, S, nmod_mat}

morphism_type(::Type{T}, ::Type{S}) where {R, T <: AbsAlgAss{gfp_elem}, S <: AbsAlgAss{gfp_elem}} = AbsAlgAssMor{T, S, gfp_mat}

morphism_type(A::Type{T}) where {T <: AbsAlgAss} = morphism_type(A, A)

################################################################################
#
#  Basis
#
################################################################################

function basis(A::AbsAlgAss)
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
  return B
end

################################################################################
#
#  Predicates
#
################################################################################

issimple_known(A::AbsAlgAss) = A.issimple != 0

################################################################################
#
#  Associativity, Distributivity test
#
################################################################################

function check_associativity(A::AbsAlgAss)
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

function check_distributivity(A::AbsAlgAss)
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
#  Dimension of center
#
################################################################################

function dimension_of_center(A::AbsAlgAss)
  C, _ = center(A)
  return dim(C)
end


################################################################################
#
#  Subalgebras
#
################################################################################

# Constructs the algebra e*A
# This is the generic fallback which constructs an associative algebra
function subalgebra(A::AbsAlgAss{T}, e::AbsAlgAssElem{T}, idempotent::Bool = false) where {T}
  @assert parent(e) == A
  B, mB = AlgAss(A)
  C, mC = subalgebra(B, mB\e, idempotent)
  mD = compose_and_squash(mB, mC)
  @assert domain(mD) == C
  return C, mD
end

function subalgebra(A::AbsAlgAss{T}, basis::Array{S}) where {T, S}
  B, mB = AlgAss(A)
  basis_pre = elem_type(B)[mB\(basis[i]) for i in 1:length(basis)]
  C, mC = subalgebra(B, basis_pre)
  mD = compose_and_squash(mB, mC)
  @assert domain(mD) == C
  return C, mD
end

################################################################################
#
#  Trace matrix
#
################################################################################

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


################################################################################
#
#  Decomposition of algebras
#
################################################################################

# Assume that A is a commutative algebra over a finite field of cardinality q.
# This functions computes a basis for ker(x -> x^q).
function kernel_of_frobenius(A::AbsAlgAss)
  F = base_ring(A)
  q = order(F)

  b = A()
  c = A()
  B = zero_matrix(F, dim(A), dim(A))
  for i = 1:dim(A)
    b.coeffs[i] = F(1)
    if i > 1
      b.coeffs[i - 1] = F()
    end
    c = b^q - b
    for j = 1:dim(A)
      B[j, i] = deepcopy(c.coeffs[j])
    end
  end

  V = right_kernel(B)
  return [ A(v) for v in V ]
end


################################################################################
#
#  Decomposition
#
################################################################################

@doc Markdown.doc"""
***
    decompose(A::AbsAlgAss{T}) -> AlgAss{T}

> Given a semisimple algebra over a field, this function 
> returns a decomposition of A as a direct sum of simple algebras.
"""
function decompose(A::AbsAlgAss{T}) where {T}
  if isdefined(A, :decomposition)
    return A.decomposition::Vector{Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(A))}}
  end

  if issimple_known(A) && A.issimple == 1
    B, mB = AlgAss(A)
    res = Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(A))}[(B, mB)]
  end

  if A isa AlgAss
    D = _decompose(A)
    return D
  end

  if A isa AlgGrp
    B, mB = AlgAss(A)
    D = _decompose(B)
    res = Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(A))}[]
    for (S, mS) in D
      mD = compose_and_squash(mB, mS)
      push!(res, (S, mD))
    end
    A.decomposition = res
    return res
  end
end

function _decompose(A::AbsAlgAss{T}) where {T}
  if iscommutative(A)
    res = _dec_com(A)
  else
    res = _dec_via_center(A)
  end

  A.decomposition = res
  return res
end

function _dec_via_center(A::S) where {T, S <: AbsAlgAss{T}}
  ZA, mZA = center(A)
  Algs = _dec_com(ZA)
  res = Tuple{AlgAss{T}, morphism_type(AlgAss{T}, S)}[ subalgebra(A, mZA(BtoZA(one(B))), true) for (B, BtoZA) in Algs]
  for i in 1:length(res)
    res[i][1].issimple = 1
  end
  A.decomposition = res
  return res
end

function _dec_com(A::AbsAlgAss)
  if characteristic(base_ring(A)) > 0
    return _dec_com_finite(A)
  else
    return _dec_com_gen(A)
  end
end

function _dec_com_gen(A::AbsAlgAss{T}) where {T <: FieldElem}
  if dim(A) == 1
    A.issimple = 1
    B, mB = AlgAss(A)
    return Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(A))}[(B, mB)]
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

    if degree(f) == dim(A) && isirreducible(f)
      A.issimple = 1
      B, mB = AlgAss(A)
      return Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(A))}[(B, mB)]
    end

    @assert issquarefree(f)

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

    A.issimple = 2

    res = Vector{Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(A))}}()
    for idem in idems
      S, StoA = subalgebra(A, idem, true)
      decS = _dec_com_gen(S)
      for (B, BtoS) in decS
        BtoA = compose_and_squash(StoA, BtoS)
        push!(res, (B, BtoA))
      end
    end
    return res
  end
end


function _dec_com_finite(A::AbsAlgAss{T}) where T
  if dim(A) == 1
    A.issimple = 1
    B, mB = AlgAss(A)
    return [(B, mB)]
  end

  F = base_ring(A)
  @assert !iszero(characteristic(F))
  V = kernel_of_frobenius(A)
  k = length(V)

  if k == 1
    A.issimple = 1
    B, mB = AlgAss(A)
    return [(B, mB)]
  end
  
  A.issimple = 2

  while true
    c = elem_type(F)[ rand(F) for i = 1:k ]
    a = dot(c, V)
    f = minpoly(a)

    if degree(f) < 2
      continue
    end

    @assert issquarefree(f)

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
      s = crt(right_side, factorss)
      sols[i] = s
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

    res = Vector{Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(A))}}()
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
end

################################################################################
#
#  Decomposition as number fields
#
################################################################################

function as_number_fields(A::AbsAlgAss{fmpq})
  if isdefined(A, :maps_to_numberfields)
    return A.maps_to_numberfields::Vector{Tuple{AnticNumberField, AbsAlgAssToNfAbsMor{typeof(A), elem_type(A)}}}
  end

  d = dim(A)

  Adec = decompose(A)

  # Compute a LLL reduced basis of the maximal order of A to find "small"
  # polynomials for the number fields.
  OA = maximal_order(A)
  L = lll(basis_mat(OA, Val{false}).num)
  n = basis_mat(OA, Val{false}).den
  basis_lll = [ elem_from_mat_row(A, L, i, n) for i = 1:d ]

  M = zero_matrix(FlintQQ, 0, d)
  matrices = Vector{fmpq_mat}()
  fields = Vector{AnticNumberField}()
  for i = 1:length(Adec)
    # For each small algebra construct a number field and the isomorphism
    B, BtoA = Adec[i]
    dB = dim(B)
    local K, BtoK
    found_field = false # Only for debugging
    for j = 1:d
      t = BtoA\basis_lll[j]
      mint = minpoly(t)
      if degree(mint) == dB
        found_field = true
        K, BtoK = _as_field_with_isomorphism(B, t, mint)
        push!(fields, K)
        break
      end
    end
    @assert found_field "This should not happen..."

    # Construct the map from K to A
    N = zero_matrix(FlintQQ, degree(K), d)
    for j = 1:degree(K)
      t = BtoA(BtoK\basis(K)[j])
      elem_to_mat_row!(N, j, t)
    end
    push!(matrices, N)
    M = vcat(M, N)
  end
  @assert nrows(M) == d

  invM = inv(M)
  matrices2 = Vector{fmpq_mat}(undef, length(matrices))
  offset = 1
  for i = 1:length(matrices)
    r = nrows(matrices[i])
    N = sub(invM, 1:d, offset:(offset + r - 1))
    matrices2[i] = N
    offset += r
  end

  result = Vector{Tuple{AnticNumberField, AbsAlgAssToNfAbsMor{typeof(A), elem_type(A)}}}()
  for i = 1:length(fields)
    push!(result, (fields[i], AbsAlgAssToNfAbsMor(A, fields[i], matrices2[i], matrices[i])))
  end
  A.maps_to_numberfields = result
  return result
end

################################################################################
#
#  Random elements
#
################################################################################

function rand(A::AbsAlgAss{T}) where T
  c = T[rand(base_ring(A)) for i = 1:dim(A)]
  return A(c)
end

function rand(A::AbsAlgAss{T}, rng::UnitRange{Int}) where T
  c = T[rand(base_ring(A), rng) for i = 1:dim(A)]
  return A(c)
end

function rand(A::AlgAss{fmpq}, rng::UnitRange{Int} = -20:20)
  c = [fmpq(rand(FlintZZ, rng)) for i = 1:dim(A)]
  return A(c)
end

################################################################################
#
#  Compute generators
#
################################################################################

function _reduce(M, v)
  cur_ind = 0
  for outer cur_ind in 1:ncols(M)
    if !iszero(v[cur_ind])
      break
    end
  end
end

function gens(A::AbsAlgAss)
  d = dim(A)
  K = base_ring(A)

  b = rand(A)
  while iszero(b)
    b = rand(A)
  end

  cur_gen = elem_type(A)[b]

  current_dim = -1

  B = zero_matrix(K, d, d)

  for k in 1:d
    B[1, k] = b.coeffs[k]
  end

  cur_dim = 1

  new_dim = 0

  if d == 1
    return cur_gen
  end

  l = 0

  t_gens = copy(cur_gen)

  while true
    l = l + 1
    while true
      t_gens = copy(cur_gen)
      t = length(t_gens)
      for i in 1:t
        for j in 1:t
          c = t_gens[i] * t_gens[j]
          for k in 1:d
            B[d, k] = c.coeffs[k]
          end
          new_dim = _rref!(B)
          if new_dim == d
            return cur_gen
          elseif new_dim > cur_dim
            cur_dim = new_dim
            push!(t_gens, c)
          end
        end
      end

      if cur_dim == new_dim
        break
      else
        cur_dim = new_dim
        B = new_B
      end
    end

    if cur_dim == d
      break
    else
      b = rand(A)
      while iszero(b)
        b = rand(A)
      end
      push!(cur_gen, b)
    end
  end

  return cur_gen
end


