################################################################################
#
#  Ramification
#
################################################################################

################################################################################
#
#  Is split
#
################################################################################

@doc raw"""
    is_split(A::AbstractAssociativeAlgebra, p) -> Bool

Return whether the $\mathbf{Q}$-algebra $A$ is split at $p$. The object $p$ can be an integer or `inf`.
"""
function is_split(A::AbstractAssociativeAlgebra, p)
  return schur_index(A, p) == 1
end

@doc raw"""
    is_split(A::StructureConstantAlgebra{QQFieldElem}) -> Bool

Given a central $\mathbf{Q}$-algebra $A$, return `true` if $A$ splits.
"""
function is_split(A::AbstractAssociativeAlgebra{QQFieldElem})
  i = schur_index(A, inf)
  if i == 2
    @vprintln :AlgAssOrd 1 "Not split at the infinite prime"
    return false
  end
  O = any_order(A)
  fac = factor(root(abs(discriminant(O)),2))
  for (p,j) in fac
    O1 = pmaximal_overorder(O, Int(p))
    if valuation(discriminant(O1), Int(p)) != 0
      @vprintln :AlgAssOrd 1 "Not split at $p"
      return false
    end
  end
  return true
end

function is_split(A::AbstractAssociativeAlgebra{AbsSimpleNumFieldElem})
  K = base_ring(A)
  for p in infinite_places(K)
    if !is_split(A, p)
      return false
    end
  end
  O1 = maximal_order(A)
  return isone(discriminant(O1))
end

function is_split(A::AbstractAssociativeAlgebra, P::InfPlc)
  if is_complex(P)
    return true
  end
  return schur_index(A, P) == 1
end

################################################################################
#
#  Ramified infinite places
#
################################################################################

function ramified_infinite_places(A::StructureConstantAlgebra{AbsSimpleNumFieldElem})
  K = base_ring(A)
  inf_plc = Vector{InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}}()
  places = real_places(K)
  for p in places
    if !is_split(A, p)
      push!(inf_plc, p)
    end
  end

  return inf_plc
end

function ramified_infinite_places_of_center(A::AbstractAssociativeAlgebra)
  dec = decompose(A)
  C, = center(A)
  res = Vector{InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}}[]
  for i in 1:length(dec)
    K, = component(Field, C, i)
    B, = _as_algebra_over_center(dec[i][1])
    plcs = ramified_infinite_places(B)
    L = base_ring(B)
    fl, f = is_isomorphic_with_map(L, K)
    @assert fl
    push!(res, [induce_image(f, p) for p in plcs])
  end

  return res
end

################################################################################
#
#  Schur indices
#
################################################################################

# We follow
# Nebe--Steel, "Recognition of division algebras",
# https://doi.org/10.1016/j.jalgebra.2009.04.026

@doc raw"""
   schur_index(A::StructureConstantAlgebra{QQFieldElem}, p::Union{IntegerUnion, PosInf}) -> Int

Determine the Schur index of $A$ at $p$, where $p$ is either a prime or `inf`.
"""
schur_index(A::AbstractAssociativeAlgebra{QQFieldElem}, ::Union{IntegerUnion, PosInf})

function schur_index(A::AbstractAssociativeAlgebra{QQFieldElem}, ::PosInf)
  @req is_central(A) "Algebra must be central"
  @req is_simple(A) "Algebra must be simple"

  dim(A) % 4 == 0 || return 1

  x, = trace_signature(A)
  n = root(dim(A), 2)
  if x == divexact(n * (n+1), 2)
    return 1
  else
    @assert x == divexact(n * (n-1), 2)
    return 2
  end
end

function schur_index(A::AbstractAssociativeAlgebra{AbsSimpleNumFieldElem}, P::InfPlc)
  @req is_central(A) "Algebra must be central"
  @req is_simple(A) "Algebra must be simple"

  dim(A) % 4 == 0 && is_real(P) || return 1

  x, = trace_signature(A, P)
  n = root(dim(A), 2)
  if x == divexact(n * (n+1), 2)
    return 1
  else
    @assert x == divexact(n * (n-1), 2)
    return 2
  end
end

#  Schur Index at p

function schur_index(A::AbstractAssociativeAlgebra, p::IntegerUnion)
  @req is_central(A) "Algebra must be central"
  @req is_simple(A) "Algebra must be simple"

  d = discriminant(maximal_order(A))
  v = valuation(d, p)
  if v == 0
    return 1
  end
  s = root(dim(A), 2)
  t = s - divexact(v, s)
  return divexact(s, t)
end

function schur_index(A::AbstractAssociativeAlgebra{<: NumFieldElem}, p::NumFieldOrderIdeal)
  @req is_central(A) "Algebra must be central"
  @req is_simple(A) "Algebra must be simple"

  M = maximal_order(A)
  d = discriminant(maximal_order(A))
  @req order(p) === base_ring(M) "Prime ideal of wrong order"
  v = valuation(d, p)
  if v == 0
    return 1
  end
  s = root(dim(A), 2)
  t = s - divexact(v, s)
  return divexact(s, t)
end

function schur_index(A::AbstractAssociativeAlgebra{QQFieldElem})
  e = schur_index(A, inf)
  for p in prime_divisors(discriminant(maximal_order(A)))
    e = lcm(e, schur_index(A, p))
  end
  return e
end

function schur_index(A::AbstractAssociativeAlgebra{<: NumFieldElem})
  rlp = infinite_places(base_ring(A))
  e = schur_index(A, rlp[1])
  for i in 2:length(rlp)
    e = lcm(e, schur_index(A, rlp[i]))
  end
  for (p, _) in factor(discriminant(maximal_order(A)))
    e = lcm(e, schur_index(A, p))
  end
  return e
end

################################################################################
#
#  Eichler condition
#
################################################################################

function is_eichler(A::AbstractAssociativeAlgebra)
  if is_simple(A) && is_central(A)
    return _is_eichler_csa(A)
  end
  d = decompose(A)
  for (B, _) in d
    BC, = _as_algebra_over_center(B)
    if !_is_eichler_csa(BC)
      return false
    end
  end
  return true
end

# Tests whether A fulfils the Eichler condition relative to the maximal Z-order
# of base_ring(A)
function _is_eichler_csa(A::AbstractAssociativeAlgebra{AbsSimpleNumFieldElem})
  @assert is_simple(A)
  @assert is_central(A)

  if !is_totally_real(base_ring(A))
    return true
  end

  if dim(A) != 4
    return true
  end

  K = base_ring(A)
  places = real_places(K)
  for p in places
    if is_split(A, p)
      return true
    end
  end
  return false
end

function _is_eichler_csa(A::AbstractAssociativeAlgebra{QQFieldElem})
  @assert is_simple(A)
  @assert is_central(A)
  if dim(A) != 4
    return true
  end
  O = Order(A, basis(A))
  return schur_index(A, inf) == 1
end
