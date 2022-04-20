################################################################################
#
#  Ramification
#
################################################################################

export schur_index, is_eichler

################################################################################
#
#  Is split
#
################################################################################

@doc Markdown.doc"""
    is_split(A::AbsAlgAss, p) -> Bool

Return whether the $\mathbf{Q}$-algebra $A$ is split at $p$. The object $p$ can be an integer or `inf`.
"""
function is_split(A::AbsAlgAss, p)
  return schur_index(A, p) == 1
end

@doc Markdown.doc"""
    is_split(A::AlgAss{fmpq}) -> Bool

Given a central $\mathbf{Q}$-algebra $A$, return `true` if $A$ splits.
"""
function is_split(A::AbsAlgAss{fmpq})
  i = schur_index(A, inf)
  if i == 2
    @vprint :AlgAssOrd 1 "Not split at the infinite prime\n"
    return false
  end
  O = any_order(A)
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

function is_split(A::AbsAlgAss{nf_elem})
  K = base_ring(A)
  for p in infinite_places(K)
    if !is_split(A, p)
      return false
    end
  end
  O1 = maximal_order(A)
  return isone(discriminant(O1))
end

function is_split(A::AbsAlgAss, P::InfPlc)
  if iscomplex(P)
    return true
  end
  return schur_index(A, P) == 1
end

################################################################################
#
#  Ramified infinite places
#
################################################################################

function ramified_infinite_places(A::AlgAss{nf_elem})
  K = base_ring(A)
  inf_plc = Vector{InfPlc}()
  places = real_places(K)
  for p in places
    if !is_split(A, p)
      push!(inf_plc, p)
    end
  end

  return inf_plc
end

function ramified_infinite_places_of_center(A::AbsAlgAss)
  dec = decompose(A)
  C, = center(A)
  res = Vector{InfPlc}[]
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

@doc Markdown.doc"""
   schur_index(A::AlgAss{fmpq}, p::Union{IntegerUnion, PosInf}) -> Int

Determine the Schur index of $A$ at $p$, where $p$ is either a prime or `inf`.
"""
schur_index(A::AbsAlgAss{fmpq}, ::Union{IntegerUnion, PosInf})

function schur_index(A::AbsAlgAss{fmpq}, ::PosInf)
  @req iscentral(A) "Algebra must be central"
  @req issimple(A) "Algebra must be simple"

  if dim(A) % 4 != 0
    return 1
  end

  x = trace_signature(A)
  n = root(dim(A), 2)
  if x[1] == divexact(n * (n + 1), 2)
    return 1
  else
    return 2
  end
end

function schur_index(A::AbsAlgAss{nf_elem}, P::InfPlc)
  @req iscentral(A) "Algebra must be central"
  @req issimple(A) "Algebra must be simple"

  if dim(A) % 4 != 0
    return 1
  end

  x = trace_signature(A, P)
  n = root(dim(A), 2)
  if x[1] == divexact(n * (n + 1),2)
    return 1
  else
    return 2
  end
end

#  Schur Index at p

function schur_index(A::AbsAlgAss, p::IntegerUnion)
  @req iscentral(A) "Algebra must be central"
  @req issimple(A) "Algebra must be simple"

  d = discriminant(maximal_order(A))
  v = valuation(d, p)
  if v == 0
    return 1
  end
  s = root(dim(A), 2)
  t = s - divexact(v, s)
  return divexact(s, t)
end

function schur_index(A::AbsAlgAss{<: NumFieldElem}, p::NumFieldOrdIdl)
  @req iscentral(A) "Algebra must be central"
  @req issimple(A) "Algebra must be simple"

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

function schur_index(A::AbsAlgAss{fmpq})
  e = schur_index(A, inf)
  for p in prime_divisors(discriminant(maximal_order(A)))
    e = lcm(e, schur_index(A, p))
  end
  return e
end

function schur_index(A::AbsAlgAss{<: NumFieldElem})
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

# Tests whether A fulfils the Eichler condition relative to the maximal Z-order
# of base_ring(A)
function is_eichler(A::AbsAlgAss{nf_elem})
  @assert issimple(A)
  @assert iscentral(A)

  if !istotally_real(base_ring(A))
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

function is_eichler(A::AbsAlgAss{fmpq})
  @assert issimple(A)
  @assert iscentral(A)
  if dim(A) != 4
    return true
  end
  O = Order(A, basis(A))
  return schur_index(A, inf) == 1
end
