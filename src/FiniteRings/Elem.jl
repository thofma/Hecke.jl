################################################################################
#
#  Ring interface functions
#
################################################################################

function is_exact_type(::Type{FiniteRingElem})
  return true
end

parent(x::FiniteRingElem) = x.parent

function data(a::FiniteRingElem)
  return a.a
end

################################################################################
#
#  Copy
#
################################################################################

function Base.deepcopy_internal(x::FiniteRingElem, stackdict::IdDict)
  return FiniteRingElem(parent(x), Base.deepcopy_internal(data(x), stackdict))
end

function Base.hash(x::FiniteRingElem, h::UInt)
  return Base.hash(data(x), h)
end

Base.copy(x::FiniteRingElem) = x

################################################################################
#
#  Printing
#
################################################################################

function Base.show(io::IO, a::FiniteRingElem)
  # same as FinGenGrpAbElem, but with different prefix
  a = data(a)
  if get(io, :compact, false) || AbstractAlgebra.is_terse(io) || (get(io, :typeinfo, Any)) == typeof(a)
    print(io, "[", join(a.coeff, ", "), "]")
    return
  end

  print(io, "Finite ring element [", join(a.coeff, ", "), "]")
end

################################################################################
#
#  Element creation
#
################################################################################

(R::FiniteRing)() = zero(R)

(R::FiniteRing)(a::IntegerUnion) = FiniteRingElem(R, a * data(one(R)))

(R::FiniteRing)(x::Vector) = FiniteRingElem(R, underlying_abelian_group(R)(x))

function (R::FiniteRing)(x::FiniteRingElem)
  @req parent(x) === R "Coercion only allowed if parent and ring are equal"
  return x
end

# zero
function zero(R::FiniteRing)
  return FiniteRingElem(R, zero(underlying_abelian_group(R)))
end

# one
function one(R::FiniteRing)
  # we cache the one, because it is expensive to compute
  if isdefined(R, :one)
    return (R.one)::FiniteRingElem
  end
  A = underlying_abelian_group(R)
  B, Btohoms = hom(A, A)
  S, StoB = sub(B, [Btohoms\(R.mult[i]) for i in 1:length(R.mult)])
  fl, x = has_preimage_with_preimage(StoB, Btohoms\(id_hom(A)))
  fl || error("Ring does not have multiplicative identity")
  o = R([c for c in x.coeff[1,:]])
  R.one = o
  return o::FiniteRingElem
end

function is_invertible(a::FiniteRingElem)
  if isassigned(a.inv::Base.RefValue{FiniteRingElem})
    return true, a.inv[]::FiniteRingElem
  end
  R = parent(a)
  Z = free_abelian_group(length(R.mult))
  f = hom(Z, R.A, [R.mult[i](a.a) for i in 1:length(R.mult)])
  fl, o = has_preimage_with_preimage(f, one(R).a)
  if fl
    ainv = R([c for c in o.coeff[1, :]])
    a.inv[] = ainv
    return true, ainv
  else
    return false, a
  end
end

function is_unit(a::FiniteRingElem)
  return is_invertible(a)[1]
end

ConformanceTests.generate_element(R::FiniteRing) = rand(R)

################################################################################
#
#  Arithmetic
#
################################################################################

function inv(a::FiniteRingElem)
  fl, ainv = is_invertible(a)
  @req fl "Element is not invertible"
  return ainv::FiniteRingElem
end

function Base.:(==)(a::FiniteRingElem, b::FiniteRingElem)
  @req parent(a) === parent(b) "Elements must have same parent"
  return data(a) == data(b)
end

function Base.:(*)(a::IntegerUnion, b::FiniteRingElem)
  return FiniteRingElem(parent(b), a * data(b))
end

Base.:(*)(b::FiniteRingElem, a::IntegerUnion) = a * b

function Base.:(*)(a::FiniteRingElem, b::FiniteRingElem)
  @req parent(a) == parent(b) "Elements must have same parent"
  R = parent(a)
  A = underlying_abelian_group(R)
  z = zero(A)
  for i in 1:ngens(A)
    z += data(a).coeff[i] * R.mult[i](data(b))
  end
  return FiniteRingElem(R, z)
end

function Base.:(^)(a::FiniteRingElem, n::Int)
  if n < 0
    return Base.power_by_squaring(inv(a), -n)
  else
    return Base.power_by_squaring(a, n)
  end
end

function Base.:(-)(a::FiniteRingElem)
  return FiniteRingElem(parent(a), -data(a))
end

function Base.:(+)(a::FiniteRingElem, b::FiniteRingElem)
  @req parent(a) === parent(b) "Elements must have same parent"
  return FiniteRingElem(parent(a), data(a) + data(b))
end

function Base.:(-)(a::FiniteRingElem, b::FiniteRingElem)
  @req parent(a) === parent(b) "Elements must have same parent"
  return FiniteRingElem(parent(a), data(a) - data(b))
end

################################################################################
#
#  Random
#
################################################################################

function Base.rand(R::FiniteRing)
  return FiniteRingElem(R, rand(R.A))
end
