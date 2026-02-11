################################################################################
#
#  Maps between finite rings
#
################################################################################

function id_hom(R::FiniteRing)
  f = FiniteRingHom(R, R, true, id_hom(underlying_abelian_group(R)))
  f.g = f
  return f
end

function hom(R::FiniteRing, S::FiniteRing, imgs::Vector{FiniteRingElem}; check::Bool = true)
  @req length(imgs) == _nzgens(R) "Wrong number of images"
  f = FiniteRingHom(R, S, true, hom(underlying_abelian_group(R), underlying_abelian_group(S), data.(imgs)))
  if check
    @req is_one(f(one(R))) "Not a ring homomorphism"
    for x in _zgens(R), y in _zgens(R)
      @req f(x + y) == f(x) + f(y) "Not a ring homomorphism"
      @req f(x * y) == f(x) * f(y) "Not a ring homomorphism"
    end
  end
  return f
end

domain(f::FiniteRingHom) = f.R

codomain(f::FiniteRingHom) = f.S

(f::FiniteRingHom)(a::FiniteRingElem) = image(f, a)

function image(f::FiniteRingHom, a::FiniteRingElem)
  @assert parent(a) === domain(f)
  return FiniteRingElem(codomain(f), f.f(a.a))
end

function preimage(f::FiniteRingHom, a::FiniteRingElem)
  @assert parent(a) === codomain(f)
  if isdefined(f, :g)
    return image(f.g::FiniteRingHom, a)
  else
    return FiniteRingElem(domain(f), preimage(f.f, a.a))
  end
end

function Base.:(\)(f::FiniteRingHom, a::FiniteRingElem)
  return preimage(f, a)
end

################################################################################
#
#  Maps from finite rings to anything
#
################################################################################

function _hom(R::FiniteRing, S::NCRing, imgzgens::Vector{<:NCRingElem}, inverse, check)
  @req length(imgzgens) == _nzgens(R) "Wrong number of images"
  f = FiniteRingMap(R, S, imgzgens, inverse)
  if check
    @req f(one(R)) == one(S) "Data does not define a morphism"
    B = _zgens(R)
    for x in B, y in B
      @req f(x * y) == f(x) * f(y) "Data does not define a morphism"
    end
  end
  return f
end

function hom(R::FiniteRing, S::NCRing, imgzgens::Vector{<:NCRingElem}; inverse = nothing, check::Bool = true)
  return _hom(R, S, imgzgens, inverse, check)
end

domain(f::FiniteRingMap) = f.R

codomain(f::FiniteRingMap) = f.S

function image(f::FiniteRingMap, x::FiniteRingElem)
  @req domain(f) === parent(x) "Parent of element must be domain"
  return sum(x.a.coeff[i] * f.imgzgens[i] for i in 1:length(x.a.coeff))::elem_type(codomain(f))
end

function preimage(f::FiniteRingMap, y)
  @req codomain(f) === parent(y) "Parent of element must be codomain"
  if !isdefined(f, :inv)
    throw(AbstractAlgebra.NotImplementedError(:preimage, (f, y)))
  end
  return f.inv(y)::elem_type(domain(f))
end
