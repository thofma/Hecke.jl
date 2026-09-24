################################################################################
#
#  Maps from orders to anything
#
################################################################################

function _hom(::Type{_PID}, R::AssociativeAlgebraOrder, S::NCRing, baseringmap, imagebasis::Vector{<:NCRingElem}, preimage, check)
  @req length(imagebasis) == degree(R) "Wrong number of images"
  f = AssociativeAlgebraOrderMap(R, S, baseringmap, imagebasis, preimage)
  if check
    @req f(one(R)) == one(S) "Data does not define a morphism"
    B = basis(R; copy = false)
    for x in B, y in B
      @req f(x * y) == f(x) * f(y) "Data does not define a morphism"
    end
  end
  return f
end

function hom(R::AssociativeAlgebraOrder, S::NCRing, baseringmap, imagebasis::Vector{<:NCRingElem}; preimage = nothing, check::Bool = true)
  return _hom(_ring_type(base_ring(R)), R, S, baseringmap, imagebasis, preimage, check)
end

function hom(R::AssociativeAlgebraOrder, S::NCRing, imagebasis::Vector{<:NCRingElem}; preimage = nothing, check::Bool = true)
  return _hom(_ring_type(base_ring(R)), R, S, identity, imagebasis, preimage, check)
end

function image(f::AssociativeAlgebraOrderMap, x::AssociativeAlgebraOrderElem)
  @req domain(f) === parent(x) "Parent of element must be domain"
  c = coordinates(x; copy = false)
  return sum(f.baseringmap(c[i]) * f.imageofbasis[i] for i in 1:length(c))::elem_type(codomain(f))
end

function preimage(f::AssociativeAlgebraOrderMap, y)
  @req codomain(f) === parent(y) "Parent of element must be codomain"
  if f.preimage === nothing
    throw(AbstractAlgebra.NotImplementedError(:preimage, (f, y)))
  end
  return f.preimage(y)::elem_type(domain(f))
end

domain(f::AssociativeAlgebraOrderMap) = f.domain

codomain(f::AssociativeAlgebraOrderMap) = f.codomain

# TODO: if the codomain is an algebra over a finite field, store the image of the basis as a matrix
# and realize the evaluation as vector-matrix multiplication.
# Store an `map_data` field, which whose exact type depends on the type of the codomain
