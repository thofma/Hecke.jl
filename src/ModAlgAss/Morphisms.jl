################################################################################
#
#  Module morphism type
#
################################################################################

mutable struct ModAlgHom{S, T} <: Map{S, S, HeckeMap, ModAlgHom}
  domain::S
  codomain::S
  matrix::T     # matrix underlying the morphism
                # D[i] * matrix = matrix * C[i]
                # where D = action of domain, C = action of codomain

  function ModAlgHom(domain::S, codomain::S, matrix::T) where {S, T}
    return new{S, T}(domain, codomain, matrix)
  end
end

domain(f::ModAlgHom) = f.domain

codomain(f::ModAlgHom) = f.codomain

matrix(f::ModAlgHom) = f.matrix

function morphism(V::T, W::T, M::MatrixElem; check = true) where {T <: ModAlgAss}
  @req has_algebra(V) == has_algebra(W) "Both modules must have underlying algebra or not"
  if has_algebra(V)
    @req algebra(V) === algebra(W) "Modules must have same underlying algbera"
  end
  if check
    x, y = consistent_action(V, W)
    for i in 1:length(x)
      @req x[i] * M == M * y[i] "Matrix is not a morphism"
    end
  end
  return ModAlgHom(V, W, M)
end

function Base.show(io::IO, f::ModAlgHom)
  print(io, "Module morphism")
end

#################################################################################
#
#  Endomorphism algebra map
#
################################################################################

mutable struct EndAlgMap{S, T, U} <: Map{S, T, HeckeMap, EndAlgMap}
  domain::S    # the endomorphism algebra as a matrix algebra
  codomain::T  # formal set of endomorphisms
  V::U         # the underlying module

  function EndAlgMap(domain::S, V::U) where {S, U}
    codomain = MapParent(V, V, "Morphism")
    return new{S, typeof(codomain), U}(domain, codomain, V)
  end
end

domain(f::EndAlgMap) = f.domain

codomain(f::EndAlgMap) = f.codomain

function image(f::EndAlgMap, a::AbsAlgAssElem)
  @req parent(a) === domain(f) "Element must be in the domain of the map"
  return ModAlgHom(f.V, f.V, matrix(a))
end

################################################################################
#
#  Basis of homomorphism spaces
#
################################################################################

function _basis_of_hom(V::ModAlgAss{T}, W::ModAlgAss{T}) where {T <: Field}
  x, y = consistent_action(V, W)
  B = _basis_of_commutator_algebra(x, y)
end

################################################################################
#
#  Endomorphism algebra function
#
################################################################################

function endomorphism_algebra(V::ModAlgAss)
  B = _basis_of_hom(V, V)
  x, _ = consistent_action(V, V)
  for b in B
    for i in 1:length(x)
      @assert x[i] * b == b * x[i]
    end
  end
  A = matrix_algebra(coefficient_ring(V), B, isbasis = true)
  return A, EndAlgMap(A, V)
end

