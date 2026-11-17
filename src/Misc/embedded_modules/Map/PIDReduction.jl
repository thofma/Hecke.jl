domain(f::EmbeddedModuleDataPIDReduction) = f.domain

codomain(f::EmbeddedModuleDataPIDReduction) = f.codomain

ring_map(f::EmbeddedModuleDataPIDReduction) = f.ring_map

function image(f::EmbeddedModuleDataPIDReduction, x::EmbeddedModuleElem)
  @req parent(x) === domain(f) "Element not in domain"
  V = codomain(f)
  F = base_ring(V)
  c = elem_type(F)[image(ring_map(f), a)
                   for a in coordinates(x; copy = false)]
  if f.projection_matrix !== nothing
    c = c * f.projection_matrix
  end
  return V(c)
end

function preimage(f::EmbeddedModuleDataPIDReduction, y)
  @req parent(y) === codomain(f) "Element not in codomain"
  M = domain(f)
  R = ring(M)
  v = coordinates(y)
  if f.section_matrix !== nothing
    v = v * f.section_matrix
  end
  c = elem_type(R)[preimage(ring_map(f), a) for a in v]
  return _element_from_coordinates(M, c; check = false)
end

image(f::EmbeddedModuleDataPIDReduction) = codomain(f)

kernel(f::EmbeddedModuleDataPIDReduction) = f.kernel

is_injective(f::EmbeddedModuleDataPIDReduction) = iszero(rank(kernel(f)))

is_surjective(f::EmbeddedModuleDataPIDReduction) = true

is_bijective(f::EmbeddedModuleDataPIDReduction) = is_injective(f)
