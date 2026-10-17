domain(f::EmbeddedModuleDataDDReduction) = f.domain

codomain(f::EmbeddedModuleDataDDReduction) = f.codomain

ring_map(f::EmbeddedModuleDataDDReduction) = f.ring_map

function image(f::EmbeddedModuleDataDDReduction, x::EmbeddedModuleElem)
  @req parent(x) === domain(f) "Element not in domain"
  V = codomain(f)
  F = base_ring(V)
  c = coordinates(x; copy = false)
  v = elem_type(F)[image(f.field_map, c[i]/f.local_generators[i])
                   for i in eachindex(c)]
  if f.projection_matrix !== nothing
    v = v * f.projection_matrix
  end
  return V(v)
end

function preimage(f::EmbeddedModuleDataDDReduction, y)
  @req parent(y) === codomain(f) "Element not in codomain"
  M = domain(f)
  K = overring(M)
  v = coordinates(y)
  if f.section_matrix !== nothing
    v = v * f.section_matrix
  end
  c = elem_type(K)[image(fraction_map(M), preimage(ring_map(f), v[i])) *
                   f.lift_coefficients[i] for i in eachindex(v)]
  return _element_from_coordinates(M, c; check = false)
end

image(f::EmbeddedModuleDataDDReduction) = codomain(f)

kernel(f::EmbeddedModuleDataDDReduction) = f.kernel

is_injective(f::EmbeddedModuleDataDDReduction) = iszero(rank(kernel(f)))

is_surjective(f::EmbeddedModuleDataDDReduction) = true

is_bijective(f::EmbeddedModuleDataDDReduction) = is_injective(f)
