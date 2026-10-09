domain(f::EmbeddedModuleDataPIDQuotient) = f.domain

codomain(f::EmbeddedModuleDataPIDQuotient) = f.codomain

function image(f::EmbeddedModuleDataPIDQuotient, x::EmbeddedModuleElem)
  @req parent(x) === domain(f) "Element not in domain"
  F = domain(f.quotient_map)
  return f.quotient_map(F(coordinates(x; copy = false)))
end

function preimage(f::EmbeddedModuleDataPIDQuotient, y)
  @req parent(y) === codomain(f) "Element not in codomain"
  c = coordinates(preimage(f.quotient_map, y))
  return _element_from_coordinates(domain(f), c; check = false)
end

image(f::EmbeddedModuleDataPIDQuotient) = codomain(f)

kernel(f::EmbeddedModuleDataPIDQuotient) = f.kernel

is_injective(f::EmbeddedModuleDataPIDQuotient) = iszero(rank(kernel(f)))

is_surjective(f::EmbeddedModuleDataPIDQuotient) = true

is_bijective(f::EmbeddedModuleDataPIDQuotient) = is_injective(f)
