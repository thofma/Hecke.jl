domain(f::EmbeddedModuleDataDDQuotient) = f.domain

codomain(f::EmbeddedModuleDataDDQuotient) = f.codomain

function image(f::EmbeddedModuleDataDDQuotient, x::EmbeddedModuleElem)
  @req parent(x) === domain(f) "Element not in domain"
  return codomain(f)(coordinates(x; copy = false))
end

function preimage(f::EmbeddedModuleDataDDQuotient, y)
  @req parent(y) === codomain(f) "Element not in codomain"
  return _element_from_coordinates(domain(f), coordinates(y); check = false)
end

image(f::EmbeddedModuleDataDDQuotient) = codomain(f)

kernel(f::EmbeddedModuleDataDDQuotient) = f.kernel

is_injective(f::EmbeddedModuleDataDDQuotient) = iszero(rank(kernel(f)))

is_surjective(f::EmbeddedModuleDataDDQuotient) = true

is_bijective(f::EmbeddedModuleDataDDQuotient) = is_injective(f)
