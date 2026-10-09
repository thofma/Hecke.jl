inclusion_map(N::EmbeddedModule, M::EmbeddedModule) =
  EmbeddedModuleMap(N, M, EmbeddedModuleDataEmbedding(N, M))

domain(f::EmbeddedModuleDataEmbedding) = f.domain

codomain(f::EmbeddedModuleDataEmbedding) = f.codomain

function image(f::EmbeddedModuleDataEmbedding, x::EmbeddedModuleElem)
  @req parent(x) === domain(f) "Element not in domain"
  return _element_from_ambient_coordinates(codomain(f),
                              deepcopy(ambient_coordinates(x)); check = false)
end

function preimage(f::EmbeddedModuleDataEmbedding, y::EmbeddedModuleElem)
  @req parent(y) === codomain(f) "Element not in codomain"
  N = domain(f)
  v = ambient_coordinates(y)
  @req _in(matrix(overring(N), 1, length(v), v), N) "Element has no preimage"
  return _element_from_ambient_coordinates(N, deepcopy(v); check = false)
end

image(f::EmbeddedModuleDataEmbedding) = domain(f)

kernel(f::EmbeddedModuleDataEmbedding) = _zero_module_like(domain(f))

is_injective(f::EmbeddedModuleDataEmbedding) = true

is_surjective(f::EmbeddedModuleDataEmbedding) = domain(f) == codomain(f)

is_bijective(f::EmbeddedModuleDataEmbedding) = is_surjective(f)
