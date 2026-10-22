@doc raw"""
    compose(f::EmbeddedModuleMap, g::EmbeddedModuleMap)

For maps between embedded modules, return the composite `h` with
`h(x) == g(f(x))`. Require `codomain(f) === domain(g)`.

Composites of inclusion maps remain inclusion maps over PIDs and Dedekind
domains. Other composites between embedded PID modules use the product of
their coordinate matrices when both are already cached, or are constructed
from the images of the domain basis. For embedded Dedekind modules, use the
product of the matrices in pseudo-basis coordinates. These composites support
preimages, kernels, and images.
"""
function compose(f::EmbeddedModuleMap{<:EmbeddedModule, <:EmbeddedModule},
                 g::EmbeddedModuleMap{<:EmbeddedModule, <:EmbeddedModule})
  @req codomain(f) === domain(g) "Composition: Maps are not compatible"
  if data(f) isa EmbeddedModuleDataEmbedding && data(g) isa EmbeddedModuleDataEmbedding
    return inclusion_map(domain(f), codomain(g))
  end
  return _compose(f, g)
end

function _compose(f::EmbeddedModuleMap{<:EmbeddedModule{_PID}, <:EmbeddedModule{_PID}},
                  g::EmbeddedModuleMap{<:EmbeddedModule{_PID}, <:EmbeddedModule{_PID}})
  M = domain(f)
  P = codomain(g)
  df = data(f)
  dg = data(g)
  if df isa EmbeddedModuleMapPIDData && dg isa EmbeddedModuleMapPIDData &&
     isdefined(df.data, :matrix) && isdefined(dg.data, :matrix)
    return _hom(M, P, matrix(df) * matrix(dg))
  end
  images = elem_type(P)[g(f(b)) for b in basis(M; copy = false)]
  return hom(M, P, images)
end

function _compose(f::EmbeddedModuleMap{<:EmbeddedModule{_DD},
                                      <:EmbeddedModule{_DD}},
                  g::EmbeddedModuleMap{<:EmbeddedModule{_DD},
                                      <:EmbeddedModule{_DD}})
  return _hom(domain(f), codomain(g), matrix(data(f))*matrix(data(g)))
end
