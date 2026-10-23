domain(f::EmbeddedModuleMap) = f.domain

codomain(f::EmbeddedModuleMap) = f.codomain

data(f::EmbeddedModuleMap) = f.data

ring_map(f::EmbeddedModuleMap) = ring_map(data(f))

image(f::EmbeddedModuleMap, x::EmbeddedModuleElem) = image(data(f), x)::elem_type(codomain(f))

preimage(f::EmbeddedModuleMap, y) = preimage(data(f), y)::elem_type(domain(f))

@doc raw"""
    preimage(f::EmbeddedModuleMap, N::EmbeddedModule)

Return the submodule of `domain(f)` whose images lie in `N`. Require `N`
to be a submodule of the embedded codomain. Support PIDs and maximal
Dedekind orders with their fraction fields as overrings.
"""
function preimage(f::EmbeddedModuleMap{<:EmbeddedModule, <:EmbeddedModule},
                  N::EmbeddedModule)
  # Project the kernel of (x, n) -> f(x) + n onto the first summand.
  h, p, _ = addition_map(f, inclusion_map(N, codomain(f)))
  return image(compose(inclusion_map(kernel(h), domain(h)), p))
end

function _check_ambient_matrix(M::EmbeddedModule, N::EmbeddedModule,
                               A::MatElem)
  @req ring(M) === ring(N) "The modules must have the same coefficient ring"
  @req overring(M) === overring(N) "The modules must have the same overring"
  @req base_ring(A) === overring(M) "The matrix must be over the overring"
  @req nrows(A) == ambient_rank(M) &&
       ncols(A) == ambient_rank(N) "The matrix has the wrong dimensions"
  return nothing
end

image(f::EmbeddedModuleMap) = image(data(f))::typeof(codomain(f))

kernel(f::EmbeddedModuleMap) = kernel(data(f))::typeof(domain(f))

is_injective(f::EmbeddedModuleMap) = is_injective(data(f))::Bool

is_surjective(f::EmbeddedModuleMap) = is_surjective(data(f))::Bool

is_bijective(f::EmbeddedModuleMap) = is_bijective(data(f))::Bool

function Hecke.AbstractAlgebra.show_map_head(io::IO, f::EmbeddedModuleMap)
  Hecke.@show_name(io, f)
  print(io, "Homomorphism of embedded modules")
end

function Hecke.AbstractAlgebra.show_map_data(io::IO,
                          f::EmbeddedModuleMap{<:EmbeddedModule{_PID}})
  B = basis(domain(f); copy = false)
  isempty(B) && return nothing
  io = Hecke.pretty(io)
  println(io, "\ndefined by")
  print(io, Hecke.Indent())
  for i in eachindex(B)
    print(io, B[i], " -> ", image(f, B[i]))
    i < length(B) && println(io)
  end
  print(io, Hecke.Dedent())
  return nothing
end
