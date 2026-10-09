domain(f::EmbeddedModuleMap) = f.domain

codomain(f::EmbeddedModuleMap) = f.codomain

data(f::EmbeddedModuleMap) = f.data

image(f::EmbeddedModuleMap, x::EmbeddedModuleElem) = image(data(f), x)::elem_type(codomain(f))

preimage(f::EmbeddedModuleMap, y) = preimage(data(f), y)::elem_type(domain(f))

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
