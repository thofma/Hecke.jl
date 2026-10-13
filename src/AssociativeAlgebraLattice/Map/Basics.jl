domain(f::AssociativeAlgebraLatticeMap) = f.domain

codomain(f::AssociativeAlgebraLatticeMap) = f.codomain

@doc raw"""
    underlying_map(f::AssociativeAlgebraLatticeMap)

Return the underlying embedded-module map.
"""
underlying_map(f::AssociativeAlgebraLatticeMap) = f.underlying_map

function image(f::AssociativeAlgebraLatticeMap, x::AssociativeAlgebraLatticeElem)
  @req parent(x) === domain(f) "Element not in domain"
  return image(underlying_map(f), elem_in_module(x))
end

function image(f::AssociativeAlgebraLatticeMap{<:AssociativeAlgebraLattice, <:AssociativeAlgebraLattice},
               x::AssociativeAlgebraLatticeElem)
  @req parent(x) === domain(f) "Element not in domain"
  m = image(underlying_map(f), elem_in_module(x))
  return AssociativeAlgebraLatticeElem(codomain(f), m)
end

function preimage(f::AssociativeAlgebraLatticeMap, y)
  @req parent(y) === codomain(f) "Element not in codomain"
  m = preimage(underlying_map(f), y)
  return AssociativeAlgebraLatticeElem(domain(f), m)
end

function preimage(f::AssociativeAlgebraLatticeMap{<:AssociativeAlgebraLattice, <:AssociativeAlgebraLattice},
                  y::AssociativeAlgebraLatticeElem)
  @req parent(y) === codomain(f) "Element not in codomain"
  m = preimage(underlying_map(f), elem_in_module(y))
  return AssociativeAlgebraLatticeElem(domain(f), m)
end

function kernel(f::AssociativeAlgebraLatticeMap)
  L = domain(f)
  return lattice(algebra(L), base_ring(L), kernel(underlying_map(f)))
end

image(f::AssociativeAlgebraLatticeMap) = image(underlying_map(f))

function image(f::AssociativeAlgebraLatticeMap{<:AssociativeAlgebraLattice, <:AssociativeAlgebraLattice})
  N = codomain(f)
  return lattice(algebra(N), base_ring(N), image(underlying_map(f)))
end

is_injective(f::AssociativeAlgebraLatticeMap) = is_injective(underlying_map(f))

is_surjective(f::AssociativeAlgebraLatticeMap) = is_surjective(underlying_map(f))

is_bijective(f::AssociativeAlgebraLatticeMap) = is_bijective(underlying_map(f))

function AbstractAlgebra.show_map_head(io::IO, f::AssociativeAlgebraLatticeMap)
  @show_name(io, f)
  if codomain(f) isa AssociativeAlgebraLattice
    print(io, "Homomorphism of associative algebra lattices")
  else
    print(io, "Homomorphism from an associative algebra lattice")
  end
end

function AbstractAlgebra.show_map_data(io::IO, f::AssociativeAlgebraLatticeMap)
  L = domain(f)
  _ring_type(base_ring(L)) === _PID || return nothing
  B = basis(L; copy = false)
  isempty(B) && return nothing
  io = pretty(io)
  println(io, "\ndefined by")
  print(io, Indent())
  for i in eachindex(B)
    print(io, B[i], " -> ", f(L(B[i]; check = false)))
    i < length(B) && println(io)
  end
  print(io, Dedent())
  return nothing
end
