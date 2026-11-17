function _lattice_map_element(L::AssociativeAlgebraLattice, x::AssociativeAlgebraLatticeElem)
  @req parent(x) === L "The element belongs to a different lattice"
  return elem_in_module(x)
end

_lattice_map_element(L::AssociativeAlgebraLattice, x::AbstractAssociativeAlgebraElem) =
  elem_in_module(L(x))

function _check_lattice_hom(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice)
  @req base_ring(L) === base_ring(N) "The lattices must have the same coefficient ring"
  @req _ring_type(base_ring(L)) === _PID "General lattice homomorphisms require PID coefficients"
  return nothing
end

@doc raw"""
    hom(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice, images::Vector)
    hom(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice, assignments::Vector{<:Pair})

Construct a linear map over the common coefficient ring, which must be a PID.
The ambient algebras may differ. A vector of images assigns images to `basis(L)`
in order. Alternatively, pairs `x => y` assign images to a generating set of `L`;
generation and compatibility with relations are checked.

Entries may be elements of the corresponding lattice or its ambient algebra.
Lattice elements must have the exact parent specified; ambient elements are
checked for membership in the corresponding lattice.
"""
function hom(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice, images::Vector)
  _check_lattice_hom(L, N)
  M, P = underlying_module(L), underlying_module(N)
  imgs = elem_type(P)[_lattice_map_element(N, y) for y in images]
  return AssociativeAlgebraLatticeMap(L, N, hom(M, P, imgs))
end

function hom(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice, assignments::Vector{<:Pair})
  _check_lattice_hom(L, N)
  M, P = underlying_module(L), underlying_module(N)
  imgs = Pair{elem_type(M), elem_type(P)}[
    _lattice_map_element(L, x) => _lattice_map_element(N, y) for (x, y) in assignments
  ]
  return AssociativeAlgebraLatticeMap(L, N, hom(M, P, imgs))
end

@doc raw"""
    hom(L::AssociativeAlgebraLattice, X, images::Vector)
    hom(L::AssociativeAlgebraLattice, X, assignments::Vector{<:Pair})

For PID coefficients, construct a linear map from `L` to `X` by delegating to
the underlying embedded module. The codomain must support the coefficient
ring's scalar action. Images must have `X` as their exact parent.

A vector of images assigns images to `basis(L)` in order. Pairs `x => y`
specify images of generators; sources may be lattice elements with parent `L`
or ambient algebra elements in `L`. Generation and relations are checked by
the embedded-module backend. Preimages, kernels, images, and predicates are
available when supported by that backend.
"""
function hom(L::AssociativeAlgebraLattice, X, images::Vector)
  @req _ring_type(base_ring(L)) === _PID "General lattice homomorphisms require PID coefficients"
  return AssociativeAlgebraLatticeMap(L, X, hom(underlying_module(L), X, images))
end

function hom(L::AssociativeAlgebraLattice, X, assignments::Vector{<:Pair})
  @req _ring_type(base_ring(L)) === _PID "General lattice homomorphisms require PID coefficients"
  M = underlying_module(L)
  imgs = Pair{elem_type(M), Any}[_lattice_map_element(L, x) => y for (x, y) in assignments]
  return AssociativeAlgebraLatticeMap(L, X, hom(M, X, imgs))
end
