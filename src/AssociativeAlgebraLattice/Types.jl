@attributes mutable struct AssociativeAlgebraLattice{AlgType, BRingType}
  algebra::AlgType
  base_ring::BRingType
  M::EmbeddedModule
  basis::Vector

  function AssociativeAlgebraLattice(A::AlgType, R::BRingType, M::EmbeddedModule) where {AlgType, BRingType}
    return new{AlgType, BRingType}(A, R, M)
  end
end

struct AssociativeAlgebraLatticeMap{D <: AssociativeAlgebraLattice,
                                   C,
                                   F <: EmbeddedModuleMap} <:
       Map{D, C, HeckeMap, AssociativeAlgebraLatticeMap}
  domain::D
  codomain::C
  underlying_map::F

  function AssociativeAlgebraLatticeMap(L::AssociativeAlgebraLattice,
                                       N,
                                       f::EmbeddedModuleMap)
    @req domain(f) === underlying_module(L) "The map has the wrong domain module"
    @req codomain(f) === N "The map has the wrong codomain"
    return new{typeof(L), typeof(N), typeof(f)}(L, N, f)
  end

  function AssociativeAlgebraLatticeMap(L::AssociativeAlgebraLattice,
                                       N::AssociativeAlgebraLattice,
                                       f::EmbeddedModuleMap)
    @req base_ring(L) === base_ring(N) "The lattices must have the same coefficient ring"
    @req domain(f) === underlying_module(L) "The map has the wrong domain module"
    @req codomain(f) === underlying_module(N) "The map has the wrong codomain module"
    return new{typeof(L), typeof(N), typeof(f)}(L, N, f)
  end
end

mutable struct AssociativeAlgebraLatticeElem{LatticeType, ModuleElemType, AlgebraElemType}
  parent::LatticeType
  elem_in_module::ModuleElemType
  elem_in_algebra::AlgebraElemType

  function AssociativeAlgebraLatticeElem(L::AssociativeAlgebraLattice, m::EmbeddedModuleElem)
    @req parent(m) === underlying_module(L) "The element belongs to a different embedded module"
    return new{typeof(L), typeof(m), elem_type(algebra(L))}(L, m)
  end
end
