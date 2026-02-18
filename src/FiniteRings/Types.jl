@attributes mutable struct FiniteRing <: NCRing
  A::FinGenAbGroup
  mult::Vector{FinGenAbGroupHom}
  one

  FiniteRing(A, mult) = new(A, mult)
end

struct FiniteRingElem <: NCRingElem
  parent::FiniteRing
  a::FinGenAbGroupElem
  inv#=Ref{FiniteRingElem=# # we want to cache the inverse, but we want to keep
                            # object immutable, so let's do the Ref[] dance.
                            # We use RefValue, since Ref is abstract

  function FiniteRingElem(R::FiniteRing, a::FinGenAbGroupElem)
    @assert parent(a) === R.A
    return new(R, a, Base.RefValue{FiniteRingElem}())
  end
end

@attributes mutable struct FiniteRingIdeal
  R::FiniteRing
  B::FinGenAbGroup        # abelian group
  BtoA::FinGenAbGroupHom  # embedding of abelian groups

  FiniteRingIdeal(x, y, z) = new(x, y, z)
end

mutable struct FiniteRingHom <: Map{FiniteRing, FiniteRing, HeckeMap, FiniteRingHom}
  R::FiniteRing
  S::FiniteRing
  is_unitary::Bool # we internally use the type to represent non-unitary morphisms
  f::FinGenAbGroupHom
  g

  function FiniteRingHom(R::FiniteRing, S::FiniteRing, is_unitary::Bool, f::FinGenAbGroupHom)
    @assert domain(f) === underlying_abelian_group(R)
    @assert codomain(f) === underlying_abelian_group(S)
    return new(R, S, is_unitary, f)
  end
end

@attributes mutable struct FiniteRingMap{S, T} <: Map{FiniteRing, T, HeckeMap, FiniteRingMap}
  R::FiniteRing
  S::S
  imgzgens::T
  inv

  function FiniteRingMap(R, S, imgzgens, inv)
    if inv === nothing
      return new{typeof(S), typeof(imgzgens)}(R, S, imgzgens)
    else
      return new{typeof(S), typeof(imgzgens)}(R, S, imgzgens, inv)
    end
  end
end

struct RingMultMap{S, T} <: Map{S, T, Any, Any}
  R::S
  A::T
  f
  g
end

mutable struct OnePlusIdeal{S}
  ideal::S

  function OnePlusIdeal(I::S) where {S}
    OI = new{S}(I)
    return OI
  end
end

mutable struct OnePlusIdealElem{S, T}
  parent::OnePlusIdeal{S}
  elem::T
end

mutable struct OnePlusIdealModuloOnePlusIdeal{S, R, T}
  I::S
  J::S
  Q::R
  ItoQ::T

  function OnePlusIdealModuloOnePlusIdeal(I::S, J::S) where {S}
    Q, ItoQ = quo(ideal(I), ideal(J))
    new{S, typeof(Q), typeof(ItoQ)}(I, J, Q, ItoQ)
  end
end

struct OnePlusIdealModuloOnePlusIdealElem{S, T}
  parent::S
  elem::T

  function OnePlusIdealModuloOnePlusIdealElem(parent::S, elem::T) where {S, T}
    return new{S, T}(parent, elem)
  end
end

struct OnePlusIdealQuoMap{S, R, T}
  I::S
  QQ::OnePlusIdealModuloOnePlusIdeal{S, R, T}
  ItoQ::T

  function OnePlusIdealQuoMap(I::S, QQ::OnePlusIdealModuloOnePlusIdeal{S, R, T}, ItoQ::T) where {S, R, T}
    return new{S, R, T}(I, QQ, ItoQ)
  end
end
