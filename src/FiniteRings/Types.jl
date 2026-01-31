struct EffectivePresentation{S}
  A::S
  G#=::FPGroup=#
  forward
  backward

  # G an FPGroup (most of the time)
  function EffectivePresentation(A::S, G, forward, backward) where {S}
    z = new{S}(A, G, forward, backward)
    #@info "Testing EffectivePresentation"
    #for i in 1:10
    #   #if A isa FiniteRing || A isa OnePlusIdeal || A isa OnePlusIdealModuloOnePlusIdeal
    #   #  y = rand(A)
    #   #  while A isa FiniteRing && !is_unit(y)
    #   #    y = rand(A)
    #   #  end
    #   #  @assert parent(y) === A "Asds"
    #   #  @show "asds"
    #   #  @show forward(y)
    #   #  @show "asssds"
    #   #  @assert backward(forward(y)) == y
    #   #end
    #   x = rand_pseudo(G)
    #   @assert parent(backward(x)) === A
    #   @assert backward(forward(backward(x))) == backward(x)
    #   y = rand_pseudo(G)
    #   @assert backward(x * y) == op(A)(backward(x), backward(y))
    # end
     return z
  end
end

@attributes mutable struct FiniteRing <: Ring
  A::FinGenAbGroup
  mult::Vector{FinGenAbGroupHom}
  one

  FiniteRing(A, mult) = new(A, mult)
end

struct FiniteRingElem <: RingElem
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

struct FiniteRingHom
  R::FiniteRing
  S::FiniteRing
  f
  g
end

@attributes mutable struct FiniteRingMap{S, T}
  R::FiniteRing
  S::S
  imgzgens::T
  inv

  FiniteRingMap(R, S, imgzgens) = new{typeof(S), typeof(imgzgens)}(R, S, imgzgens)

  FiniteRingMap(R, S, imgzgens, inv) = new{typeof(S), typeof(imgzgens)}(R, S, imgzgens, inv)
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
