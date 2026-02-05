function id_hom(R::FiniteRing)
  f = FiniteRingHom2(R, R, true, id_hom(underlying_abelian_group(R)))
  f.g = f
  return f
end

function hom(R::FiniteRing, S::FiniteRing, imgs::Vector{FiniteRingElem}; check::Bool = true)
  @req length(imgs) == _nzgens(R) "Wrong number of images"
  f = FiniteRingHom2(R, S, true, hom(underlying_abelian_group(R), underlying_abelian_group(S), data.(imgs)))
  if check
    @req is_one(f(one(R))) "Not a ring homomorphism"
    for x in _zgens(R), y in _zgens(R)
      @req f(x + y) == f(x) + f(y) "Not a ring homomorphism"
      @req f(x * y) == f(x) * f(y) "Not a ring homomorphism"
    end
  end
  return f
end

domain(f::FiniteRingHom2) = f.R

codomain(f::FiniteRingHom2) = f.S

(f::FiniteRingHom2)(a::FiniteRingElem) = image(f, a)

function image(f::FiniteRingHom2, a::FiniteRingElem)
  @assert parent(a) === domain(f)
  return FiniteRingElem(codomain(f), f.f(a.a))
end

function preimage(f::FiniteRingHom2, a::FiniteRingElem)
  @assert parent(a) === codomain(f)
  if isdefined(f, :g)
    return image(f.g::FiniteRingHom2, a)
  else
    return FiniteRingElem(S, preimage(f.f, a.a))
  end
end

function Base.:(\)(f::FiniteRingHom2, a::FiniteRingElem)
  return preimage(f, a)
end

###

domain(f::FiniteRingHom) = f.R

codomain(f::FiniteRingHom) = f.S

function image(f::FiniteRingHom, a::FiniteRingElem)
  @assert parent(a) === f.R
  return f.f(a)#FiniteRingElem(S, f.f(a.a))
end

(f::FiniteRingHom)(a) = image(f, a)

function preimage(f::FiniteRingHom, a::FiniteRingElem)
  @assert parent(a) === f.S
  return f.g(a)#FiniteRingElem(S, preimage(f.f, a.a))
end

function Base.:(\)(f::FiniteRingHom, a::FiniteRingElem)
  return preimage(f, a)
end

function quo(I::FiniteRingIdeal, J::FiniteRingIdeal)
  gensJ = _zgens(J)
  R = I.R
  @assert I.R === J.R
  gensJinI = FinGenAbGroupElem[]
  for g in gensJ
    fl, x = has_preimage_with_preimage(I.BtoA, g.a)
    if !fl
      error("Ideal not containing second argument")
    end
    push!(gensJinI, x)
  end
  Q, ItoQ = quo(I.B, gensJinI)
  SQ, SQtoQ = snf(Q)
  Q, ItoQ = SQ, ItoQ * inv(SQtoQ)
  gensQ = gens(Q)
  homs = FinGenAbGroupHom[]
  for a in gensQ
    H = FinGenAbGroupElem[]
    for x in gensQ
      push!(H, ItoQ(I.BtoA\((FiniteRingElem(R, I.BtoA(ItoQ\a)) * FiniteRingElem(R, I.BtoA(ItoQ\x))).a)))
    end
    push!(homs, hom(Q, Q, H))
  end
  quoring = FiniteRing(Q, homs)
  pr = x -> FiniteRingElem(quoring, ItoQ(I.BtoA\(x.a)))
  lf = y -> FiniteRingElem(R, I.BtoA(ItoQ\(y.a)))
  return quoring, FiniteRingHom(R, quoring, pr, lf)
end

function quo(R::FiniteRing, J::FiniteRingIdeal)
  gensJ = _zgens(J)
  gensJinI = FinGenAbGroupElem[]
  Q, RtoQ = quo(R.A, J.BtoA.(gens(J.B)))
  SQ, SQtoQ = snf(Q)
  Q, RtoQ = SQ, RtoQ * inv(SQtoQ)
  gensQ = gens(Q)
  homs = FinGenAbGroupHom[]
  for a in gensQ
    H = FinGenAbGroupElem[]
    for x in gensQ
      push!(H, RtoQ((FiniteRingElem(R, RtoQ\a) * FiniteRingElem(R, RtoQ\x)).a))
    end
    push!(homs, hom(Q, Q, H))
  end
  quoring = FiniteRing(Q, homs)
  pr = x -> FiniteRingElem(quoring, RtoQ(x.a))
  lf = y -> FiniteRingElem(R, RtoQ\(y.a))
  return quoring, FiniteRingHom(R, quoring, pr, lf)
end

##########################

function _hom(R::FiniteRing, S::NCRing, imgzgens::Vector{<:NCRingElem}; inverse = nothing, check::Bool = true)
  # implement check
  if inverse === nothing
    return FiniteRingMap(R, S, imgzgens)
  else
    return FiniteRingMap(R, S, imgzgens, inverse)
  end
end

domain(f::FiniteRingMap) = f.R

(f::FiniteRingMap)(x) = image(f, x)

codomain(f::FiniteRingMap) = f.S

function image(f::FiniteRingMap, x::FiniteRingElem)
  @req domain(f) === parent(x) "Parent of element must be domain"
  return sum(x.a.coeff[i] * f.imgzgens[i] for i in 1:length(x.a.coeff))::elem_type(codomain(f))
end

function preimage(f::FiniteRingMap, y)
  @assert isdefined(f, :inv)
  @req codomain(f) === parent(y) "Parent of element must be codomain"
  return f.inv(y)::elem_type(domain(f))
end

#

@attributes mutable struct AbstractAssociativeAlgebraMap{D, C, S, T}
  R::D
  S::C
  base_ring_map::S
  imgbasis::T
  inv

  function AbstractAssociativeAlgebraMap(R::Hecke.AbstractAssociativeAlgebra, S::NCRing, base_ring_map, imgbasis, inv)
    if inv === nothing
      new{typeof(R), typeof(S), typeof(base_ring_map), typeof(imgbasis)}(R, S, base_ring_map, imgbasis)
    else
      new{typeof(R), typeof(S), typeof(base_ring_map), typeof(imgbasis)}(R, S, base_ring_map, imgbasis, inv)
    end
  end
end

function _hom(R::Hecke.AbstractAssociativeAlgebra, S::NCRing, imgbasis::Vector{<:NCRingElem};inv = nothing, check::Bool = true)
  return AbstractAssociativeAlgebraMap(R, S, identity, imgbasis, inv)
end

function _hom(R::Hecke.AbstractAssociativeAlgebra, S::NCRing, f, imgbasis::Vector{<:NCRingElem}; inv = nothing, check::Bool = true)
  return AbstractAssociativeAlgebraMap(R, S, f, imgbasis, inv)
end

domain(f::AbstractAssociativeAlgebraMap) = f.R

(f::AbstractAssociativeAlgebraMap)(x) = image(f, x)

codomain(f::AbstractAssociativeAlgebraMap) = f.S

function image(f::AbstractAssociativeAlgebraMap, x)
  @req domain(f) === parent(x) "Parent of element must be domain"
  c = coefficients(x)
  return sum(f.base_ring_map(c[i]) * f.imgbasis[i] for i in 1:length(c))::elem_type(codomain(f))
end

function preimage(f::AbstractAssociativeAlgebraMap, y)
  @assert isdefined(f, :inv)
  @req codomain(f) === parent(y) "Parent of element must be codomain"
  return f.inv(y)::elem_type(domain(f))
end

### AbsOrdQuoRign
#
@attributes mutable struct AbsOrdQuoRingMap{D, C, T}
  R::D
  S::C
  imgbasis::T

  AbsOrdQuoRingMap(R::Hecke.AbsOrdQuoRing, S::NCRing, imgbasis) = new{typeof(R), typeof(S), typeof(imgbasis)}(R, S, imgbasis)
end

function _hom(R::Hecke.AbsOrdQuoRing, S::NCRing, imgbasis::Vector{<:NCRingElem}; check::Bool = true)
  return AbsOrdQuoRingMap(R, S, imgbasis)
end

domain(f::AbsOrdQuoRingMap) = f.R

(f::AbsOrdQuoRingMap)(x) = image(f, x)

codomain(f::AbsOrdQuoRingMap) = f.S

function image(f::AbsOrdQuoRingMap, x)
  @req domain(f) === parent(x) "Parent of element must be domain"
  c = coordinates(x.elem)
  return sum(c[i] * f.imgbasis[i] for i in 1:length(c))::elem_type(codomain(f))
end

############

function isomorphism(::Type{MatAlgebra}, R::FiniteRing)
  p = exponent(R.A)
  @assert is_prime(p)
  G = gens(R.A)
  @assert length(G) == length(elementary_divisors(R.A))
  F = GF(p)
  MA = matrix_algebra(F, map_entries.(Ref(F), transpose.(matrix.(R.mult))); isbasis = true) # isbasis = true is important
  inv = _hom(R, MA, [MA(F.(x.a.coeff[1,:])) for x in _zgens(R)])
  f = _hom(MA, R, x -> lift(ZZ, x), [FiniteRingElem(R, R.A(lift.(Ref(ZZ), coefficients(y)))) for y in basis(MA)])
  f.inv = inv
  inv.inv = f
  #for i in 1:10
  #  r = preimage(f, rand(R))
  #  s = preimage(f, rand(R))
  #  @assert f(r) * f(s) == f(r * s)
  #  @assert f(r) + f(s) == f(r + s)
  #  @assert preimage(f, f(r)) == r
  #end
  return MA, f
end

function isomorphism(::Type{Hecke.StructureConstantAlgebra}, R::FiniteRing)
  p = exponent(R.A)
  @assert is_prime(p)
  @assert fits(Int, p)
  G = gens(R.A)
  @assert length(G) == length(elementary_divisors(R.A))
  F = Nemo.Native.GF(Int(p))
  MA = matrix_algebra(F, map_entries.(Ref(F), transpose.(matrix.(R.mult))); isbasis = true) # isbasis = true is important
  S, StoMA = StructureConstantAlgebra(MA)
  inv = _hom(R, S, [preimage(StoMA, MA(F.(x.a.coeff[1,:]))) for x in _zgens(R)])
  f = _hom(S, R, x -> lift(ZZ, x), [FiniteRingElem(R, R.A(lift.(Ref(ZZ), coefficients(StoMA(y))))) for y in basis(S)])
  f.inv = inv
  inv.inv = f
  #for i in 1:10
  #  r = preimage(f, rand(R))
  #  s = preimage(f, rand(R))
  #  @assert f(r) * f(s) == f(r * s)
  #  @assert f(r) + f(s) == f(r + s)
  #  @assert preimage(f, f(r)) == r
  #end
  if has_attribute(R, :radical)
    set_attribute!(S, :radical => Hecke._ideal_from_kgens(S, [preimage(f, x) for x in _zgens(radical(R))]))
  end
  if has_attribute(R, :radical_chain)
    rc = get_attribute(R, :radical_chain)
    set_attribute!(S, :radical_chain => [Hecke._ideal_from_kgens(S, [preimage(f, x) for x in _zgens(rc[i])]) for i in 1:length(rc)])
  end
  return S, f
end

function isomorphism(::Type{FinGenAbGroup}, R::FiniteRing)
  # get the underlying abelian group
  return R.A, x -> FiniteRingElem(R, x), y -> y.a
end
