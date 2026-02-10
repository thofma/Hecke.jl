# To matrix algebra

function isomorphism(::Type{MatAlgebra}, R::FiniteRing)
  p = characteristic(R)
  @req is_prime(p) "Finite ring must have prime characteristic"
  G = additive_generators(R)
  @assert length(G) == length(elementary_divisors(R.A))
  F = GF(p)
  MA = matrix_algebra(F, map_entries.(Ref(F), transpose.(matrix.(R.mult))); isbasis = true) # isbasis = true is important
  iso = hom(R, MA, [MA(F.(x.a.coeff[1,:])) for x in _zgens(R)]; check = false)
  isoinv = hom(MA, R, x -> lift(ZZ, x), [FiniteRingElem(R, R.A(lift.(Ref(ZZ), coefficients(y)))) for y in basis(MA)]; check = false)
  iso.inv = isoinv
  isoinv.inverse = iso
  return iso
end

function isomorphism(::Type{StructureConstantAlgebra}, R::FiniteRing)
  return isomorphism(StructureConstantAlgebra{FqFieldElem}, R)
end

function isomorphism(::Type{StructureConstantAlgebra{T}}, R::FiniteRing) where {T <: FinFieldElem}
  p = exponent(R.A)
  @req is_prime(p) "Characteristic must be prime"
  if T === fpFieldElem
    @req fits(Int, p) "Characteristic ($(p)) too large for fpFieldElem"
    F = Nemo.Native.GF(Int(p))
  elseif T === FpFieldElem
    F = Nemo.Native.GF(p)
  else
    @assert T === FqFieldElem
    F = GF(p)
  end
  G = gens(R.A)
  @assert length(G) == length(elementary_divisors(R.A))
  MA = matrix_algebra(F, map_entries.(Ref(F), transpose.(matrix.(R.mult))); isbasis = true) # isbasis = true is important
  S, StoMA = StructureConstantAlgebra(MA)
  iso = hom(R, S, [preimage(StoMA, MA(F.(x.a.coeff[1,:]))) for x in _zgens(R)]; check = false)
  isoinv = hom(S, R, x -> lift(ZZ, x), [FiniteRingElem(R, R.A(lift.(Ref(ZZ), coefficients(StoMA(y))))) for y in basis(S)]; check = false)
  iso.inv = isoinv
  isoinv.inverse = iso
  if has_attribute(R, :radical)
    set_attribute!(S, :radical => Hecke._ideal_from_kgens(S, [image(iso, x) for x in _zgens(radical(R))]))
  end
  if has_attribute(R, :radical_chain)
    rc = get_attribute(R, :radical_chain)
    set_attribute!(S, :radical_chain => [Hecke._ideal_from_kgens(S, [image(iso, x) for x in _zgens(rc[i])]) for i in 1:length(rc)])
  end
  return iso
end
