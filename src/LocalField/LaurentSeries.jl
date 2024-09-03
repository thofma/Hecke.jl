characteristic(K::Generic.LaurentSeriesField{<:FinFieldElem}) = characteristic(base_ring(K))

function uniformizer(K::Generic.LaurentSeriesField{<:FinFieldElem}, k::Int = 1; prec = max_precision(K))
  return set_precision!(gen(K)^k, prec)
end

absolute_ramification_index(K::Generic.LaurentSeriesField{<:FinFieldElem}) = ZZ(1)

_valuation_integral(a::Generic.LaurentSeriesFieldElem{<:FinFieldElem}) = valuation(a)

function residue_field(K::Generic.LaurentSeriesField{T}) where {T <: FinFieldElem}
  mk = get_attribute(K, :ResidueField)
  if mk !== nothing
    return codomain(mk), mk
  end
  k = base_ring(K)
  Ktok = function(x::Generic.LaurentSeriesFieldElem{T})
    valuation(x) < 0 && error("The element is not integral")
    return coeff(x, 0)
  end
  ktoK = function(x::T)
    return K(x)
  end
  mk = MapFromFunc(K, k, Ktok, ktoK)
  set_attribute!(K, :ResidueField => mk)
  return k, mk
end

setprecision!(a::Generic.LaurentSeriesFieldElem, k::Int) = set_precision!(a, k)
setprecision(a::Generic.LaurentSeriesFieldElem, k::Int) = set_precision!(deepcopy(a), k)
