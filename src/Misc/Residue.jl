function divexact(a::ZZModRingElem, y::ZZRingElem; check::Bool = true)
  return divexact(a, parent(a)(y), check = check)
end

function lift(a::Generic.ResidueRingElem)
  return a.data
end

function lift(a::Generic.ResidueFieldElem)
  return a.data
end

function ^(a::ResElem, f::ZZRingElem)
  f==0 && return one(parent(a))
  f==1 && return a
  if f<0
    f=-f
    a = inv(a)
  end
  if f<(1<<30)
    return a^Int(f)
  end
  b = a^(div(f, 2))
  b = b^2
  if isodd(f)
    b *= a
  end
  return b
end

function set!(z::fqPolyRepFieldElem, x::fqPolyRepFieldElem)
  ccall((:fq_nmod_set, libflint), Nothing,
          (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Ref{fqPolyRepField}),
          z, x, parent(z))
end

characteristic(F::Generic.ResidueField{ZZRingElem}) = abs(F.modulus)
