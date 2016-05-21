
function lift(a::GenResidue)
  return a.data
end

function ^(a::ResidueElem, f::fmpz)
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

