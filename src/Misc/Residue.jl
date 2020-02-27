
function lift(a::Generic.Res)
  return a.data
end

function lift(a::Generic.ResF)
  return a.data
end

function lift(a::Nemo.nmod)
  return fmpz(a.data)
end

function lift(a::Nemo.gfp_elem)
  return fmpz(a.data)
end

function ^(a::ResElem, f::fmpz)
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

function set!(z::fq_nmod, x::fq_nmod)
  ccall((:fq_nmod_set, libflint), Nothing,
          (Ref{fq_nmod}, Ref{fq_nmod}, Ref{FqNmodFiniteField}),
          z, x, parent(z))
end

characterstic(F::Generic.ResField{fmpz}) = abs(F.modulus)
