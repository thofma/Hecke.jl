
function lift(a::Generic.Res)
  return a.data
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
  ccall((:fq_nmod_set, :libflint), Void,
          (Ptr{fq_nmod}, Ptr{fq_nmod}, Ptr{FqNmodFiniteField}),
          &z, &x, &parent(z))
end

