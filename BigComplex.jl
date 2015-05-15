
export BigComplex, abs2, precision, conj, atan2, angle

type BigComplex 
  re::BigFloat
  im::BigFloat
  function BigComplex(r::BigFloat)
    c = new()
    c.re = r
    c.im = zero(r)
    return c
  end

  function BigComplex(r::BigInt)
    return BigComplex(BigFloat(r))
  end

  function BigComplex(r::fmpz)
    return BigComplex(BigFloat(BigInt(r)))
  end

  function BigComplex(r::BigFloat, i::BigFloat)
    c = new()
    c.re = r
    c.im = i
    return c
  end

  function BigComplex(r::Complex{Float64})
    return BigComplex(BigFloat(Base.real(r)), BigFloat(Base.imag(r)))
  end

  function BigComplex(r::acb_t)
    return BigComplex(BigFloat(midpoint(real(r))), BigFloat(midpoint(imag(r))))
  end
end

function show(io::IO, a::BigComplex)
  print(io, a.re, " + ", a.im, "im")
end

function +(a::BigComplex, b::BigComplex)
  return BigComplex(a.re + b.re, a.im + b.im)
end

function -(a::BigComplex, b::BigComplex)
  return BigComplex(a.re - b.re, a.im - b.im)
end

function -(a::BigComplex)
  return BigComplex(-a.re, -a.im)
end

function *(a::BigComplex, b::BigComplex)
  return BigComplex(a.re*b.re - a.im*b.im, a.re*b.im + a.im*b.re)
end

function +(a::BigComplex, b::BigFloat)
  return BigComplex(a.re + b, a.im)
end

function *(a::BigComplex, b::BigFloat)
  return BigComplex(a.re * b, a.im * b)
end

function *(a::BigFloat, b::BigComplex)
  return BigComplex(b.re * a, b.im * a)
end

function /(a::BigComplex, b::BigComplex)
  return a*conj(b)/abs2(b)
end

function conj(a::BigComplex)
  return BigComplex(a.re, -a.im)
end

function abs2(a::BigComplex)
  return a.re^2 + a.im^2
end

function angle(a::BigComplex)
  return atan2(imag(a), real(a))
end

function /(a::BigComplex, b::BigFloat)
  return BigComplex(a.re/b, a.im/b)
end

function precision(a::BigComplex)
  return min(Base.precision(a.re), Base.precision(a.im))
end

function real(a::BigComplex)
  return a.re
end

function imag(a::BigComplex)
  return a.im
end
