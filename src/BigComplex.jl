import Base: abs2, angle, convert, exponent


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
  # atan2
  return atan(imag(a), real(a))
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
