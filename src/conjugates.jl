

export conjugates_init, is_constant, is_squarefree, conjugates, angle, cos, 
       sin, abs, abs2, sqrt

function is_constant(f::PolyElem)
  return f.length<2
end

function is_squarefree(f::PolyElem)
  return is_constant(gcd(f, derivative(f)))
end

type roots_ctx
  f::fmpz_poly
  r_d::Array{BigComplex, 1}  # the 1st r1 ones will be real
  r::Array{BigComplex, 1}          # the complexes and at the end, the conjugated
  r1::Int
  r2::Int
  function roots_ctx()
    r = new()
    return r
  end
end

function conjugates_init(f::Union(fmpz_poly, fmpq_poly))
  if typeof(f) == fmpq_poly
    f = f*denominator(f)
    g = Array(fmpz, length(f))
    for i = 1:f.length
      g[i] = ZZ(num(coeff(f, i-1)))
    end
    g = PolynomialRing(ZZ, string(var(parent(f))))[1](g)
    f = g
  end
  is_constant(gcd(f, derivative(f))) || error("poly should be square-free")
  c = roots_ctx()
  c.f = f
  r = complex_roots(f, target_prec = 100)

  r_d = Array(BigComplex, 0)
  c_d = Array(BigComplex, 0)
  for i = 1:length(r)
    rr = BigComplex(r[i])
    if Base.abs2(imag(rr)) < 1e-20
      push!(r_d, rr)
      continue
    end
    if imag(rr) > 0 
      push!(c_d, rr)
      continue
    end
  end
  assert(length(r_d) + 2*length(c_d) == length(r))
  c.r1 = length(r_d)
  c.r2 = length(c_d)
  sort!(r_d, lt = function(a,b) return real(a) < real(b); end)
  sort!(c_d, lt = function(a,b) return angle(a) < angle(b); end)
  c.r_d = vcat(r_d, c_d)

  c.r = Array(BigComplex, 0)

  old = get_bigfloat_precision()
  set_bigfloat_precision(53)
  for i = 1:length(c.r_d)
    push!(c.r, c.r_d[i])
  end
  set_bigfloat_precision(old)

  return c
end

function evaluate(f::fmpq_poly, r::BigComplex)
  #Horner - not elegant, but workable
  l = f.length-1
  s = BigComplex(BigFloat(coeff(f, l)))
  for i =l-1:-1:0
    s = s*r+BigComplex(BigFloat(coeff(f, i)))
  end
  return s
end


function evaluate(f::fmpz_poly, r::BigComplex)
  #Horner - not elegant, but workable
  l = f.length-1
  s = BigComplex(coeff(f, l))
  for i =l-1:-1:0
    s = s*r+BigComplex(coeff(f, i))
  end
  return s
end

function hensel_lift(f::fmpz_poly, r::BigComplex)
  return r - evaluate(f, r)/evaluate(derivative(f), r)
end


function conjugates(c::roots_ctx, p::Int)
  prec = precision(c.r[1])
  while prec < 2*p
    prec *= 2
    for i = 1:length(c.r)
      function _h()
        return hensel_lift(c.f, c.r[i])
      end
      c.r[i] = with_bigfloat_precision(_h, prec)
    end
  end
  return set_precision(c.r, p)
end

function set_precision(a::BigFloat, p::Int)
  return with_bigfloat_precision(function() return a*1.0; end, p)
end

function set_precision(a::BigComplex, p::Int)
  return with_bigfloat_precision(function() return BigComplex(a.re*1.0, a.im*1.0); end, p)
end

function set_precision(a::Array{BigComplex, 1}, p::Int)
  b = Array(BigComplex, 0);
  for i = 1:length(a)
    push!(b, set_precision(a[i], p))
  end
  return b
end

function minkowski(c::roots_ctx, a::nf_elem, p::Int)
  r = conjugates(c, p)
  m = Array(BigFloat, 0);
  a = (parent(a).pol.parent)(a)
  s2 = sqrt(BigFloat(2.0))
  for i = 1:c.r1
    push!(m, real(evaluate(a, r[i])))
  end
  for i = 1:c.r2
    z = evaluate(a, r[i+c.r1])
    push!(m, s2*real(z))
    push!(m, s2*imag(z))
  end
  return m
end

function length(c::roots_ctx, a::nf_elem, p::Int = 50)
  m = minkowski(c, a, p)
  return sum([x*x for x in m])
end

function minkowski_mat(c::roots_ctx, K::NfNumberField, p::Int)
  old = get_bigfloat_precision()
  set_bigfloat_precision(p)
  r = conjugates(c, p)
  d = Array(typeof(r[1]), length(r))
  one = BigComplex(BigFloat(1.0), BigFloat(0.0))
  s2 = Base.sqrt(BigFloat(2.0))
  for i = 1:length(r)
    d[i] = one
  end

  n = degree(K)
  m = Array(BigFloat, n, n)

  for i = 1:n
    for j = 1:c.r1
      m[i,j] = real(d[j])
      if i < n
        d[j] = d[j] * r[j]
      end
    end
    for j=1:c.r2
      m[i, 2*j+c.r1-1] = s2*real(d[j+c.r1])
      m[i, 2*j+c.r1] = s2*imag(d[j+c.r1])
      if i < n
        d[j+c.r1] = d[j+c.r1]*r[j+c.r1]
      end
    end
  end
  set_bigfloat_precision(old)
  return m
end

function *(a::fmpz_mat, b::Array{BigFloat, 2})
  s = Base.size(b)
  cols(a) == s[1] || error("dimensions do not match")

  c = Array(BigFloat, rows(a), s[2])
  A = ZZ()
  for i = 1:rows(a)
    for j = 1:s[2]
      t = zero(b[1,1])
      for k = 1:cols(a)
        getindex!(A, a, i, k)
        t += A * b[k, j]
      end
      c[i,j] = t
    end
  end
  return c
end

for (s,f) in ((:trunc, Base.trunc), (:round, Base.round), (:ceil, Base.ceil), (:floor, Base.floor))
  @eval begin
    function ($s)(a::Array{BigFloat, 2})
      s = Base.size(a)
      m = MatrixSpace(ZZ, s[1], s[2])()
      for i = 1:s[1]
        for j = 1:s[2]
          m[i,j] = ZZ(BigInt(($f)(a[i,j])))
        end
      end
      return m
    end
  end
end
