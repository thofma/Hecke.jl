function conjugates_init(f_in::Union{ZZPolyRingElem, QQPolyRingElem})
  local f::ZZPolyRingElem
  if typeof(f_in) == QQPolyRingElem
    f_in = f_in*denominator(f_in)
    gz = Array{ZZRingElem}(undef, length(f_in))
    for i = 1:f_in.length
      gz[i] = FlintZZ(numerator(coeff(f_in, i-1)))
    end
    g = polynomial_ring(FlintZZ, string(var(parent(f_in))), cached = false)[1](gz)
    f = g
  else
    f = f_in
  end
  is_constant(gcd(f, derivative(f))) || error("poly should be square-free")
  c = roots_ctx()
  c.f = f
  r = _roots(f, 100)

  r_d = Array{BigComplex}(undef, 0)
  c_d = Array{BigComplex}(undef, 0)
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
  @assert (length(r_d) + 2*length(c_d) == length(r))
  c.r1 = length(r_d)
  c.r2 = length(c_d)
  sort!(r_d, lt = function(a,b) return real(a) < real(b); end)
  sort!(c_d, lt = function(a,b) return angle(a) < angle(b); end)
  c.r_d = vcat(r_d, c_d)

  c.r = Array{BigComplex}(undef, 0)

  old = precision(BigFloat)
  setprecision(53)
  for i = 1:length(c.r_d)
    push!(c.r, c.r_d[i])
  end
  setprecision(old)

  return c
end

function evaluate(f::QQPolyRingElem, r::BigComplex)
  #Horner - not elegant, but workable
  l = f.length-1
  s = BigComplex(BigFloat(coeff(f, l)))
  for i =l-1:-1:0
    s = s*r+BigComplex(BigFloat(coeff(f, i)))
  end
  return s
end

function evaluate(f::ZZPolyRingElem, r::BigComplex)
  #Horner - not elegant, but workable
  l = f.length-1
  s = BigComplex(coeff(f, l))
  for i =l-1:-1:0
    s = s*r+BigComplex(coeff(f, i))
  end
  return s
end

function hensel_lift(f::ZZPolyRingElem, r::BigComplex)
  return r - evaluate(f, r)/evaluate(derivative(f), r)
end

function conjugates(K::AbsSimpleNumField, p::Int)
  return conjugates(roots_ctx(K), p)
end

function conjugates(c::roots_ctx, p::Int)
  prec = precision(c.r[1])
  while prec < 2*p
    prec *= 2
    for i = 1:length(c.r)
      function _h()
        return hensel_lift(c.f, c.r[i])
      end
      c.r[i] = setprecision(_h, prec)
    end
  end
  return setprecision(c.r, p)
end

function Base.setprecision(a::BigComplex, p::Int)
  return BigComplex(setprecision(a.re, p), setprecision(a.im, p))
end

function Base.setprecision(a::Vector{BigComplex}, p::Int)
  b = Array{BigComplex}(undef, 0);
  for i = 1:length(a)
    push!(b, setprecision(a[i], p))
  end
  return b
end

function minkowski(a::AbsSimpleNumFieldElem, p::Int)
  c = roots_ctx(parent(a))
  x = conjugates_arb(a, p)
  old = precision(BigFloat)
  setprecision(BigFloat, p)
  m = Array{BigFloat}(undef, 0)
  for i=1:c.r1
    v = BigFloat(real(x[i]))
    push!(m, v)
  end
  s2 = sqrt(BigFloat(2))
  for i=1:c.r2
    z = x[c.r1+i]
    push!(m, s2*BigFloat(real(z)))
    push!(m, s2*BigFloat(imag(z)))
  end
  setprecision(BigFloat, old)
  return m
end

function length(a::AbsSimpleNumFieldElem, p::Int = 50)
  m = minkowski(a, p)
  return sum([x*x for x in m])
end


function minkowski_matrix(K::AbsSimpleNumField, p::Int = 50)
  c = roots_ctx(K)

  if isdefined(c, :minkowski_matrix)
    if c.minkowski_mat_p == p
      return c.minkowski_matrix
    elseif c.minkowski_mat_p >= p
      return map(x->setprecision(x, p), c.minkowski_matrix)
    end
  end

  old = precision(BigFloat)
  setprecision(p)

  g = gen(K)
  n = degree(K)
  mm = vcat([minkowski(g^i, p) for i=0:n-1])
  m = Array{BigFloat}(undef, n, n)
  for i=1:n
    for j=1:n
      m[i,j] = mm[i][j]
    end
  end
  c.minkowski_matrix = m
  c.minkowski_mat_p = p
  setprecision(old)
  return m
end
