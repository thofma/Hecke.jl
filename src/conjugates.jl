
export conjugates_init, isconstant, issquarefree, conjugates, angle, cos, 
       sin, abs, abs2, sqrt

function isconstant(f::PolyElem)
  return f.length<2
end

function issquarefree(f::PolyElem)
  return isconstant(gcd(f, derivative(f)))
end

function conjugates_init(f::Union{fmpz_poly, fmpq_poly})
  if typeof(f) == fmpq_poly
    f = f*denominator(f)
    g = Array{fmpz}(length(f))
    for i = 1:f.length
      g[i] = FlintZZ(numerator(coeff(f, i-1)))
    end
    g = PolynomialRing(FlintZZ, string(var(parent(f))))[1](g)
    f = g
  end
  isconstant(gcd(f, derivative(f))) || error("poly should be square-free")
  c = roots_ctx()
  c.f = f
  r = _roots(f, 100)

  r_d = Array{BigComplex}(0)
  c_d = Array{BigComplex}(0)
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

  c.r = Array{BigComplex}(0)

  old = precision(BigFloat)
  setprecision(53)
  for i = 1:length(c.r_d)
    push!(c.r, c.r_d[i])
  end
  setprecision(old)

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

function evaluate(f::fmpq_poly, r::T) where T <: RingElem
  R = parent(r)
  if iszero(f)
    return zero(R)
  end
  l = length(f) - 1
  s = R(coeff(f, l))
  for i in l-1:-1:0
    s = s*r + R(coeff(f, i))
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

function conjugates(K::AnticNumberField, p::Int)
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
  return set_precision(c.r, p)
end

function set_precision(a::BigFloat, p::Int)
  return setprecision(function() return a*1.0; end, p)
end

function set_precision(a::BigComplex, p::Int)
  return setprecision(function() return BigComplex(a.re*1.0, a.im*1.0); end, p)
end

function set_precision(a::Array{BigComplex, 1}, p::Int)
  b = Array{BigComplex}(0);
  for i = 1:length(a)
    push!(b, set_precision(a[i], p))
  end
  return b
end

function minkowski(a::nf_elem, p::Int)
  c = roots_ctx(parent(a))
  x = conjugates_arb(a, p)
  m = Array{BigFloat}(0)
  for i=1:c.r1
    push!(m, BigFloat(real(x[i])))
  end
  s2 = sqrt(BigFloat(2))
  for i=1:c.r2
    z = x[c.r1+i]
    push!(m, s2*BigFloat(real(z)))
    push!(m, s2*BigFloat(imag(z)))
  end
  return m


  r = conjugates(c, p)
  m = Array{BigFloat}(0);
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

function length(a::nf_elem, p::Int = 50)
  m = minkowski(a, p)
  return sum([x*x for x in m])
end

function setprecision!(x::BigFloat, p::Int)
  ccall((:mpfr_prec_round, :libmpfr), Void, (Ref{BigFloat}, Clong, Int32), x, p, Base.MPFR.ROUNDING_MODE[])
end

function Base.setprecision(x::BigFloat, p::Int)
  setprecision(BigFloat, p) do
    y = BigFloat()
    ccall((:mpfr_set, :libmpfr), Void, (Ref{BigFloat}, Ref{BigFloat}, Int32), y, x, Base.MPFR.ROUNDING_MODE[])
    return y
  end
end


function minkowski_mat(c::roots_ctx, p::Int)
  if isdefined(c, :minkowski_mat) 
    if c.minkowski_mat_p == p
      return c.minkowski_mat
    elseif c.minkowski_mat_p > p
      return map(x->setprecision(x, p), c.minkowski_mat)
    end
  end
  old = precision(BigFloat)
  setprecision(p)
  m = vcat([minkowski(g^i, p) for i=0:n-1])
  setprecision(old)
  c.minkowski_mat = m
  c.minkowski_mat_p = p
  return m

  r = conjugates(c, p)
  d = Array{typeof(r[1])}(length(r))
  one = BigComplex(BigFloat(1.0), BigFloat(0.0))
  s2 = Base.sqrt(BigFloat(2.0))
  for i = 1:length(r)
    d[i] = deepcopy(one)
  end

  n = degree(c.f)
  m = Array{BigFloat}(n, n)

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
  setprecision(old)
  c.minkowski_mat = m
  c.minkowski_mat_p = p
  return m
end

function minkowski_mat(K::AnticNumberField, p::Int = 50)
  c = roots_ctx(K)

  if false && isdefined(c, :minkowski_mat) && c.minkowski_mat_p == p
    return c.minkowski_mat
  end
  old = precision(BigFloat)
  setprecision(p)

  g = gen(K)
  n = degree(K)
  mm = vcat([minkowski(g^i, p) for i=0:n-1])
  m = Array{BigFloat}(n,n)
  for i=1:n
    for j=1:n
      m[i,j] = mm[i][j]
    end
  end
  setprecision(old)
  c.minkowski_mat = m
  c.minkowski_mat_p = p
  return m
end

function mult!(c::Array{BigFloat, 2}, a::fmpz_mat, b::Array{BigFloat, 2})
  error("dont")
  s = Base.size(b)
  t = Base.size(c)
  cols(a) == s[1] || error("dimensions do not match")
  rows(a) == t[1] || error("dimensions do not match")
  t[2] == s[2]    || error("dimensions do not match")

  R = RealRing()
  tmp_mpz = R.z1
  tmp_mpz_r = R.t1
  tmp_mpfr = deepcopy(c[1,1]) #R.t2

  ##CF: careful: one SHOULD use mpfr_mul_z, but this converts to
  ##    mpfr every time. I think mpfr_mul_z should be re-written
  ##    to directly operate. Hoever, this is not going to happen soon.
  for i = 1:rows(a)
    for j = 1:t[2]
      if isdefined(c, i, j)
        ccall((:mpfr_set_zero, :libmpfr), Void, (Ptr{BigFloat}, Int), &c[i,j], 0)
      else
        c[i,j] = BigFloat(0)
      end

    end
    for j = 1:cols(a)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz},
        (Ptr{fmpz_mat}, Int, Int), &a, i - 1, j - 1)
      ccall((:flint_mpz_init_set_readonly, :libflint),
        Void, (Ptr{BigInt}, Ptr{fmpz}), &tmp_mpz, z)
      ccall((:mpfr_set_z, :libmpfr), Void, (Ptr{BigFloat}, Ptr{BigInt}, Int32),
        &tmp_mpz_r, &tmp_mpz, __get_rounding_mode())
      for k = 1:s[2]
        ccall((:mpfr_mul, :libmpfr), Int, (Ptr{BigFloat}, Ptr{BigFloat}, Ptr{BigFloat}, Int32), &tmp_mpfr, &b[j,k], &tmp_mpz_r, Base.MPFR.ROUNDING_MODE[end])
        ccall((:mpfr_add, :libmpfr), Int, (Ptr{BigFloat}, Ptr{BigFloat}, Ptr{BigFloat}, Int32), &c[i,k], &tmp_mpfr, &c[i,k], Base.MPFR.ROUNDING_MODE[end])
      end
#      ccall((:flint_mpz_clear_readonly, :libflint), Void, (Ptr{BigInt}), &tmp_mpz)
    end
  end
  return c
end


function *(a::fmpz_mat, b::Array{BigFloat, 2})
  s = Base.size(b)
  cols(a) == s[1] || error("dimensions do not match")

  c = Array{BigFloat}(rows(a), s[2])
  return mult!(c, a, b)
end

for (s,f) in ((:trunc, Base.trunc), (:round, Base.round), (:ceil, Base.ceil), (:floor, Base.floor))
  @eval begin
    function ($s)(a::Array{BigFloat, 2})
      s = Base.size(a)
      m = zero_matrix(FlintZZ, s[1], s[2])
      for i = 1:s[1]
        for j = 1:s[2]
          m[i,j] = FlintZZ(BigInt(($f)(a[i,j])))
        end
      end
      return m
    end
  end
end
