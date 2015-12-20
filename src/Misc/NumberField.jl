import Nemo.AnticNumberField

################################################################################
#
# convenience ...
#
################################################################################

#CF: we have to "extend" AnticNumberField as NumberField is just defined by
#    NumberField = AnticNumberField in Nemo.
#    Possibly should be replaced by having optional 2nd arguments?

function AnticNumberField(f::fmpq_poly)
  return NumberField(f, "_a")
end

function AnticNumberField(f::fmpz_poly, s::Symbol)
  Qx, x = PolynomialRing(QQ, parent(f).S)
  return NumberField(Qx(f), s)
end

function AnticNumberField(f::fmpz_poly, s::AbstractString)
  Qx, x = PolynomialRing(QQ, parent(f).S)
  return NumberField(Qx(f), s)
end

function AnticNumberField(f::fmpz_poly)
  Qx, x = PolynomialRing(QQ, parent(f).S)
  return NumberField(Qx(f))
end

################################################################################
# given a basis (an array of elements), get a linear combination with
# random integral coefficients
################################################################################

function rand(b::Array{nf_elem,1}, r::UnitRange)
  length(b) == 0 && error("Array must not be empty")

  s = zero(b[1].parent)
  t = zero(b[1].parent)

  for i = 1:length(b)
    mul!(t, b[i], rand(r))
    add!(s, t, s)
  end
  return s
end

function rand!(c::nf_elem, b::Array{nf_elem,1}, r::UnitRange)
  length(b) == 0 && error("Array must not be empty")

  mul!(c, b[1], rand(r))
  t = zero(b[1].parent)

  for i = 2:length(b)
    mul!(t, b[i], rand(r))
    add!(c, t, c)
  end
  nothing
end

################################################################################
#
#  fmpq_poly with denominator 1 to fmpz_poly
#
################################################################################

function Base.call(a::FmpzPolyRing, b::fmpq_poly)
  (den(b) != 1) && error("denominator has to be 1")
  z = a()
  ccall((:fmpq_poly_get_numerator, :libflint), Void,
              (Ptr{fmpz_poly}, Ptr{fmpq_poly}), &z, &b)
  return z
end

function basis(K::AnticNumberField)
  n = degree(K)
  g = gen(K);
  d = Array(typeof(g), n)
  b = K(1)
  for i = 1:n-1
    d[i] = b
    b *= g
  end
  d[n] = b
  return d
end

function representation_mat(a::nf_elem)
  @assert den(a) == 1
  dummy = fmpz(0)
  n = degree(a.parent)
  M = MatrixSpace(FlintZZ, n,n)()::fmpz_mat
  t = gen(a.parent)
  b = a
  for i = 1:n-1
    elem_to_mat_row!(M, i, dummy, b)
    b *= t
  end
  elem_to_mat_row!(M, n, dummy, b)
  return M
end 

function set_den!(a::nf_elem, d::fmpz)
  ccall((:nf_elem_set_den, :libflint), 
        Void, 
       (Ptr{Nemo.nf_elem}, Ptr{Nemo.fmpz}, Ptr{Nemo.AnticNumberField}), 
       &a, &d, &parent(a))
end

function factor(f::PolyElem{nf_elem})
  Kx = parent(f)
  K = base_ring(f)
  Qy = parent(K.pol)
  y = gen(Qy)
  Qyx, x = PolynomialRing(Qy, "x")
  
  Qx = PolynomialRing(QQ, "x")[1]
  Qxy = PolynomialRing(Qx, "y")[1]

  k = 0
  N = zero(Qxy)

  T = zero(Qxy)
  for i in 0:degree(K.pol)
    T = T + coeff(K.pol, i)*gen(Qxy)^i
  end

  g = f

  while true
    G = zero(Qyx)
    for i in 0:degree(g)
      G = G + Qy(coeff(g, i))*x^i
    end

    Gcompose = G

    # Switch the place of the variables

    H = zero(Qxy)

    for i in 0:degree(Gcompose)
      t = coeff(Gcompose, i)
      HH = zero(Qxy)
      for j in 0:degree(t)
        HH = HH + coeff(t, j)*gen(Qxy)^j
      end
      H = H + HH*gen(Qx)^i
    end

    N = resultant(T, H)

    if !is_constant(N) && is_squarefree(N)
      break
    end

    k = k + 1
    g = compose(f, gen(Kx) - k*gen(K))
  end
  
  fac = factor(N)

  res = Array(PolyElem{nf_elem}, fac.len)

  for i in 1:fac.len
    t = zero(Kx)
    for j in 0:degree(fac[i][1])
      t = t + K(coeff(fac[i][1], j))*gen(Kx)^j
    end
    t = compose(t, gen(Kx) + k*gen(K))
    res[i] = gcd(f, t)
  end

  return res
end

################################################################################
#
# Operations for nf_elem
#
################################################################################

function hash(a::nf_elem)
   h = 0xc2a44fbe466a1827%UInt
   for i in 1:degree(parent(a)) + 1
         h $= hash(coeff(a, i))
         h = (h << 1) | (h >> (sizeof(Int)*8 - 1))
   end
   return h
end

function gen!(r::nf_elem)
   a = parent(r)
   ccall((:nf_elem_gen, :libflint), Void, 
         (Ptr{nf_elem}, Ptr{AnticNumberField}), &r, &a)
   return r
end

function one!(r::nf_elem)
   a = parent(r)
   ccall((:nf_elem_one, :libflint), Void, 
         (Ptr{nf_elem}, Ptr{AnticNumberField}), &r, &a)
   return r
end

function zero!(r::nf_elem)
   a = parent(r)
   ccall((:nf_elem_zero, :libflint), Void, 
         (Ptr{nf_elem}, Ptr{AnticNumberField}), &r, &a)
   return r
end

*(a::nf_elem, b::Integer) = a * fmpz(b)

//(a::Integer, b::nf_elem) = parent(b)(a)//b

function norm_div(a::nf_elem, d::fmpz, nb::Int)
   z = fmpq()
   ccall((:nf_elem_norm_div, :libflint), Void,
         (Ptr{fmpq}, Ptr{nf_elem}, Ptr{AnticNumberField}, Ptr{fmpz}, UInt),
         &z, &a, &a.parent, &d, UInt(nb))
   return z
end


function sub!(a::nf_elem, b::nf_elem, c::nf_elem)
   ccall((:nf_elem_sub, :libflint), Void,
         (Ptr{nf_elem}, Ptr{nf_elem}, Ptr{nf_elem}, Ptr{AnticNumberField}),
 
         &a, &b, &c, &a.parent)
end

