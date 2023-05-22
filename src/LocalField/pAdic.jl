@doc raw"""
    lift(a::padic) -> ZZRingElem

Returns the positive canonical representative in $\mathbb{Z}$. $a$ needs
to be integral.
"""
function lift(a::padic)
  b = ZZRingElem()
  R = parent(a)

  if iszero(a)
    return ZZ(0)
  end
  ccall((:padic_get_fmpz, libflint), Nothing, (Ref{ZZRingElem}, Ref{padic}, Ref{FlintPadicField}), b, a, R)
  return b
end

function _lift(a::padic)
  R = parent(a)
  v = valuation(a)
  if v >= 0
    return QQFieldElem(lift(a))
  else
    m = prime(R)^-v
    return QQFieldElem(lift(m * a))//m
  end
end

function Base.setprecision(f::Generic.Poly{padic}, N::Int)
  g = parent(f)()
  fit!(g, length(f))
  for i=1:length(f)
    g.coeffs[i] = setprecision!(f.coeffs[i], N)
  end
  set_length!(g, normalise(g, length(f)))
  return g
end

function setprecision!(f::Generic.Poly{padic}, N::Int)
  for i=1:length(f)
    f.coeffs[i] = setprecision!(f.coeffs[i], N)
  end
  return f
end

"""
The log of `1-x`, x needs to have a valuation >1
"""
function my_log_one_minus_inner(x::ZZRingElem, pr::Int, v::Int, p)
  #need N s.th. Nv-log_p(N) >= pr
  #as a function of N, this has a min at log(p)/v
  #the N needs to > pr/v + s.th. small
  lp = log(p)
  N = div(pr, v) + 1
  while N*v-log(N)/lp < pr
    @show N += 1
  end
  return -x*my_eval(map(i->QQFieldElem(1, i), 1:N), QQFieldElem(x))
end

function my_log_one_minus(x::padic)
  v = valuation(x)
  lg = parent(x)(0)
  le = 1
  #write x as (1-py_1)(1-p^2y_2)(1-p^4y_3)...
  #with y_i small , i.e. |y_i| <= p^(2^(i-1))
  pp = prime(parent(x), 2)
  X = 1-x
  while true
    y = lift(1-X) % pp
    lg += parent(x)(my_log_one_minus_inner(y, precision(x), le, prime(parent(x))))
    X = X*inv(parent(x)(1-y))
    pp *= pp
    le *= 2
    if isone(X) || le >= precision(x)
      return lg
    end
    @assert valuation(X-1) >= le
  end

end

function my_log_one_minus_inner(x::Generic.ResidueRingElem{QQPolyRingElem}, pr::Int, v::Int, p)
  #need N s.th. Nv-log_p(N) >= pr
  #as a function of N, this has a min at log(p)/v
  #the N needs to > pr/v + s.th. small
  lp = log(p)
  N = div(pr, v) + 1
  while N*v-log(N)/lp < pr
    @show N += 1
  end
  R = parent(x)
  return -x*my_eval(map(i->R(QQFieldElem(1, i)), 1:N), x)
end

function my_log_one_minus(x::qadic)
  v = valuation(x)
  lg = parent(x)(0)
  le = 1
  #write x as (1-py_1)(1-p^2y_2)(1-p^4y_3)...
  #with y_i small , i.e. |y_i| <= p^(2^(i-1))
  pp = prime(parent(x))^2
  X = 1-x
  R, _ = polynomial_ring(QQ, cached = false)
  S = residue_ring(R, map_coefficients(x->QQ(lift(x)), defining_polynomial(parent(x)), parent = R))
  while true
    Y = 1-X
    y = S(R([lift(coeff(Y, i)) % pp for i=0:length(Y)]))
    lg += parent(x)(my_log_one_minus_inner(y, precision(x), le, prime(parent(x))).data)
    X = X*inv(parent(x)(1-y.data))
    pp *= pp
    le *= 2
    if isone(X) || le >= precision(x)
      return lg
    end
    @assert valuation(X-1) >= le
  end

end
