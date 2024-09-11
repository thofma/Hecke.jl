function _lift(a::PadicFieldElem)
  R = parent(a)
  v = valuation(a)
  if v >= 0
    return QQFieldElem(lift(ZZ, a))
  else
    m = prime(R)^-v
    return QQFieldElem(lift(ZZ, m * a))//m
  end
end

function _coerce(Qp::PadicField, x::PadicFieldElem)
  @assert prime(Qp) == prime(parent(x))
  if precision(x) < precision(Qp)
    error("Precision of field ($(precision(Qp)) larger than precision of element ($(precision(x)))")
  end
  return Qp(_lift(x))
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

function my_log_one_minus(x::PadicFieldElem)
  v = valuation(x)
  lg = parent(x)(0)
  le = 1
  #write x as (1-py_1)(1-p^2y_2)(1-p^4y_3)...
  #with y_i small , i.e. |y_i| <= p^(2^(i-1))
  pp = prime(parent(x), 2)
  X = 1-x
  while true
    y = lift(ZZ, 1-X) % pp
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

function my_log_one_minus_inner(x::EuclideanRingResidueRingElem{QQPolyRingElem}, pr::Int, v::Int, p)
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

function my_log_one_minus(x::QadicFieldElem)
  v = valuation(x)
  lg = parent(x)(0)
  le = 1
  #write x as (1-py_1)(1-p^2y_2)(1-p^4y_3)...
  #with y_i small , i.e. |y_i| <= p^(2^(i-1))
  pp = prime(parent(x))^2
  X = 1-x
  R, _ = polynomial_ring(QQ, cached = false)
  S, _ = residue_ring(R, map_coefficients(x->QQ(lift(ZZ, x)), defining_polynomial(parent(x)), parent = R))
  while true
    Y = 1-X
    y = S(R([lift(ZZ, coeff(Y, i)) % pp for i=0:length(Y)]))
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
