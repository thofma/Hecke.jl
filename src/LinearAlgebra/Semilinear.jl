function _semilinear_kernel(A::MatElem{<:FinField}, p)
  # p must be the characteristic of base_ring(A)
  F = base_ring(A)
  @assert characteristic(F) == p
  if order(F) == p # prime field, then
    # if F = F_p, then p-similinear = linear
    return kernel(A; side = :left)
  end
  # x -> x^p is surjective, so we find a kernel and just take the preimage
  K = kernel(A; side = :left)
  return map_entries(x -> absolute_frobenius(x, -1), K)
end

function _semilinear_kernel(A::MatElem{<:Generic.RationalFunctionFieldElem{<:FinFieldElem, <:PolyRingElem{<:FinFieldElem}}}, p)
  F = base_ring(A)
  K = kernel(A; side = :left)
  return _intersect_with_pspan(K)
end

function absolute_frobenius_inverse(x::FinFieldElem)
  return absolute_frobenius(x, -1)
end

function absolute_frobenius_inverse(x::PolyRingElem)
  Fx = parent(x)
  F = base_ring(Fx)
  p = Int(characteristic(F))
  d = div(degree(x), p)
  coe = elem_type(base_ring(x))[zero(F) for i in 0:(d + 1)]
  for i in 0:degree(x)
    e, r = divrem(i, p)
    if r != 0
      @assert is_zero(coeff(x, i))
    else
      coe[e + 1] = absolute_frobenius_inverse(coeff(x, i))
    end
  end
  y = Fx(coe)
  return y
end

function absolute_frobenius_inverse(x::Generic.FracFieldElem{<:PolyRingElem{<:FinFieldElem}})
  K = parent(x)
  return K(absolute_frobenius_inverse(numerator(x)),
           absolute_frobenius_inverse(denominator(x)),
           reduce = true)
end

function absolute_frobenius_inverse(x::Generic.RationalFunctionFieldElem{<:FinFieldElem, <:PolyRingElem{<:FinFieldElem}})
  return parent(x)(absolute_frobenius_inverse(data(x)))
end

_elem_to_polynomial(x) = numerator(x)(gen(parent(defining_polynomial(parent(x)))))/denominator(x)

function absolute_frobenius_inverse(x::Generic.FunctionFieldElem)
  # We need to write x as a polynomial in alpha^p
  # we have as a polynomial in alpha
  # so lets write alpha as a polynomial in alpha^p
  K = parent(x)
  k = base_ring(K)
  d = degree(K)
  alpha = gen(K)
  p = Int(characteristic(K))
  alphappows =  [_elem_to_polynomial(alpha^(p*i)) for i in 0:d-1]
  fl, xinalphap = can_solve_with_solution(matrix(k, [coeff.(f, 0:d-1) for f in alphappows]), coeff.(_elem_to_polynomial(x),0:d-1))
  return K(absolute_frobenius_inverse.(xinalphap))
end

function _intersect_with_pspan(A::MatElem{<:Generic.RationalFunctionFieldElem{<:FinFieldElem, <:PolyRingElem{<:FinFieldElem}}})
  # F is f.g. over perfect field and we have an F-basis of derivations
  # Thus something is p-th power if and only if it is in the kernel of the
  # derivations
  M = map_entries(derivative, A)
  R, T = echelon_form_with_transformation(M)
  @assert T * M == R
  n = something(findfirst(i -> is_zero_row(R, i), 1:nrows(R)), nrows(R) + 1)
  # n is the nullity of R
  bas = T[n:nrows(T), :] * A
  # we promise to alwayss return x such that x .^ p * A = 0
  # so let's take p-th roots
  return map_entries(absolute_frobenius_inverse, bas)
end

function _intersect_with_pspan(A::MatElem{<:FinFieldElem})
  # F is f.g. over perfect field and we have an F-basis of derivations
  # Thus something is p-th power if and only if it is in the kernel of the
  # derivations
  return map_entries(absolute_frobenius_inverse, A)
end
