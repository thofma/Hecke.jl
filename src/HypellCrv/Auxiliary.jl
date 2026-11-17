
################################################################################
#
#  Helper functions for genus 2 curves.
#
################################################################################


function derivative(f::MPolyRingElem{T}, x::MPolyRingElem{T}, n::Int) where T
  @req n >= 0 "n needs to be non-zero."
  i = 0
  while n > i
    f = derivative(f, x)
    i += 1
  end
return f
end

function derivative(f::MPolyRingElem{T}, exponents::Vector{Int}) where T
  for i in (1:length(exponents))
    n = exponents[i]
    for j in (1:n)
      f = derivative(f, i)
    end
  end
return f
end


function gcdx(f::ZZRingElem, g::ZZRingElem, hs::ZZRingElem...)
  fs = ZZRingElem[f,g,hs...]
  n = length(fs)
  M = matrix(ZZ,n,1,fs)
  result = hnf_with_transform(M)
  return tuple(result[1][1,1], result[2][1,:]...)
end

function gcdx(fs::AbstractArray{ZZRingElem})
  length(fs) > 0 || error("Empty collection")
  n = length(fs)
  M = matrix(ZZ,n,1,fs)
  result = hnf_with_transform(M)
  return result[1][1,1], result[2][1,:]
end

# Given a linear equation of the form f(x, y) = a * x + b * y = 0,
# find the minimal x_0, y_0 such that f(x_0, y_0) = 0.
function minimize_linear_equation(f::MPolyRingElem{QQFieldElem})
  R = parent(f)
  x, y = gens(R)

  a_num = numerator(coeff(f, x)) 
  a_den = denominator(coeff(f, x))

  b_num = numerator(coeff(f, y)) 
  b_den = denominator(coeff(f,y))

  gcd_ab = gcd([a_num * b_den, b_num * a_den, a_den * b_den])

  C1 = divexact(a_num * b_den, gcd_ab)
  C2 = divexact(b_num * a_den, gcd_ab)
  C3 = divexact(a_den * b_den, gcd_ab)

  _, x0, y0 = C3 * collect(gcdx(C1, C2))

  return x0, y0
end

function trace_one_element(F::FinField)
  if is_odd(degree(F))
    return F(1)
  end
  while true
    x = rand(F)
    t = trace(x)
    if t != 0
      return x/t
    end
  end
end

function coerce_to_base_field(a::FqFieldElem)
  f_min = minpoly(a)
  if degree(f_min) ==1
    return roots(f_min)[1]
  else
    error("Can't coerce to base field.")
  end
end
