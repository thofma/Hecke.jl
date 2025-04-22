density(f::PolyRingElem) = length(findall(x->!iszero(x), coefficients(f)))/length(f)

#move elsewhere? Not used in here
function Hecke.representation_matrix(a::ResElem{<:PolyRingElem})
  R = parent(a)
  S = base_ring(base_ring(R))
  n = degree(modulus(R))
  m = zero_matrix(S, n, n)
  for i=0:n-1
    m[1, i+1] = coeff(a.data, i)
  end
  for j=2:n
    a *= gen(R)
    for i=0:n-1
      m[j, i+1] = coeff(a.data, i)
    end
  end
  return m
end

