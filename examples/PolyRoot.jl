module PolyRoot

using Hecke

function is_power(f::PolyRingElem{T}, n::Int) where {T <: FieldElem}
  #iteration is for roots of x^-n -f^(n-1) which has root f^((1-n)/n)
  #or root(f, n)^(1-n)

  # in pos. char, needs to split
  degree(f) % n == 0 || return false, f
  v, f = remove(f, gen(parent(f)))
  v % n == 0 || return false, f
  lc = constant_coefficient(f)
  fl, lc = Hecke.is_power(lc, n)
  fl || return false, f
  lc = inv(lc^(n-1))
  inv_n = inv(base_ring(f)(n))
  d = divexact(degree(f), n)+1
  r = parent(f)(lc)
  b = powermod(f, n-1, gen(parent(f))^d)
  p = 1
  while p < d
    r = r*(1+inv_n)-b*inv_n*powermod(r, n+1, gen(parent(f))^d)
    p *= 2
  end
  r = (f*r) % gen(parent(f))^d
  #this is the ONLY possible candidate
  #(think about n-th roots of 1 - maybe only other roots lift?)
  #NO: this is a purely transcendental extension, roots of unity are in
  #base_ring or don't come in.
  r = shift_left(r, div(v, n))
  if leading_coefficient(r)^n != leading_coefficient(f)
    return false, r
  end
  return true, r
end

end
