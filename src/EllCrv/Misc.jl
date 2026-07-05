#################################################################################
#
#             EllipticCurve/Misc.jl : Misc functions
#
################################################################################

###############################################################################
#
#  Computing all divisors
#
################################################################################

@doc raw"""
    squaredivisors(n::ZZRingElem) -> Iterator

Computes the numbers whose square divides a given number $n$. It is assumed
that $n$ is not zero.
"""
function squaredivisors(n)
  n == 0 && error("The number must be nonzero")
  return Divisors(n, units = true, power = 2)
end

################################################################################
#
#  Misc
#
################################################################################

function smod(a::T, b::S) where {T, S}
  z = mod(a, b)
  if 2*z > b
    z = z - b
  end
  return z
end

@doc raw"""
	normal_basis(K::FinField, L::FinField) -> FinFieldElem

Return a normal element of $L$ over $K = \mathbf F_q$, i.e. an
element $a$ in L such that 1, a^q, a^(q^2), ..., a^(q^n) forms
a K-basis of L.
"""
function normal_basis(K::T, L::T) where T<:FinField

  p1 = characteristic(K)
  p2 = characteristic(L)

  r1 = degree(K)
  r2 = degree(L)

  q = p1^r1

  @assert p1 == p2
  n = divexact(r2, r1)
  while true
    alpha = rand(L)
    a = [alpha^(q^i) for i in (0:n-1)]
    M = matrix([tr(i * j) for i in a, j in a])
    if !iszero(det(M))
      return alpha
    end
  end
end


function mod(a::AbsSimpleNumFieldElem, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  R = order(I)
  k, phi = residue_field(R, I)
  a_num = phi(R(numerator(a)))
  a_denom = phi(R(denominator(a)))
  b = a_num//a_denom
  return preimage(phi, b)
end

@doc raw"""
	inv_mod(a::AbsSimpleNumFieldOrderElem, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> AbsSimpleNumFieldOrderElem

Return a lift of the inverse of an element modulo a prime ideal.
"""
function Base.invmod(a::AbsSimpleNumFieldOrderElem, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  R = order(I)
  k, phi = residue_field(R, I)
  return preimage(phi, inv(phi(R(a))))
end

function Base.invmod(a::AbsSimpleNumFieldElem, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  R = order(I)
  k, phi = residue_field(R, I)
  a_num = phi(R(numerator(a)))
  a_denom = phi(R(denominator(a)))
  b = a_num//a_denom
  return preimage(phi, inv(b))
end

@doc raw"""
	pth_root_mod(a::AbsSimpleNumFieldOrderElem, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> AbsSimpleNumFieldOrderElem

Return a lift of the pth root of an element mod a prime ideal lying over p.
"""
function pth_root_mod(a::AbsSimpleNumFieldOrderElem, pIdeal::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  R = order(pIdeal)
  p = pIdeal.gen_one
  k, phi = residue_field(R, pIdeal)
  return preimage(phi, pth_root(phi(R(a))))
end

function pth_root_mod(a::AbsSimpleNumFieldElem, pIdeal::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  R = order(pIdeal)
  p = pIdeal.gen_one
  k, phi = residue_field(R, pIdeal)
  a_num = phi(R(numerator(a)))
  a_denom = phi(R(denominator(a)))
  b = a_num//a_denom
  return preimage(phi, pth_root(b))
end

################################################################################
#
#  Rational Function Field Valuation
#
################################################################################

# might be not the best place but still
# currently only used in elliptic curve code
function valuation(x::T, p::T) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem}
  @req parent(x) === parent(p) "x and p must come from the same field"
  is_zero(x) && return inf

  if is_one(denominator(p))
    f = numerator(p)
    @req is_irreducible(f) "p must represent a place"
    return valuation(numerator(x), f) - valuation(denominator(x), f)
  else
    @req p == 1 // gen(parent(p)) "p must be a finite-place generator (poly) or 1//t"
    return degree(denominator(x)) - degree(numerator(x))
  end
end
function valuation(x::AbstractAlgebra.Generic.RationalFunctionFieldElem{T, U}, p::U) where {T, U <: PolyRingElem{T}}
  @req parent(p) === parent(numerator(x)) "p must come from the polynomial ring of x"
  return valuation(x, parent(x)(p))
end
