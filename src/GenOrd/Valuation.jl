################################################################################
#
#  GenOrd/Valuation.jl : Valuations at prime ideals
#
################################################################################
#
# Adapted from NumFieldOrd/NfOrd/Valuation.jl
#
# The valuation function is the analogue of `val_func_index` for number
# fields
#
################################################################################
#
#  Valuation function
#
################################################################################

# Can we use the valuation function for P? As for number fields, we require
#   a maximal order. We also need the anti-uniformizer, which we read off
#   from a principal generator or a two-element normal presentation of P.
function _has_valuation_function(P::GenOrdIdl)
  is_prime_known(P) && P.is_prime == 1 || return false
  P.splitting_type[1] > 0 || return false
  is_maximal_known_and_maximal(order(P)) || return false
  return has_princ_gen(P) || has_2_elem_normal(P)
end

function val_func_index(P::GenOrdIdl{S, T}) where {S, T}
  O = order(P)
  R = base_ring(O)
  n = degree(O)
  p = minimum(P; copy = false)
  e = ramification_index(P)
  gamma, d = integral_split(anti_uniformizer(P), O)
  M = representation_matrix(gamma)

  local val
  let O = O, R = R, n = n, p = p, e = e, d = d, M = M
    function val(x::FieldElem)
      num, den = integral_split(x, O)
      v = matrix(R, 1, n, coordinates(num))
      k = 0
      while true
        w = v * M
        for j in 1:n
          fl, q = divides(w[1, j], d)
          fl || return k - e * valuation(den, p)
          w[1, j] = q
        end
        v = w
        k += 1
      end
    end
  end
  return val
end

# Function that chooses the valuation depending on the properties of the
# ideal.
function assure_valuation_function(P::GenOrdIdl)
  isdefined(P, :valuation) && return nothing
  @hassert :GenOrd 1 _has_valuation_function(P)
  P.valuation = val_func_index(P)
  return nothing
end

################################################################################
#
#  Valuation of elements
#
################################################################################

@doc raw"""
    valuation(a::FieldElem, P::GenOrdIdl) -> Int
    valuation(a::GenOrdElem, P::GenOrdIdl) -> Int
    valuation(a::RingElem, P::GenOrdIdl) -> Int

Return the $P$-adic valuation of the nonzero element $a$ of the field, the
order or the base ring of the order of the prime ideal $P$.
"""
function valuation(a::FieldElem, P::GenOrdIdl)::Int
  @req !is_zero(a) "Element must be nonzero"
  O = order(P)
  @req parent(a) === O.F "Incompatible parents"
  if !_has_valuation_function(P)
    return valuation_naive(a, P)
  end
  assure_valuation_function(P)
  return P.valuation(a)::Int
end

function valuation(a::GenOrdElem, P::GenOrdIdl)::Int
  @req parent(a) === order(P) "Incompatible parents"
  return valuation(data(a), P)
end

# a in the base ring: v_P(a) = e(P) * v_p(a), where p is the minimum of P
function valuation(a::RingElem, P::GenOrdIdl)::Int
  @req !is_zero(a) "Element must be nonzero"
  O = order(P)
  @req parent(a) === base_ring(O) "Incompatible parents"
  if !is_prime_known(P) || P.is_prime != 1 || P.splitting_type[1] == 0
    return valuation_naive(O(a), P)
  end
  return P.splitting_type[1] * valuation(a, minimum(P; copy = false))::Int
end

function valuation_naive(a::GenOrdElem, P::GenOrdIdl)::Int
  return valuation_naive(ideal(order(P), a), P)
end

function valuation_naive(a::FieldElem, P::GenOrdIdl)::Int
  O = order(P)
  num, den = integral_split(a, O)
  return valuation_naive(num, P) - valuation_naive(O(den), P)
end

################################################################################
#
#  Valuation of ideals
#
################################################################################

# For p in two-element normal presentation <m, alpha> and beta the numerator
# of alpha^{-1}, v_p(A) is the largest e with beta^e * A / m^e integral.
function valuation_naive(A::GenOrdIdl{S, T},
                         p::GenOrdIdl{S, T})::Int where {S, T}
  @req !is_zero(A) "A is zero"

  O = order(A)
  e = 0
  if has_2_elem_normal(p)
    beta = Hecke.numerator(inv(O.F(_gen_two(p))), O)
    newA = fractional_ideal(beta*A, _gen_one(p))
    while is_integral(newA)
      e += 1
      newA = fractional_ideal(numerator(beta*newA; copy = false), _gen_one(p))
    end
  else
    newA = Hecke.colon(A,p)
    while is_integral(newA)
      e+=1
      newA = Hecke.colon(newA,fractional_ideal(p))
    end
  end
  return e
end

@doc raw"""
    valuation(A::GenOrdIdl, p::GenOrdIdl) -> Int

Return the $p$-adic valuation of the nonzero ideal $A$, that is, the largest
$i$ such that $A$ is contained in $p^i$.
"""
function Hecke.valuation(A::GenOrdIdl{S, T},
                         p::GenOrdIdl{S, T})::Int where {S, T}
  @req !is_zero(A) "A is zero"
  if has_minimum(A) && has_minimum(p) &&
      !divides(minimum(A; copy = false), minimum(p; copy = false))[1]
    return 0
  end
  if !_has_valuation_function(p)
    return valuation_naive(A, p)
  end
  if has_princ_gen(A)
    return valuation(_princ_gen(A), p)
  end
  if has_2_elem(A)
    # v_p(A) = min(v_p(gen_one), v_p(gen_two)); a generator can be zero
    a1 = _gen_one(A)
    a2 = _gen_two(A)
    is_zero(a1) && return valuation(a2, p)
    is_zero(a2) && return valuation(a1, p)
    return min(valuation(a1, p), valuation(a2, p))
  end
  return minimum(valuation(b, p) for b in basis(A; copy = false) if !is_zero(b))
end
