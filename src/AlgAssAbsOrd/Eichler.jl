function principal_generator_eichler(I::AlgAssAbsOrdIdl)
  O = left_order(I)
  @assert is_maximal(O)
  A = algebra(O)
  @assert is_eichler(A)

  d = discriminant(O)

  y = integral_coprime_representative(O, I, d)
  J = I*y

  N = normred(J, O)
  @assert denominator(N) == 1 # J should be integral
  N = numerator(N)
  @assert is_principal(N) "Ideal is not principal"

  primes = collect(keys(factor(N).fac))
  valuations = [ valuation(N, p) for p in primes ]
  w = _norm_equation_valuations_only(O, primes, valuations)
  w = evaluate(w)

  Ow = O*O(w)
  ww = _eichler_find_transforming_unit(J, Ow)
  return w*ww*inv(y)
end

# Many functions are in AlgAssRelOrd/Eichler.jl

# Finds at least n units in the order F.maximal_orders[order_num]
function _find_some_units(F::FieldOracle{S, T, U, M}, order_num::Int, n::Int) where { S <: AbstractAssociativeAlgebra{QQFieldElem}, T, U, M }
  O = F.maximal_orders[order_num]
  units = Vector{elem_type(O)}()
  while length(units) < n
    KtoA = get_new_field(F, order_num)
    K = domain(KtoA)
    OK = maximal_order(K)
    UK, mUK = unit_group(OK)
    for j = 1:ngens(UK)
      u = mUK(UK[j])
      if u == -one(OK)
        continue
      end
      push!(units, O(KtoA(elem_in_nf(u, copy = false))))
    end
  end
  return units
end

# Finds x\in A^\times such that I == Jx.
# Requires nr(I) == nr(J) and that nr(I) is coprime to d where d is the
# discriminant of O.
function _eichler_find_transforming_unit(I::AlgAssAbsOrdIdl, J::AlgAssAbsOrdIdl)
  O = left_order(I)
  @assert is_maximal(O)
  # We assume that left_order(J) == O, but testing this would be really expensive

  n = normred(I, O)
  @assert n == normred(J, O)
  @assert denominator(n) == 1
  n = numerator(n)

  fac_n = factor(n)
  if isempty(fac_n)
    return one(algebra(order(O)))
  end

  primes = Vector{ZZRingElem}()
  for (p, e) in fac_n
    for i = 1:e
      push!(primes, p)
    end
  end
  t = _eichler_find_transforming_unit_recurse(I, J, primes)
  return t
end
