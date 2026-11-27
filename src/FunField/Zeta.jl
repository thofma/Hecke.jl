# Zeta-function of a function field

################################################################################
#
#  L-polynomial
#
################################################################################

function L_polynomial(Zt::ZZPolyRing, F::Generic.AbsSimpleFunctionField{<:FinFieldElem})
  @req _is_separable(F) "Currently assumes separable extension"
  # F is defined over F_q, having exact constant field F_Q with Q = q^m
  m = constant_field_degree(F)
  Q = order(defining_constant_field(F))^m
  g = genus(F)
  c = zeros(ZZRingElem, 2*g+1)

  # every place has degree (over F_q) divisible by m
  # the place of degree k over F_q has degree k/m over F_Q
  counts = _fill_place_degree_counts(F, g*m)
  @assert all(iszero(counts[k]) for k in 1:g*m if k % m != 0)
  # B_k is the number of places of degree k (1 <= k <= g)
  B = [counts[k*m] for k in 1:g]
  # N_k is the number of rational points over F_{Q^k} (1 <= k <= g)
  # N_k = sum_{d | k} d*B_d
  N = [sum(d * B[d] for d in divisors(k)) for k = 1:g]
  # S_k is the (negative) power sum of frobenius eigenvalues: S_k = N_k - Q^k - 1
  # log L(t) = sum S_n * t^n/n
  S = [N[k] - Q^k - ZZ(1)  for k = 1:g]
  # L'(t) = L(t) sum S_n * t^{n-1}
  # giving c_n = 1/n * sum S_k * c_{n-k} [we compute for 1 <= n <= g]
  c[1] = ZZ(1)
  for n in 1:g
    c[n+1] = divexact(sum(S[k] * c[n - k + 1] for k in 1:n), n)
  end
  # from functional equation: c_{g+n} = Q^n * c_{g-n} for 1 <= n <= g
  for n in 1:g
    c[g + n + 1] = Q^n * c[g - n + 1]
  end

  return Zt(c)
end

function L_polynomial(F::Generic.AbsSimpleFunctionField{<:FinFieldElem})
  return L_polynomial(polynomial_ring(ZZ, :t; cached = false)[1], F)
end

################################################################################
#
#  Counting the places of given degree
#
################################################################################

# Lazy enumeration of irreducible monic polynomials of a given degree
function _enumerate_monic_irreducibles(kx::PolyRing{<:FinFieldElem}, d::Int)
  @req d >= 0 "degree must be non-negative"
  k = base_ring(kx)
  # ntuple(_ -> k, d)    : produces d-tuple (k, ..., k) of a field
  # ntuple(_ -> k, d)... : splats ("unpacks") into positional arguments
  # so we have Iterators.product(k, ..., k)
  # Note that iteration over a finite field iterates over its elements
  monics = (  kx(elem_type(k)[c..., one(k)])
              for c in Iterators.product(ntuple(_ -> k, d)...))
  return Iterators.filter(is_irreducible, monics)
end

# f first ensured monic, and then scaled with the lcm d of the coefficient denominators
#   F(Y) = d^n * f(Y/d),
function _integral_monic_model(F::Generic.AbsSimpleFunctionField{<:FinFieldElem})
  f_orig = defining_polynomial(F)
  f = f_orig*inv(leading_coefficient(f_orig))
  d = reduce(lcm, (denominator(c) for c in coefficients(f)))

  kxY, Y = polynomial_ring(parent(d), :Y; cached = false)
  n = degree(f)
  return sum(numerator(coeff(f, i)*d^(n - i))*Y^i for i in 0:n)
end

# returns array counts[1:N] with counts[i] = the number of places of degree exactly i <= N
function _fill_place_degree_counts(F::Generic.AbsSimpleFunctionField{<:FinFieldElem}, N::Int)
  @req N >= 0 "degree bound must be non-negative"

  # NOTE: GenOrd's prime_decomposition follows number field in treating
  #   degree_limit == 0 as meaning "do not bound degree from the above"
  # Alas this means that for N = 0, we would need to add a special handling below
  # Thankfully, this is easily treated here as a special case
  N == 0 && return Int[]

  counts = zeros(Int, N)
  kx = parent(numerator(gen(base_field(F))))

  ft = _integral_monic_model(F)
  # for p not dividing disc(ft): ft is p-maximal and unramified at p
  bad_primes = Set(first(t) for t in factor(discriminant(ft)) if degree(first(t)) <= N)

  Ofin = finite_maximal_order(F)
  for e in 1:N, p in _enumerate_monic_irreducibles(kx, e)
    # needs full prime_decomposition
    if p in bad_primes
      for (P, _) in prime_decomposition(Ofin, p, div(N, e))
        counts[e*degree(P)] += 1
      end
      continue
    end

    # Kummer-Dedekind case: one place of degree e*k per irreducible factor of degree k
    # in here we can "cheat" and read counts from the distinct-degree factorization
    K, mK = Hecke.residue_field(kx, p)
    KY, _ = polynomial_ring(K, :Y; cached = false)
    for (k, g) in factor_distinct_deg(map_coefficients(mK, ft; parent = KY))
      e*k <= N && (counts[e*k] += div(degree(g), k))
    end
  end

  Oinf = infinite_maximal_order(F)
  for (P, _) in prime_decomposition(Oinf, gen(base_ring(Oinf)), N)
    counts[degree(P)] += 1
  end

  return counts
end
