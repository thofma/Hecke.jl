@doc raw"""
    defining_constant_field(K::AbsSimpleFunctionField) -> Field

Let K be a field extension of k(x).
Return the field k over which the base field k(x) is defined.
"""
function defining_constant_field(K::AbstractAlgebra.Generic.AbsSimpleFunctionField)
  return base_ring(base_ring(K))
end

function is_constant(c::Generic.RationalFunctionFieldElem)
  return degree(numerator(c)) <= 0 && degree(denominator(c)) == 0
end

# convert an element of k(x) that is known to be constant to an element of k
function _constant_to_base(c::Generic.RationalFunctionFieldElem, k::Field)
  n = numerator(c)
  d = denominator(c)
  @assert degree(n) <= 0 && degree(d) == 0 "Element is not constant"
  return k(coeff(n, 0)) // k(coeff(d, 0))
end

# Random element of the k-span of B, with small coefficients if k is infinite
function _random_k_combination(B::Vector, k::Field)
  if is_finite(k)
    return sum(rand(k) * b for b in B)
  else
    return sum(k(rand(-10:10)) * b for b in B)
  end
end

@doc raw"""
    constant_field_degree(K::AbsSimpleFunctionField) -> Int

Let K be a field extension of k(x). And let k' be the constant field of K. 
Return the degree of k' over the defining constant field k.
"""
@attr Int function constant_field_degree(F::Generic.AbsSimpleFunctionField)
  @req _is_separable(F) "Currently assumes separable extension"

  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)
  J_fin = fractional_ideal(ideal(Ofin, one(Ofin)))
  J_inf = fractional_ideal(ideal(Oinf, one(Oinf)))
  return _riemann_roch_dim(J_fin, J_inf, F)
end


@doc raw"""
    constant_field(K::AbsSimpleFunctionField) -> Field, Map

Return the constant field k' of K and the embedding of k' into K.
This can differ from the defining constant field k used for the
base field k(x).
"""
function constant_field(F::Generic.AbsSimpleFunctionField)
  return get_attribute!(F, :constant_field) do
    _constant_field(F)
  end::Tuple{Field, Map}
end

function _constant_field(F::Generic.AbsSimpleFunctionField)
  @req _is_separable(F) "Currently assumes separable extension"

  k = defining_constant_field(F)
  kx = base_field(F)
  m = constant_field_degree(F)

  #Check if the exact constant field is already the constant field.
  if m == 1
    image_map = function(x::FieldElem)
      return F(kx(x))
    end

    pre_image_map = function(y::Generic.AbsSimpleFunctionFieldElem)
      c = coeff(y, 0)
      @req is_constant(c) && y == F(c) "Element is not a constant"
      return _constant_to_base(c, k)
    end
    return k, MapFromFunc(k, F, image_map, pre_image_map)
  end

  # k-basis of L(0) = k'
  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)
  B = _riemann_roch_space(fractional_ideal(ideal(Ofin, one(Ofin))),
                          fractional_ideal(ideal(Oinf, one(Oinf))), F)

  # Find a primitive element of k'/k by trying random elements
  kt, t = polynomial_ring(k, :t)
  c = zero(F)
  f = zero(kt)
  found = false

  candidates = Iterators.flatten((B, (_random_k_combination(B, k) for _ in 1:200)))
  for b in candidates
    mp = minpoly(b)
    if degree(mp) == m
      c = b
      f = kt([_constant_to_base(coeff(mp, i), k) for i in 0:m])
      found = true
      break
    end
  end
  @assert found "Could not find a primitive element of the exact constant field"

  K, mK = residue_field(kt, f)
  a = mK(t)

  # Matrix whose rows are the coordinates of 1, c, ..., c^(m-1)
  n = degree(F)
  powers = elem_type(F)[one(F)]
  for _ in 2:m
    push!(powers, powers[end] * c)
  end
  M = zero_matrix(kx, m, n)
  for i in 1:m, j in 1:n
    M[i, j] = coeff(powers[i], j - 1)
  end

  image_map = function(x::FieldElem)
    g = preimage(mK, x)
    return sum(F(kx(coeff(g, i))) * powers[i + 1] for i in 0:min(degree(g), m - 1); init = zero(F))
  end

  pre_image_map = function(y::Generic.AbsSimpleFunctionFieldElem)
    v = matrix(kx, 1, n, [coeff(y, j - 1) for j in 1:n])
    fl, s = can_solve_with_solution(M, v; side = :left)
    @req fl && all(is_constant(s[1, i]) for i in 1:m) "Element is not a constant"
    return sum(K(_constant_to_base(s[1, i], k)) * a^(i - 1) for i in 1:m)
  end

  return K, MapFromFunc(K, F, image_map, pre_image_map)
end
