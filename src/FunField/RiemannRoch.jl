#maximal divisor reduction with (x)_\infty
function maximal_reduction(D::Divisor)
  @req !iszero(D) "Divisor is zero."
  F = function_field(D)
  J_fin, J_inf = inverse_ideals(D)
  D_red, r, a = _maximal_reduction(J_fin, J_inf, F)
  return D_red, r, divisor(a)
end

#maximal divisor reduction with (x)_\infty
function _maximal_reduction(J_fin, J_inf, F)
  n = degree(F)
  
  A = pole_divisor(Hecke.separating_element(F))

  #start of riemann roch space computation to get d_i
  B_fin = _coordinate_matrix(J_fin)
  B_inf = _coordinate_matrix(J_inf)
  dM, d_deg = _riemann_roch_common_setup(B_fin, B_inf)

  # weak Popov reduction of dM (no denominators)
  T, U = _weak_popov_with_transform!(dM)

  #Let v_i be the basis generators in the RR computation.
  #Choose 'r' maximal s.th. v_i *x^r in RR(D) for some i.
  d_min, idx = findmin(maximum(degree, T[i, 1:n]) for i in 1:n)
  r = d_deg - d_min

  #'a' is first basis generator v_i s.th. v_i * x^r in RR(D),
  #so 'a' in RR(D-r*(x)_\infty) (not necessarily as a generator).
  a = (U[idx:idx, :]*basis(J_fin))[1]

  ainv = inv(a)
  D_red_fin = ainv * J_fin
  D_red_inf = _shift_infinite_ideal(ainv * J_inf, -r)

  D_red = _divisor_from_inverse_ideals(D_red_fin, D_red_inf)

  return D_red, r, a
end