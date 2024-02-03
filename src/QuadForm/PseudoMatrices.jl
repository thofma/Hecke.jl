# TODO: The scaling of pseudo-matrices with an element scales the ideals and not the matrix ...

function _translate_pseudo_hnf(H::PMat, f)
  OL = maximal_order(codomain(f))
  return _translate_pseudo_hnf(H, f, OL)
end

function _translate_pseudo_hnf(H::PMat, f, target_order)
  OE = target_order
  E = nf(OE)
  coeff_ideals = fractional_ideal_type(OE)[]
  for i in 1:length(H.coeffs)
    push!(coeff_ideals, fractional_ideal(OE, elem_type(E)[f(x) for x in gens(H.coeffs[i])]))
  end
  m = zero_matrix(E, nrows(H), ncols(H))
  MH = matrix(H)
  for i in 1:nrows(H)
    for j in 1:ncols(H)
      m[i, j] = f(MH[i, j])
    end
  end
  pm = pseudo_matrix(m, coeff_ideals)
  return pm
end

function pseudo_hnf_via_absolute(H::PMat; full_rank::Bool = true, shape::Symbol = :lowerleft, nonzero::Bool = false)
  O = base_ring(H)
  E = nf(O)
  EabsToE = absolute_simple_field(E)[2]
  return pseudo_hnf_via_absolute(H, EabsToE, full_rank = full_rank,
                                             shape = shape,
                                             nonzero = nonzero)
end

function pseudo_hnf_via_absolute(H::PMat, EabsToE; full_rank::Bool = true, shape::Symbol = :lowerleft, nonzero::Bool = false)
  O = base_ring(H)
  E = nf(O)
  pm = _translate_pseudo_hnf(H, pseudo_inv(EabsToE))
  if full_rank
    HH = pseudo_hnf_full_rank(pm, shape)
  else
    HH = pseudo_hnf(pm, shape)
  end

  if nonzero
    r = 0
    if shape === :lowerleft
      for i in 1:nrows(HH)
        if !is_zero_row(matrix(HH), i)
          r = i
          break
        end
      end
      HH = sub(HH, r:nrows(pm), 1:ncols(pm))
    elseif shape === :upperright
      for i in nrows(HH):-1:1
        if !is_zero_row(matrix(HH), i)
          r = i
          break
        end
      end
      H = sub(HH, 1:r, 1:ncols(HH))
    end
  end

  return _translate_pseudo_hnf(HH, EabsToE, O)
end

################################################################################
#
#  Sum
#
################################################################################

function _sum_modules_with_map(a::PMat{<: RelSimpleNumFieldElem, <: RelNumFieldOrderFractionalIdeal}, b::PMat, f, full_rank = true)
  H = vcat(a, b)
  return pseudo_hnf_via_absolute(H, f, shape = :lowerleft, nonzero = true)
end

_sum_modules(L::QuadLat, a::PMat, b::PMat, full_rank = true) = _sum_modules(a, b, full_rank)

function _sum_modules(L::HermLat, a::PMat, b::PMat, full_rank = true)
  f = absolute_simple_field(ambient_space(L))[2]
  return _sum_modules_with_map(a, b, f, full_rank)
end

function _sum_modules(a::PMat{<: RelSimpleNumFieldElem, <: RelNumFieldOrderFractionalIdeal}, b::PMat, full_rank = true)
  H = vcat(a, b)
  return pseudo_hnf_via_absolute(H, shape = :lowerleft, nonzero = true)
end

function _sum_modules(a::PMat, b::PMat, full_rank = true)
  H = vcat(a, b)
  H = pseudo_hnf(H, :lowerleft)
  r = 0
  for i in 1:nrows(H)
    if !is_zero_row(matrix(H), i)
      r = i
      break
    end
  end
  @assert r != 0
  return sub(H, r:nrows(H), 1:ncols(H))
end

################################################################################
#
#  Intersect
#
################################################################################

function _intersect_modules(L::QuadLat, a::PMat, b::PMat, full_rank = true)
  return _intersect_modules(a, b, full_rank)
end

function _intersect_modules(L::HermLat, a::PMat{<: RelSimpleNumFieldElem, <: RelNumFieldOrderFractionalIdeal}, b::PMat, full_rank = true)
  f = absolute_simple_field(ambient_space(L))[2]
  return _intersect_modules_with_map(a, b, f, full_rank)
end

function _intersect_modules(a::PMat{<: RelSimpleNumFieldElem, <: RelNumFieldOrderFractionalIdeal}, b::PMat, full_rank = true)
  f = absolute_simple_field(nf(base_ring(a)))[2]
  return _intersect_modules_with_map(a, b, f, full_rank)
end

function _intersect_modules_with_map(a::PMat{<: RelSimpleNumFieldElem, <: RelNumFieldOrderFractionalIdeal}, b::PMat, f, full_rank = true)
  OE = maximal_order(domain(f))
  aE = _translate_pseudo_hnf(a, pseudo_inv(f), OE)
  bE = _translate_pseudo_hnf(b, pseudo_inv(f), OE)
  c = _intersect_modules(aE, bE, full_rank)
  return _translate_pseudo_hnf(c, f, base_ring(a))
end

function _intersect_modules(a::PMat, b::PMat, full_rank = true)
  M1 = hcat(a, deepcopy(a))
  d = ncols(b)
  z = zero_matrix(base_ring(matrix(a)), d, d)
  M2 = hcat(pseudo_matrix(z, b.coeffs), b)
  M = vcat(M1, M2)
  if full_rank
    H = sub(pseudo_hnf(M, :lowerleft), 1:d, 1:d)
    return H
  else
    H = pseudo_hnf_kb(M, :lowerleft)
    i = 1
    while is_zero_row(H.matrix, i)
      i += 1
    end
    return sub(H, i:d, 1:d)
  end
end

function _modules_equality(a::PMat, b::PMat)
  _spans_subset_of_pseudohnf(a, b, :lowerleft) && _spans_subset_of_pseudohnf(b, a, :lowerleft)
end

function _module_scale_ideal(a::AbsNumFieldOrderIdeal, b::PMat)
  return pseudo_matrix(matrix(b), [ a * c for c in coefficient_ideals(b)])
end

_module_scale_ideal(a::PMat, b::AbsNumFieldOrderIdeal) = _module_scale_ideal(b, a)

function _module_scale_ideal(a::AbsSimpleNumFieldOrderFractionalIdeal, b::PMat)
  return pseudo_matrix(matrix(b), Ref(a) .* coefficient_ideals(b))
end

_module_scale_ideal(a::PMat, b::AbsSimpleNumFieldOrderFractionalIdeal) = _module_scale_ideal(b, a)

function _module_scale_ideal(a::RelNumFieldOrderIdeal, b::PMat)
  return pseudo_matrix(matrix(b), Ref(a) .* coefficient_ideals(b))
end

_module_scale_ideal(a::PMat, b::RelNumFieldOrderIdeal) = _module_scale_ideal(b, a)

function _module_scale_ideal(a::RelNumFieldOrderFractionalIdeal, b::PMat)
  return pseudo_matrix(matrix(b), Ref(a) .* coefficient_ideals(b))
end

_module_scale_ideal(a::PMat, b::RelNumFieldOrderFractionalIdeal) = _module_scale_ideal(b, a)

*(a::AbsNumFieldOrderIdeal, b::PMat) = _module_scale_ideal(a, b)

*(a::AbsSimpleNumFieldOrderFractionalIdeal, b::PMat) = _module_scale_ideal(a, b)

*(a::RelNumFieldOrderIdeal, b::PMat) = _module_scale_ideal(a, b)

*(a::RelNumFieldOrderFractionalIdeal, b::PMat) = _module_scale_ideal(a, b)

################################################################################
#
#  Local basis matrices
#
################################################################################

# Given a pseudo matrix over K with row span M and p a prime ideal of K, find a
# basis matrix of M \otimes OK_p.
function _local_basis_matrix(a::PMat, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  @assert base_ring(a) == order(p)
  uni = uniformizer(p)
  z = zero_matrix(base_ring(matrix(a)), nrows(a), ncols(a))
  for i in 1:nrows(a)
    c = coefficient_ideals(a)[i]
    x = uni^valuation(c, p)
    for j in 1:ncols(a)
      z[i, j] = x * matrix(a)[i, j]
    end
  end
  return z
end

# Given a pseudo matrix over E/K with row span M and a p a prime ideal of K,
# find a basis matrix of M \otimes OE_p.
function _local_basis_matrix_prime_below(a::PMat, p::T) where T
  @assert base_ring(base_ring(a)) == order(p)
  R = base_ring(a)
  D = prime_decomposition(R, p)
  unis = elem_type(R)[p_uniformizer(q[1]) for q in D]
  @assert all(valuation(unis[i], D[i][1]) == 1 for i in 1:length(D))
  @assert all(sum(valuation(unis[i], D[j][1]) for j in 1:length(D)) == 1 for i in 1:length(D))
  z = zero_matrix(base_ring(matrix(a)), nrows(a), ncols(a))
  _c = coefficient_ideals(a)
  for i in 1:nrows(a)
    c = _c[i]
    x = elem_in_nf(unis[1])^(valuation(c, D[1][1]))
    for k in 2:length(D)
      x = x * elem_in_nf(unis[k])^valuation(c, D[k][1])
    end
    for j in 1:ncols(a)
      z[i, j] = x * matrix(a)[i, j]
    end
  end
  return z
end

# Given a pseudo matrix over E/K with row span M and a p a prime ideal of K,
# find a basis matrix N of M \otimes OE_p. The row span of N is a submodule of
# M.
function _local_basis_matrix_prime_below_submodule(a::PMat, p)
  @assert base_ring(base_ring(a)) == order(p)
  R = base_ring(a)
  D = prime_decomposition(R, p)
  z = zero_matrix(base_ring(matrix(a)), nrows(a), ncols(a))
  _c = coefficient_ideals(a)
  for i in 1:nrows(a)
    c = _c[i]
    f = factor(c)
    if length(f) == 0
      x = one(nf(R))
    else
      for Q in D
        if !(haskey(f, Q[1]))
          f[Q[1]] = 0
        end
      end
      x = approximate(Int[e for (_, e) in f], ideal_type(base_ring(a))[p for (p, _) in f])
      #@assert all(valuation(x, p) == e for (p, e) in f)
    end
    #@assert valuation(x, D[1][1]) == valuation(c, D[1][1])
    #x = unis[1]^valuation(c, D[1][1])
    #for k in 2:length(D)
    #  x = x * unis[k]^valuation(c, D[k][1])
    #end
    for j in 1:ncols(a)
      z[i, j] = x * matrix(a)[i, j]
    end
  end
  if false
    _z = pseudo_matrix(z, [one(nf(R)) * R for i in 1:nrows(z)])
    @assert _spans_subset_of_pseudohnf(_z, a, :lowerleft)
    @assert valuation(det(_z), D[1][1]) == valuation(det(a), D[1][1])
  end
  return z
end

# Given a pseudo matrix over K with row span M and a p a prime ideal of K,
# find a basis matrix N of M \otimes OK_p. The row span of N is a submodule of
# M.
function _local_basis_submodule_matrix(a::PMat, p)
  #@assert base_ring(base_ring(a)) == order(p)
  z = zero_matrix(base_ring(matrix(a)), nrows(a), ncols(a))
  for i in 1:nrows(a)
    c = coefficient_ideals(a)[i]
    vpc = valuation(c, p)
    found = false
    local x
    for b in absolute_basis(c) # could use generators here
      if valuation(b, p) == vpc
        found = true
        x = b
        break
      end
    end
    @assert found
    for j in 1:ncols(a)
      z[i, j] = x * matrix(a)[i, j]
    end
  end
  return z
end

function _local_basis_supermodule_matrix(a::PMat, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  throw(NotImplemented())
end

