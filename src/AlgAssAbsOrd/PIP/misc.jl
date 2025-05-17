function _get_order_from_gens(A::AbstractAssociativeAlgebra{S}, B::Vector{ <: AbstractAssociativeAlgebraElem{S} }) where { S <: NumFieldElem }
  M = zero_matrix(base_ring(A), length(B), dim(A))
  for i = 1:length(B)
    elem_to_mat_row!(M, i, B[i])
  end
  pm = pseudo_hnf(pseudo_matrix(M), :lowerleft, true)
  return order(A, sub(pm, (nrows(pm) - ncols(pm) + 1):nrows(pm), 1:ncols(pm)))
end

_get_order_from_gens(A::AbstractAssociativeAlgebra{QQFieldElem}, B::Vector) = order(A, B)

function absolute_basis(M::AlgAssAbsOrd{<:StructureConstantAlgebra{QQFieldElem}})
  return basis(M)
end

function _isless(x::fpMatrix, y::fpMatrix)
  i = 0
  c = ncols(x)
  while i < c
    i += 1
    if x[i] == y[i]
      continue
    else
      return x[i] < y[i]
    end
  end
  return false
end

function maximal_order_via_absolute(O::AlgAssRelOrd)
  A = algebra(O)
  C, AtoC, CtoA = restrict_scalars(A, QQ)
  OC = maximal_order(Hecke._get_order_from_gens(C, AtoC.(elem_in_algebra.(absolute_basis(O)))))
  M = zero_matrix(base_ring(A), degree(OC), dim(A))
  for i = 1:degree(OC)
    elem_to_mat_row!(M, i, CtoA(elem_in_algebra(basis(OC, copy = false)[i], copy = false)))
  end
  PM = sub(pseudo_hnf(pseudo_matrix(M), :lowerleft, true), (degree(OC) - dim(A) + 1):degree(OC), 1:dim(A))
  O = order(A, PM)
  O.is_maximal = 1
  return O
end

function _get_a_twosided_conductor(O, M)
  A = algebra(O)
  Z, ZtoA = center(A)
  Fl = conductor(O, M, :left)

  FinZ = _as_ideal_of_smaller_algebra(ZtoA, Fl)
  # Compute FinZ*OA but as an ideal of O
  bM = basis(M, copy = false)
  bFinZ = basis(FinZ, copy = false)
  basis_F = Vector{elem_type(A)}()
  for x in bM
    for y in bFinZ
      yy = ZtoA(y)
      t = yy * elem_in_algebra(x, copy = false)
      push!(basis_F, t)
    end
  end

  for b in basis_F
    @assert b in O
  end

  F = ideal_from_lattice_gens(A, O, basis_F, :twosided)
  if is_maximal(M)
    F.left_order = M
    F.right_order = M
  end
  return F
end

function _describe(B)
  d = dimension_of_center(B)
  s = div(dim(B), d)
  n = isqrt(s)
  if isdefined(B, :isomorphic_full_matrix_algebra)
    ismatalg = true
  else
    ismatalg = false
  end
  if ismatalg
    return "Full matrix algebra of degree $n over field of degree $d"
  else
    return "Division algebra of degree $n over field of degree $d"
  end
end


