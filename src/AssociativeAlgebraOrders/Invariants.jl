for f in (:tr, :trred, :norm, :normred)
  @eval function $f(x::AssociativeAlgebraOrderElem)
    return base_ring(parent(x))($f(elem_in_algebra(x; copy = false)))
  end
end

for f in (:charpoly, :minpoly, :reduced_charpoly)
  @eval function $f(x::AssociativeAlgebraOrderElem)
    return change_base_ring(base_ring(parent(x)), $f(elem_in_algebra(x; copy = false)))
  end
  @eval function $f(R::PolyRing, x::AssociativeAlgebraOrderElem)
    return change_base_ring(base_ring(R), $f(elem_in_algebra(x; copy = false)); parent = R)
  end
end

function representation_matrix(x::AssociativeAlgebraOrderElem{<:AssociativeAlgebraOrder{R, _PID}},
                               side::Symbol = :left) where {R}
  @req side === :left || side === :right "The side must be :left or :right"
  O = parent(x)
  B = basis_matrix(O; copy = false)
  M = B*representation_matrix(elem_in_algebra(x; copy = false), side)*
      basis_matrix_inverse(O; copy = false)
  return change_base_ring(base_ring(O), M)
end

for (f, g) in ((:_trace_matrix, :tr), (:_trred_matrix, :trred))
  @eval @attr dense_matrix_type(R) function $f(O::AssociativeAlgebraOrder{R, _PID}) where {R}
    return _trace_matrix(O, $g, base_ring(O))
  end
end

function _trace_matrix(O::AssociativeAlgebraOrder, f, R)
  b = basis_alg(O; copy = false)
  N = zero_matrix(R, degree(O), degree(O))
  for i in eachindex(b), j in i:length(b)
    N[i, j] = R(f(b[i]*b[j]))
    N[j, i] = N[i, j]
  end
  return N
end

function trace_matrix(O::AssociativeAlgebraOrder; copy::Bool = true)
  M = _trace_matrix(O)
  return copy ? deepcopy(M) : M
end

function trred_matrix(O::AssociativeAlgebraOrder; copy::Bool = true)
  M = _trred_matrix(O)
  return copy ? deepcopy(M) : M
end

@doc raw"""
    discriminant(O::AssociativeAlgebraOrder)

Return the reduced-trace discriminant as an element of the coefficient ring.
Reduced traces must be defined for the ambient algebra.
"""
@attr elem_type(R) function discriminant(O::AssociativeAlgebraOrder{R, _PID}) where {R}
  return det(trred_matrix(O; copy = false))
end
