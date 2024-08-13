################################################################################
#
#  Solving over Dedekind domains
#
################################################################################

# TODO:
# At the moment I only need it for maximal orders
# To do it properly, we need to distinguish between maximal and non-maximal
# orders (or better is_maximal_known etc.). In the non-maximal order case
# we can turn it into linear algebra over Z.

struct PseudoHermiteFormTrait <: AbstractAlgebra.Solve.MatrixNormalFormTrait end

AbstractAlgebra.Solve.matrix_normal_form_type(::NumFieldOrder) = PseudoHermiteFormTrait()

function AbstractAlgebra.Solve._can_solve_internal_no_check(::PseudoHermiteFormTrait, A, b, task::Symbol; side::Symbol)
  if side === :right
    fl, _X, _K = AbstractAlgebra.Solve._can_solve_internal_no_check(PseudoHermiteFormTrait(), transpose(A), transpose(b), task; side = :left)
    return fl, transpose(_X), transpose(_K)
  end

  R = base_ring(A)
  @assert is_maximal(R)
  AP = pseudo_matrix(A)
  H, T = pseudo_hnf_with_transform(AP)
  # compute the rank
  r = something(findlast(i -> !is_zero_row(matrix(H), i), 1:nrows(H)), nrows(H))
  # We have to only take the full rank part of H, otherwise is _contained_in_span_...
  # confused.
  H = sub(H, 1:r, 1:ncols(H))
  if task === :only_check
    Kb = nf(R).(b)
    for i in 1:nrows(b)
      fl = _contained_in_span_of_pseudohnf(Kb[i:i, :], H, Val(false))
      if !fl
        return false, b, b
      end
    end
    return true, b, b
  end
  sol = zero_matrix(R, nrows(b), nrows(A))
  if task === :with_kernel
    K = kernel(A; side = :left)
  else
    K = b
  end

  Kb = nf(R).(b)

  pad = zero_matrix(nf(R), 1, nrows(A) - r)

  for i in 1:nrows(b)
    fl, _sol = _contained_in_span_of_pseudohnf(Kb[i:i, :], H, Val(true))
    if !fl
      return false, b, K
    end
    # We cut of some parts of H, so when we assemble the solution for A
    # we have to pad it again
    sol[i, :] = [_sol pad] * T
  end
  return true, R.(sol), K
end

function kernel(::PseudoHermiteFormTrait, A; side::Symbol = :left)
  if side === :right
    return transpose(kernel(transpose(A); side = :left))
  end
  H, T = pseudo_hnf_with_transform(pseudo_matrix(A))
  return _kernel_given_pmat_with_transform(H, T)
end

function _kernel_given_pmat_with_transform(H, T)
  R = base_ring(H)
  # compute the rank
  r = something(findlast(i -> !is_zero_row(matrix(H), i), 1:nrows(H)), nrows(H))
  rows = Vector{elem_type(R)}[]
  if r == nrows(T)
    return zero_matrix(R, 0, nrows(H))
  end
  for i in (r + 1):nrows(T)
    I = H.coeffs[i]
    gI = gens(I)
    for g in gI
      push!(rows, R.(g.* T[i, :]))
    end
  end
  return matrix(R, rows)
end
