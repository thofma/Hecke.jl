################################################################################
#
#  Quotients of orders as orders
#
################################################################################

@doc raw"""
    quotient_order(O::Order, I::Ideal) -> Order

Given a two-sided ideal $I$ contained in $\mathcal{O}$ such that
$\mathcal{O}/I$ is torsion-free, returns the tuple $(R, h)$ with
$R = \mathcal{O}/I$ and $h$ the projection on the ambient algebras.
"""
function quotient_order(O::AlgAssAbsOrd, I::AlgAssAbsOrdIdl)
  M = basis_matrix_wrt(I, O)
  @assert isone(denominator(M))
  S, U, V = snf_with_transform(numerator(M))
  adj_bas_mat = inv(V)
  adj_bas_all = [elem_from_mat_row(O, adj_bas_mat, i) for i in 1:degree(O)]
  k = something(findfirst(iszero, diagonal(S)), nrows(S) + 1)
  adjusted_basis = adj_bas_all[k:end]
  l = length(adjusted_basis)
  mt = Array{QQFieldElem, 3}(undef, l, l, l)
  for i in 1:l
    for j in 1:l
      bij = adjusted_basis[i] * adjusted_basis[j]
      mt[i, j, :] = (coordinates(bij) * V)[k:end]
    end
  end
  quoAlg = StructureConstantAlgebra(QQ, mt; check = false)
  ord = Order(quoAlg, basis(quoAlg))
  #
  bminvO = QQMatrix(basis_mat_inv(FakeFmpqMat, O))
  VQ = change_base_ring(QQ, V)
  A = algebra(O)
  img = matrix(QQ, [((coefficients(b) * bminvO * VQ)[k:end]) for b in basis(A)])
  preimg = matrix(QQ, [coefficients(elem_in_algebra(adjusted_basis[i])) for i in 1:l])
  h = hom(A, quoAlg, img, preimg)

  # Lets determine the decomposition of quoAlg if the decomposition of algebra(O) is known

  #if isdefined(A, :decomposition)
  #  dec = Vector{Tuple{StructureConstantAlgebra{QQFieldElem},
  #               morphism_type(StructureConstantAlgebra{QQFieldElem}, typeof(quoAlg))}}()

  #  d = 0
  #  for (B, mB) in decompose(A)
  #    if !iszero(h(mB(one(B))))
  #      push!(dec, (B, compose_and_squash(h, mB)))
  #      d += dim(B)
  #    end
  #  end
  #  @assert d == dim(quoAlg)

  #  quoAlg.decomposition = dec

  #  if get_attribute(A, :refined_wedderburn, false)
  #    set_attribute!(quoAlg, :refined_wedderburn => true)
  #  end
  #end

  _transport_refined_wedderburn_decomposition_forward(h)
  return ord, h
end
