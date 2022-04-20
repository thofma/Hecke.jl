################################################################################
#
#  Quotients of orders as orders
#
################################################################################

@doc Markdown.doc"""
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
  k = findfirst(iszero, diagonal(S))
  adjusted_basis = adj_bas_all[k:end]
  l = length(adjusted_basis)
  mt = Array{fmpq, 3}(undef, l, l, l)
  for i in 1:l
    for j in 1:l
      bij = adjusted_basis[i] * adjusted_basis[j]
      mt[i, j, :] = (coordinates(bij) * V)[k:end]
    end
  end
  quoAlg = AlgAss(QQ, mt)
  ord = Order(quoAlg, basis(quoAlg))
  #
  bminvO = fmpq_mat(basis_mat_inv(O))
  VQ = change_base_ring(QQ, V)
  A = algebra(O)
  img = matrix(QQ, [((coefficients(b) * bminvO * VQ)[k:end]) for b in basis(A)])
  preimg = matrix(QQ, [coefficients(elem_in_algebra(adjusted_basis[i])) for i in 1:l])
  h = hom(A, quoAlg, img, preimg)

  # Lets determine the decomposition of quoAlg if the decomposition of algebra(O) is known

  if isdefined(A, :decomposition)
    dec = Vector{Tuple{AlgAss{fmpq},
                 morphism_type(AlgAss{fmpq}, typeof(quoAlg))}}()

    d = 0
    for (B, mB) in decompose(A)
      if !iszero(h(mB(one(B))))
        push!(dec, (B, compose_and_squash(h, mB)))
        d += dim(B)
      end
    end
    @assert d == dim(quoAlg)

    quoAlg.decomposition = dec

    if get_attribute(A, :refined_wedderburn, false)
      set_attribute!(quoAlg, :refined_wedderburn => true)
    end
  end

  return ord, h
end
