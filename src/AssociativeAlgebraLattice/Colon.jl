################################################################################
#
#  Colons
#
################################################################################

# TODO: Refactor via embedded-module duality and bilinear images:
# (L:M)_left = dual(im(Theta)), with Theta(m, phi)(x) = phi(x*m)
# for m in M and phi in dual(L); use phi(m*x) for the right colon.
# Track dual ambient spaces so double duality recovers A. Do HNF
# selection in embedded modules, using known elementary-divisor multiples
# when available, and retain numerator/denominator data and bulk matrix
# copies in optimized backends.
function _colon_module(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice;
                       side::Symbol = :left)
  _check_compatible(L, M)
  R = base_ring(L)
  @req _ring_type(R) === _PID "Colons are only supported over PIDs"
  @req is_full_lattice(L) && is_full_lattice(M) "The lattices must have full rank"
  @req side === :left || side === :right "The side must be :left or :right"
  A = algebra(L)
  @req has_one(A) "The ambient algebra must have an identity"
  K = base_ring(A)
  d = dim(A)
  B = basis_matrix_inverse(underlying_module(L))
  C = zero_matrix(K, d^2, d)
  action = side === :left ? :right : :left
  for (i, m) in enumerate(basis(M; copy = false))
    N = representation_matrix(m, action)*B
    # Stack the coordinate linear forms for x*m or m*x as rows.
    for s in 1:d, t in 1:d
      C[t + (i - 1)*d, s] = N[s, t]
    end
  end
  H = basis_matrix(embedded_module(R, K, C))
  # The colon is the coordinate dual of the module of linear forms.
  Ht = transpose(H)
  return embedded_module(R, K, inv(Ht); overstructure = A,
                         is_basis_matrix = true, inverse = Ht)
end

@doc raw"""
    colon(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice; side = :left)

For compatible full PID lattices in a unital algebra `A`, return the lattice
`{x in A | x*M ⊆ L}` if `side` is `:left`, or `{x in A | M*x ⊆ L}` if
`side` is `:right`.
"""
function colon(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice;
               side::Symbol = :left)
  N = _colon_module(L, M; side)
  return lattice(algebra(L), base_ring(L), N)
end
