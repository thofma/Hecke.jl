function _direct_sum_matrix(M::EmbeddedModule{_PID}, N::EmbeddedModule{_PID})
  return Hecke.block_diagonal_matrix([basis_matrix(M), basis_matrix(N)])
end

function _direct_sum_matrix(M::EmbeddedModule{_DD}, N::EmbeddedModule{_DD})
  B, C = basis_matrix(M), basis_matrix(N)
  A = Hecke.block_diagonal_matrix([matrix(B), matrix(C)])
  I = vcat(Hecke.coefficient_ideals(B), Hecke.coefficient_ideals(C))
  return Hecke.pseudo_matrix(ring(M), A, I)
end

# Internal analogue of direct_sum: return the sum, injections, and projections.
function _direct_sum(M::EmbeddedModule, N::EmbeddedModule)
  @req ring(M) === ring(N) "The modules must have the same coefficient ring"
  @req overring(M) === overring(N) "The modules must have the same overring"
  D = embedded_module(ring(M), overring(M), _direct_sum_matrix(M, N);
                       overstructure = (M, N), is_basis_matrix = true)
  C = _coordinate_ring(M)
  r, s = rank(M), rank(N)
  A = Hecke.identity_matrix(C, r + s)
  iM = _hom(M, D, sub(A, 1:r, 1:r + s))
  iN = _hom(N, D, sub(A, r + 1:r + s, 1:r + s))
  pM = _hom(D, M, sub(A, 1:r + s, 1:r))
  pN = _hom(D, N, sub(A, 1:r + s, r + 1:r + s))
  return D, (iM, iN), (pM, pN)
end

@doc raw"""
    addition_map(M::EmbeddedModule, N::EmbeddedModule, P = M + N)

Return `(f, pM, pN)`, where `f` maps the internal direct sum of `M` and `N`
to `P` by addition, and `pM` and `pN` are its projections onto the summands.
Require compatible modules with `M` and `N` contained in `P`.

For `z = preimage(f, x)`, the elements `pM(z)` and `pN(z)` sum to `x` in
the common ambient space. Preimages are solved over the coefficient ring,
retaining coefficient ideals over supported maximal Dedekind orders.
"""
function addition_map(M::EmbeddedModule, N::EmbeddedModule,
                       P::EmbeddedModule = M + N)
  _check_compatible(M, N)
  @req issubset(M, P) && issubset(N, P) "The summands must lie in the codomain"
  return addition_map(inclusion_map(M, P), inclusion_map(N, P))
end

@doc raw"""
    addition_map(f::EmbeddedModuleMap, g::EmbeddedModuleMap)

For maps with the same embedded codomain, return `(h, pM, pN)`, where
`h(x, y) = f(x) + g(y)` on the internal direct sum of their domains, and
`pM` and `pN` are the projections. Support PIDs and maximal Dedekind orders
with their fraction fields as overrings.
"""
function addition_map(f::EmbeddedModuleMap{<:EmbeddedModule, <:EmbeddedModule},
                      g::EmbeddedModuleMap{<:EmbeddedModule, <:EmbeddedModule})
  @req codomain(f) === codomain(g) "The maps must have the same codomain"
  D, _, (pM, pN) = _direct_sum(domain(f), domain(g))
  A = vcat(matrix(data(f)), matrix(data(g)))
  return _hom(D, codomain(f), A), pM, pN
end
