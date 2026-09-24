function quo(M::EmbeddedModule, N::EmbeddedModule)
  BM = basis_matrix(M)
  fl, T = can_solve_with_solution(basis_matrix(M), basis_matrix(N); side = :left)
  @req fl "Not a submodule"
  F = free_module(ring(M), nrows(BM))
  S, _ = sub(F, [F(T[i, :]) for i in 1:nrows(T)])
  Q, FtoQ = quo(F, S)
  Q, MapFromFunc(M, Q, x -> FtoQ(F(coordinates(x))), y -> _element_from_coordinates(M, Hecke.AbstractAlgebra.Generic._matrix(preimage(FtoQ, y))))
end

function quotient_vector_space(M::EmbeddedModule, N::EmbeddedModule, p::RingElem)
  R = ring(M)
  @assert parent(p) === R
  @assert is_prime(p)
  F, RtoF = residue_field(R, p)
  Q, MtoQ = quo(M, N)
  S, StoQ = snf(Q)
  invfac = invariant_factors(S)
  @assert all(x -> is_divisible_by(p, x) && is_divisible_by(x, p), invfac)
  QQ = free_module(F, length(invfac))
  QQ, MapFromFunc(M, QQ, x -> QQ(RtoF.(Hecke.AbstractAlgebra.Generic._matrix(preimage(StoQ, MtoQ(x))))), y -> preimage(MtoQ, StoQ(S(preimage.(RtoF, Hecke.AbstractAlgebra.Generic._matrix(y)))))), RtoF
end
