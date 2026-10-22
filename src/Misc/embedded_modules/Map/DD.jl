# Matrices act on row pseudo-coordinates over the fraction field.
function _hom_from_ambient_matrix(M::EmbeddedModule{_DD},
                                  N::EmbeddedModule{_DD}, A::MatElem)
  _check_ambient_matrix(M, N, A)
  B = matrix(basis_matrix(M))*A
  fl, C = can_solve_with_solution(matrix(basis_matrix(N)), B; side = :left)
  @req fl "The matrix does not define a module map"
  return _hom(M, N, C)
end

function _hom(M::EmbeddedModule{_DD}, N::EmbeddedModule{_DD}, A::MatElem)
  R, K = ring(M), overring(M)
  @req R === ring(N) "The modules must have the same coefficient ring"
  @req K === overring(N) "The modules must have the same overring"
  @req Hecke.is_maximal(R) "The coefficient ring must be a maximal order"
  @req K === Hecke.field(R) "The overring must be the fraction field"
  @req base_ring(A) === K "The matrix must be over the fraction field"
  @req nrows(A) == rank(M) &&
       ncols(A) == rank(N) "The matrix has the wrong dimensions"
  I = Hecke.coefficient_ideals(basis_matrix(M))
  J = Hecke.coefficient_ideals(basis_matrix(N))
  for i in 1:nrows(A), j in 1:ncols(A)
    iszero(A[i, j]) && continue
    @req Hecke.is_integral(
      (A[i, j]*I[i])//J[j]) "The matrix does not define a module map"
  end
  return EmbeddedModuleMap(M, N, EmbeddedModuleMapDDData(M, N, A))
end

domain(f::EmbeddedModuleMapDDData) = f.domain
codomain(f::EmbeddedModuleMapDDData) = f.codomain
ring_map(f::EmbeddedModuleMapDDData) = f.ring_map
matrix(f::EmbeddedModuleMapDDData) = f.matrix

function image(f::EmbeddedModuleMapDDData, x::EmbeddedModuleElem)
  @req parent(x) === domain(f) "Element not in domain"
  c = coordinates(x; copy = false)*matrix(f)
  return _element_from_coordinates(codomain(f), c; check = false)
end

@attr Tuple{Hecke.pseudo_matrix_type(R, K),
            dense_matrix_type(K)} function _matrix_normal_form(
    f::EmbeddedModuleMapDDData{<:EmbeddedModule{_DD, R, K}}) where {R, K}
  M = domain(f)
  P = Hecke.pseudo_matrix(ring(M), matrix(f),
                          Hecke.coefficient_ideals(basis_matrix(M)))
  if iszero(nrows(P)) || iszero(ncols(P))
    return P, Hecke.identity_matrix(overring(M), nrows(P))
  end
  # Cohen, Advanced Topics in Computational Number Theory, Section 1.4:
  # H = T*A, and the new row ideals times T lie in the source row ideals.
  return Hecke.pseudo_hnf_with_transform(P, :lowerleft)
end

function preimage(f::EmbeddedModuleMapDDData, y::EmbeddedModuleElem)
  @req parent(y) === codomain(f) "Element not in codomain"
  M = domain(f)
  iszero(y) && return zero(M)
  H, T = _matrix_normal_form(f)
  v = matrix(overring(M), 1, rank(codomain(f)),
             coordinates(y; copy = false))
  fl, c = Hecke._contained_in_span_of_pseudohnf(v, H, Val(true);
                                               shape = :lowerleft)
  @req fl "Element has no preimage"
  return _element_from_coordinates(M, (c*T)[1, :])
end

function image(f::EmbeddedModuleMapDDData)
  M, N = domain(f), codomain(f)
  iszero(matrix(f)) && return _zero_module_like(N)
  B = matrix(f)*matrix(basis_matrix(N))
  P = Hecke.pseudo_matrix(ring(M), B,
                          Hecke.coefficient_ideals(basis_matrix(M)))
  return embedded_module(ring(N), overring(N), P;
                         overstructure = overstructure(N))
end

function kernel(f::EmbeddedModuleMapDDData)
  M = domain(f)
  iszero(matrix(f)) && return M
  H, T = _matrix_normal_form(f)
  r = count(i -> is_zero_row(matrix(H), i), 1:nrows(H))
  B = sub(T, 1:r, 1:ncols(T))*matrix(basis_matrix(M))
  P = Hecke.pseudo_matrix(ring(M), B, Hecke.coefficient_ideals(H)[1:r])
  return embedded_module(ring(M), overring(M), P;
                         overstructure = overstructure(M))
end

is_injective(f::EmbeddedModuleMapDDData) =
  rank(matrix(f)) == rank(domain(f))
is_surjective(f::EmbeddedModuleMapDDData) = image(f) == codomain(f)
is_bijective(f::EmbeddedModuleMapDDData) =
  is_injective(f) && is_surjective(f)

function matrix(f::EmbeddedModuleDataEmbedding{<:EmbeddedModule{_DD},
                                              <:EmbeddedModule{_DD}})
  fl, A = can_solve_with_solution(matrix(basis_matrix(codomain(f))),
                                 matrix(basis_matrix(domain(f)));
                                 side = :left)
  @assert fl
  return A
end
