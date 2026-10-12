function hom(M::EmbeddedModule{_PID}, X, images::Vector)
  @req length(images) == rank(M) "Wrong number of basis images"
  @req all(x -> parent(x) === X, images) "Images must belong to the codomain"
  if X isa EmbeddedModule
    @req ring(M) === ring(X) "The modules must have the same coefficient ring"
  end
  return EmbeddedModuleMap(M, X,
                           EmbeddedModuleMapPIDData(M, X, identity, images))
end

function hom(M::EmbeddedModule{_PID}, X, imgs::Vector{<:Pair})
  @req all(p -> first(p) isa EmbeddedModuleElem && parent(first(p)) === M,
           imgs) "Source elements must belong to the domain"
  @req all(p -> parent(last(p)) === X, imgs) "Images must belong to the codomain"
  if X isa EmbeddedModule
    @req ring(M) === ring(X) "The modules must have the same coefficient ring"
  end

  r = rank(M)
  if iszero(r)
    @req all(p -> iszero(last(p)), imgs) "Map not well-defined"
    return hom(M, X, elem_type(X)[])
  end
  @req !isempty(imgs) "The source elements must generate the domain"

  R = ring(M)
  A = zero_matrix(R, length(imgs), r)
  for i in eachindex(imgs)
    A[i, :] = coordinates(first(imgs[i]); copy = false)
  end
  fl, C = _basis_coordinates_in_generators(A)
  @req fl "The source elements must generate the domain"

  images = elem_type(X)[zero(X) for i in 1:r]
  for i in 1:r, j in eachindex(imgs)
    images[i] += C[i, j] * last(imgs[j])
  end
  f = hom(M, X, images)
  # Agreement on the generators ensures that every relation maps to zero.
  @req all(p -> f(first(p)) == last(p), imgs) "Map not well-defined"
  return f
end

domain(f::EmbeddedModuleMapPIDData) = f.domain

codomain(f::EmbeddedModuleMapPIDData) = f.codomain

ring_map(f::EmbeddedModuleMapPIDData) = f.ring_map

image_basis(f::EmbeddedModuleMapPIDData) = f.image_basis

function image(f::EmbeddedModuleMapPIDData, x::EmbeddedModuleElem)
  @req parent(x) === domain(f) "Element not in domain"
  g = ring_map(f)
  y = zero(codomain(f))
  c = coordinates(x; copy = false)
  B = image_basis(f)
  for i in eachindex(c)
    y += g(c[i]) * B[i]
  end
  return y
end

function preimage(f::EmbeddedModuleMapPIDData, y)
  @req parent(y) === codomain(f) "Element not in codomain"
  error("Preimage not available for this map")
end

function matrix(f::EmbeddedModuleMapPIDData{<:EmbeddedModule{_PID},
                                          <:EmbeddedModule{_PID}})
  R = ring(domain(f))
  if !isdefined(f.data, :matrix)
    B = image_basis(f)
    A = zero_matrix(R, rank(domain(f)), rank(codomain(f)))
    for i in eachindex(B)
      A[i, :] = coordinates(B[i]; copy = false)
    end
    f.data.matrix = A
  end
  return f.data.matrix::dense_matrix_type(R)
end

function solve_context_of_matrix(f::EmbeddedModuleMapPIDData)
  if !isdefined(f.data, :solve_context)
    f.data.solve_context = Hecke.solve_init(matrix(f))
  end
  R = ring(domain(f))
  return f.data.solve_context::Hecke.AbstractAlgebra.Solve.solve_context_type(R)
end

function image(f::EmbeddedModuleMapPIDData{<:EmbeddedModule{_PID},
                                         <:EmbeddedModule{_PID}},
               x::EmbeddedModuleElem)
  @req parent(x) === domain(f) "Element not in domain"
  c = coordinates(x; copy = false) * matrix(f)
  return _element_from_coordinates(codomain(f), c; check = false)
end

function preimage(f::EmbeddedModuleMapPIDData{<:EmbeddedModule{_PID},
                                            <:EmbeddedModule{_PID}},
                  y::EmbeddedModuleElem)
  @req parent(y) === codomain(f) "Element not in codomain"
  ctx = solve_context_of_matrix(f)
  fl, c = can_solve_with_solution(ctx, coordinates(y; copy = false);
                                side = :left)
  @req fl "Element has no preimage"
  return _element_from_coordinates(domain(f), c; check = false)
end

function image(f::EmbeddedModuleMapPIDData{<:EmbeddedModule{_PID},
                                         <:EmbeddedModule{_PID}})
  N = codomain(f)
  iszero(rank(domain(f))) && return _zero_module_like(N)
  B = change_base_ring(overring(N), matrix(f)) * basis_matrix(N)
  return embedded_module(ring(N), overring(N), B;
                         overstructure = overstructure(N))
end

function kernel(f::EmbeddedModuleMapPIDData{<:EmbeddedModule{_PID},
                                          <:EmbeddedModule{_PID}})
  M = domain(f)
  iszero(rank(M)) && return _zero_module_like(M)
  iszero(rank(codomain(f))) && return M
  K = kernel(solve_context_of_matrix(f); side = :left)
  B = change_base_ring(overring(M), K) * basis_matrix(M)
  return embedded_module(ring(M), overring(M), B;
                         overstructure = overstructure(M))
end

function is_injective(f::EmbeddedModuleMapPIDData{<:EmbeddedModule{_PID},
                                                <:EmbeddedModule{_PID}})
  iszero(rank(domain(f))) && return true
  iszero(rank(codomain(f))) && return false
  return iszero(nrows(kernel(solve_context_of_matrix(f); side = :left)))
end

function is_surjective(f::EmbeddedModuleMapPIDData{<:EmbeddedModule{_PID},
                                                 <:EmbeddedModule{_PID}})
  N = codomain(f)
  iszero(rank(N)) && return true
  I = Hecke.identity_matrix(ring(N), rank(N))
  return Hecke.can_solve(solve_context_of_matrix(f), I; side = :left)
end

is_bijective(f::EmbeddedModuleMapPIDData) = is_injective(f) && is_surjective(f)
