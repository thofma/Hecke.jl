# PIP
# function _in(a::Vector, M::EmbeddedModule{_PID})
#   if isdefined(M, :basis_matrix_inverse)
#     t = _tmp_vec_overring(M)
#     mul!(t, a, basis_matrix_inverse(M))
#     return _has_preimage(fraction_map(M), t)
#   end
#   x, y = decompose(fraction_map(M), a)
#   Mn, Md = basis_matrix_components(M)
#   fl, z = divides(Md, y)
#   if !fl
#     return false
#   end
#   return can_solve(Mn, z * x; side = :left)
# end

function _in(a::Vector, M::EmbeddedModule{_PID}, ::Val{with_coordinates} = Val(false)) where {with_coordinates}
  if isdefined(M, :basis_matrix_inverse)
    t = _tmp_vec_overring(M)
    mul!(t, a, basis_matrix_inverse(M))
    return _has_preimage(fraction_map(M), t, Val(with_coordinates))
  end
  fl, u = can_solve_with_solution(basis_matrix(M), a; side = :left)
  if !fl
    if with_coordinates
      return false, _tmp_vec_ring(M)
    else
      return false
    end
  end
  return _has_preimage(fraction_map(M), u, Val(with_coordinates))
  #x, y = decompose(fraction_map(M), a)
  #Mn, Md = basis_matrix_components(M)
  #fl, z = divides(Md, y)
  #if !fl
  #  return false
  #end
  #return can_solve_with_solution(Mn, z * x; side = :left)
end

function _in(a::MatrixElem, M::EmbeddedModule{_PID}, ::Val{with_coordinates} = Val(false)) where {with_coordinates}
  if isdefined(M, :basis_matrix_inverse)
    t = _tmp_mat_overring(M, nrows(a))
    mul!(t, a, basis_matrix_inverse(M))
    return _has_preimage(fraction_map(M), t, Val(with_coordinates))
  end
  fl, u = can_solve_with_solution(basis_matrix(M), a; side = :left)
  if !fl
    if with_coordinates
      return false, zero_matrix(ring(M), nrows(a), rank(M))
    else
      return false
    end
  end
  return _has_preimage(fraction_map(M), u, Val(with_coordinates))
end

# Dedekind domain with given pseudo-element
function _in((a, id)::Tuple, M::EmbeddedModule{_DD})
  MB = basis_matrix(M)
  if a isa Vector
    a = matrix(overring(M), 1, length(a), a)
  end
  return Hecke._contained_in_span_of_pseudohnf(a, id, MB; shape = :lowerleft)
end

function _in(a::MatrixElem, M::EmbeddedModule{_DD})
  return Hecke._contained_in_span_of_pseudohnf(a, basis_matrix(M); shape = :lowerleft)
end

function _in(N::PMat, M::EmbeddedModule{_DD})
  return Hecke._spans_subset_of_pseudohnf(N, basis_matrix(M); shape = :lowerleft)
end

_map(x, M) = x

function Base.in(x, M::EmbeddedModule)
  return _in(_map(x, M), M)
end

function Base.in(x::PseudoElement, M::EmbeddedModule)
  if _ring_type(ring(M)) === _PID
    return _in(_map(element(x), M), M)
  else
    y = _map(element(x), M)
    return _in((y, fractional_ideal(x)), M)
  end
end

function issubset(N::EmbeddedModule, M::EmbeddedModule)
  _check_compatible(N, M)
  return _in(_short_generator_matrix(N), M)
end

function ==(M::EmbeddedModule, N::EmbeddedModule)
  M === N && return true
  is_compatible(M, N) || return false
  return issubset(M, N) && issubset(N, M)
end

function _embedded_module_hash(M::EmbeddedModule{_PID}, h::UInt)
  return hash(basis_matrix(M), h)
end

function _embedded_module_hash(M::EmbeddedModule{_DD}, h::UInt)
  P = basis_matrix(M)
  return hash(Hecke.coefficient_ideals(P), hash(matrix(P), h))
end

function Base.hash(M::EmbeddedModule, h::UInt)
  h = hash(ring(M), h)
  h = hash(overring(M), h)
  h = hash(overstructure(M), h)
  return _embedded_module_hash(M, h)
end

function index(N::EmbeddedModule{_PID}, M::EmbeddedModule; check = true)
  if check
    @req rank(N) == rank(M) "Index not defined"
    @req issubset(N, M) "Modules must be contained in each other"
  end
  if has_full_rank(N)
    i = _preimage(fraction_map(M), divexact(det(basis_matrix(N)), det(basis_matrix(M))))
    return i
  end
  fl, T = can_solve_with_solution(basis_matrix(M), basis_matrix(N); side = :left)
  @assert fl
  return _preimage(fraction_map(M), det(T))
end
