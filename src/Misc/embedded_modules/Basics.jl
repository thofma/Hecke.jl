_embedded_module_type(::Type{R}, ::Type{OR}) where {R, OR} = EmbeddedModule{_ring_type(R), R, OR}

_ring_type(M::EmbeddedModule) = _ring_type(ring(M))

ring(M::EmbeddedModule) = M.ring

overring(M::EmbeddedModule) = M.overring

overstructure(M::EmbeddedModule) = M.overstructure

ambient_rank(M::EmbeddedModule) = ncols(generator_matrix(M))

index_multiple(M::EmbeddedModule) = M.index_multiple

fraction_map(M::EmbeddedModule) = M.fractionmap

is_known(::typeof(rank), M::EmbeddedModule) = M.rank != -1

_tmp_vec_ring(M::EmbeddedModule) = (isdefined(M, :tmp_vec_ring) ? M.tmp_vec_ring : M.tmp_vec_ring = [zero(ring(M)) for i in 1:ambient_rank(M)])::Vector{elem_type(ring(M))}

_tmp_vec_overring(M::EmbeddedModule) = (isdefined(M, :tmp_vec_overring) ? M.tmp_vec_overring : M.tmp_vec_overring = [zero(overring(M)) for i in 1:ambient_rank(M)])::Vector{elem_type(overring(M))}

function _tmp_mat_overring(M::EmbeddedModule, r::Int = 1)
  if isdefined(M, :tmp_mat_overring)
    if nrows(M.tmp_mat_overring::dense_matrix_type(overring(M))) < r
      t = zero_matrix(overring(M), r, ambient_rank(M))
      M.tmp_mat_overring = t
      return t
    else
      t = M.tmp_mat_overring::dense_matrix_type(overring(M))
      return @view t[1:r, :]
    end
  else
    t = zero_matrix(overring(M), r, ambient_rank(M))
    M.tmp_mat_overring = t
    return t
  end
end

generator_matrix(M::EmbeddedModule{_PID, RingType, OverringType}) where {RingType, OverringType} = M.generator_matrix

generator_matrix(M) = M.generator_matrix

# For type _PID, we assume that the ring supports hnf and hnf_modular_eldiv with all
# trim options and shape options

function basis_matrix_numerator(M::EmbeddedModule{_PID, RingType, OverringType}) where {RingType, OverringType}
  if !isdefined(M, :basis_matrix_numerator)
    if isdefined(M, :basis_matrix)
      N, d = decompose(fraction_map(M), basis_matrix(M))
      set_basis_matrix_components(M, N, d)
      return M.basis_matrix_numerator::dense_matrix_type(RingType)
    end
    @assert isdefined(M, :generator_matrix)
    N, d = decompose(fraction_map(M), generator_matrix(M))
    if is_known(index_multiple, M)
      NN = _hnf_modular_eldiv(N, index_multiple(M); shape = :lowerleft, trim = true)
      #B = hnf_modular_eldiv(generator_matrix(M), ring(M), index_multiple(M); shape = :lowerleft, cutoff = true)
    else
      NN = _hnf(N; shape = :lowerleft, trim = true)
    end
    set_basis_matrix_components(M, NN, d)

  end
  return M.basis_matrix_numerator::dense_matrix_type(RingType)
end

basis_matrix_components(M::EmbeddedModule{_PID, RingType, OverringType}) where {RingType, OverringType} = (basis_matrix_numerator(M), M.denominator)::Tuple{dense_matrix_type(RingType), elem_type(RingType)}

function basis_matrix(M::EmbeddedModule{_DD, RingType, OverringType}) where {RingType, OverringType}
  if isdefined(M, :basis_matrix)
    return M.basis_matrix::Hecke.pseudo_matrix_type(RingType, OverringType)
  end
  N = Hecke.pseudo_hnf(generator_matrix(M), :lowerleft)
  # trim myself :(
  NN = matrix(N)
  k = findfirst(i -> !is_zero_row(NN, i), 1:nrows(NN))
  if k === nothing
    N = sub(N, 1:0, 1:ncols(N))
  else
    N = sub(N, k:nrows(N), 1:ncols(N))
  end
  M.basis_matrix = N
  return N
end

function basis_matrix(M::EmbeddedModule{_PID, RingType, OverringType}) where {RingType, OverringType}
  if isdefined(M, :basis_matrix)
    return M.basis_matrix::dense_matrix_type(OverringType)
  else
    @assert isdefined(M, :generator_matrix)
    N, d = decompose(fraction_map(M), generator_matrix(M))
    NN = _hnf(N; shape = :lowerleft, trim = true)
    set_basis_matrix_components(M, NN, d)
  end

  @assert isdefined(M, :basis_matrix_numerator)
  N = basis_matrix_numerator(M)
  d = M.denominator
  M.basis_matrix = divexact(change_base_ring(overring(M), N), d)
  return M.basis_matrix::dense_matrix_type(OverringType)
end

function basis_matrix_inverse(N)
  if !isdefined(N, :basis_matrix_inverse)
    N.basis_matrix_inverse = inv(basis_matrix(N))
  end
  return N.basis_matrix_inverse::dense_matrix_type(overring(N))
end

function set_basis_matrix_inverse(N, M)
  @assert !isdefined(N, :basis_matrix_inverse)
  N.basis_matrix_inverse = M
  return N.basis_matrix_inverse::dense_matrix_type(overring(N))
end

function set_basis_matrix(N, M)
  @assert !isdefined(N, :basis_matrix)
  N.basis_matrix = M
  return N.basis_matrix::dense_matrix_type(overring(N))
end

function set_basis_matrix(N::EmbeddedModule{_DD, RingType, OverringType}, M::PMat) where {RingType, OverringType}
  @assert !isdefined(N, :basis_matrix)
  N.basis_matrix = M
  return N.basis_matrix::Hecke.pseudo_matrix_type(RingType, OverringType)
end

function set_basis_matrix_components(M::EmbeddedModule, B, d)
  M.basis_matrix_numerator = B
  if d !== nothing
    if !isdefined(M, :denominator)
      M.denominator = d
    else
      @assert M.denominator == d
    end
  end

  # update rank
  if is_known(rank, M)
    @assert M.rank === nrows(B)
  else
    M.rank = nrows(B)
  end

  M.fullrank = M.rank == ambient_rank(M) ? 1 : 2

  if M.fullrank == 1 && !is_known(index_multiple, M) && Hecke.is_triangular(B)
    #@assert is_triangular(B)
    # wrong if not integral?
    M.index_multiple = prod(diagonal(B))
  end

  return M
end

function rank(M::EmbeddedModule{_PID})
  if M.rank == -1
    M.rank = nrows(basis_matrix_numerator(M))
  end
  return M.rank
end

function rank(M::EmbeddedModule{_DD})
  if M.rank == -1
    M.rank = nrows(basis_matrix(M))
  end
  return M.rank
end

zero_embedded_module(R, S, n::Int) = embedded_module(R, S, zero_matrix(S, 0, n))

@doc raw"""
    embedded_module(R::Ring, S::Ring, M; overstructure = nothing,
                    is_basis_matrix = false, inverse = nothing)

Construct the $R$-submodule of $S^n$ generated by the rows of `M`. Over a
Dedekind domain, `M` may be a pseudo-matrix. Use `is_basis_matrix` when `M` is
already a basis, and `overstructure` to identify an optional ambient object.
"""
function embedded_module(R::Ring, S::Ring, M#=::MatrixElem or PMat=#; overstructure = nothing, is_basis_matrix = false, inverse = nothing)
  if base_ring(M) === S || _ring_type(R) === _DD
    N = EmbeddedModule(overstructure, M, R, S)
  else
    N = EmbeddedModule(overstructure, change_base_ring(S, M), R, S)
  end

  if is_basis_matrix
    set_basis_matrix(N, M)
  end

  if inverse !== nothing
    set_basis_matrix_inverse(N, inverse::dense_matrix_type(S))
  end

  return N
end

function is_compatible(M::EmbeddedModule, N::EmbeddedModule)
  ring(M) === ring(N) || return false
  overring(M) === overring(N) || return false
  overstructure(M) === overstructure(N) || return false
  return ambient_rank(M) == ambient_rank(N)
end

function _check_compatible(M::EmbeddedModule, N::EmbeddedModule)
  @req is_compatible(M, N) "The embedded modules have different ambient structures"
  return nothing
end

is_known(::typeof(basis_matrix), M::EmbeddedModule) = isdefined(M, :basis_matrix)

is_known(::typeof(index_multiple), M::EmbeddedModule) = isdefined(M, :index_multiple)

#is_known(::typeof(is_full_rank), M::EmbeddedModule) = M.fullrank == 1

has_full_rank(M::EmbeddedModule) = rank(M) == ambient_rank(M)

function _short_generator_matrix(M::EmbeddedModule)
  if is_known(basis_matrix, M)
    return basis_matrix(M)
  else
    return generator_matrix(M)
  end
end
