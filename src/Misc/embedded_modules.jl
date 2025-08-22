abstract type _RingType end
abstract type _PID <: _RingType end
abstract type _DD <: _RingType end
abstract type _Field <: _RingType end

_ring_type(::ZZRing) = _PID
_ring_type(::PolyRing{<:T}) where {T <: FieldElement} = _PID
_ring_type(::AbsNumFieldOrder) = _DD

# Structure to represent R-modules inside S^n, where R <= S are commutative rings and
# S = Frac(R)
mutable struct EmbeddedModule{RingType, OverringType}
  overstructure::Any # only used to check whether modules are compatible
  generator_matrix
  ring::RingType
  overring::OverringType
  fullrank::Int # 0 (unknown) 1 (yes) 2 (no)
  rank::Int
  index_multiple
  basis_matrix       # might also be a pseudo-matrix?
  basis_matrix_inverse
  denominator
  solve_context
  basis
  canonical_basis_matrix

  function EmbeddedModule(overstructure,
                          generator_matrix,
                          ring::RingType,
                          overring::OverringType
      ) where {RingType, OverringType}
    z = new{RingType, OverringType}(overstructure, generator_matrix, ring, overring, 0, -1)
  end
end

_ring_type(M::EmbeddedModule) = _ring_type(ring(M))

ring(M::EmbeddedModule) = M.ring

overring(M::EmbeddedModule) = M.overring

overstructure(M::EmbeddedModule) = M.overstructure

ambient_rank(M::EmbeddedModule) = nrows(generator_matrix(M))

index_multiple(M::EmbeddedModule) = M.index_multiple

is_known(::typeof(rank), M::EmbeddedModule) = M.rank != -1

generator_matrix(M::EmbeddedModule{RingType, OverringType}) where {RingType, OverringType} = M.generator_matrix::dense_matrix_type(OverringType)

function basis_matrix(M::EmbeddedModule{RingType, OverringType}) where {RingType, OverringType}
  if !isdefined(M, :basis_matrix)
    if is_known(index_multiple, M)
      B = _hnf_integral_modular_eldiv(generator_matrix(M), ring(M), index_multiple(M); shape = :lowerleft, cutoff = true)
    else
      B = _hnf_integral(generator_matrix(M), ring(M); shape = :lowerleft, cutoff = true)
    end
    set_basis_matrix(M, B)
  end
  return M.basis_matrix::dense_matrix_type(OverringType)
end

function set_basis_matrix(M::EmbeddedModule, B)
  M.basis_matrix = B

  # update rank
  if is_known(rank, M)
    M.rank === nrows(B)
  else
    M.rank = nrows(B)
  end

  M.fullrank = M.rank == ambient_rank(M) ? 1 : 2

  if M.fullrank == 1 && !is_known(index_multiple, M)
    M.index_multiple = prod(diagonal(B))
  end
  return M
end

function rank(M::EmbeddedModule)
  if M.rank == -1
    M.rank = nrows(basis_matrix(M))
  end
  return M.rank
end

function embedded_module(R::Ring, M::MatrixElem; overstructure = nothing, is_basis_matrix = false)
  S = base_ring(M)
  n = nrows(M)
  return EmbeddedModule(nothing, M, R, S)
end

function embedded_module(R::Ring, S::Ring, M::MatrixElem; overstructure = nothing, is_basis_matrix = false)
  if base_ring(M) === S
    N = embedded_module(R, M; overstructure)
  else
    N = embedded_module(R, change_base_Ring(S, M); overstructure)
  end

  if is_basis_matrix
    set_basis_matrix(N, M)
  end

  return N
end

function is_compatible(M::EmbeddedModule, N::EmbeddedModule)
  ring(M) !== ring(N) && return false
  overring(M) !== overring(N) && return false
  if overstructure(M) === nothing === overstructure(N)
    return ambient_rank(M) == ambient_rank(N)
  end
  return overstructure(M) === overstructure(N)
end

abstract type _EquiType end
abstract type _Equi <: _EquiType end
abstract type _NonEqui <: _EquiType end

_equi_type(M::EmbeddedModule{RingType, RingType}) where {RingType} = _Equi

_equi_type(M::EmbeddedModule{RingType, OverringType}) where {RingType, OverringType} = _NonEqui

#function is_equistructural(M::EmbeddedModule{RingType, RingType}) where {RingType}
#  return ring(M) === overring(M)
#end
#
#is_equistructural(M::EmbeddedModule{RingType, OverringType}) where {RingType, OverringType} = false

is_known(::typeof(basis_matrix), M::EmbeddedModule) = isdefined(M, :basis_matrix)

is_known(::typeof(index_multiple), M::EmbeddedModule) = isdefined(M, :index_multiple)

#is_known(::typeof(is_full_rank), M::EmbeddedModule) = M.fullrank == 1

function _short_generator_matrix(M::EmbeddedModule)
  if is_known(basis_matrix, M)
    return basis_matrix(M)
  else
    return generator_matrix(M)
  end
end

################################################################################
#
#  Show
#
################################################################################

function Base.show(io::IO, M::EmbeddedModule)
  println(io, "Embedded module over $(ring(M)) with generator matrix")
  show(io, "text/plain", _short_generator_matrix(M))
end

################################################################################
#
#  Arithmetic
#
################################################################################

_multiply_with_denominator(a::RingElement, M::EmbeddedModule) = _multiply_with_denominator(a, M, _equi_type(M))

_multiply_with_denominator(a::RingElement, M, ::Type{_Equi}) = a
_multiply_with_denominator(a::RingElement, M, ::Type{_NonEqui}) = a * denominator(M)

function Base.:(+)(M::EmbeddedModule, N::EmbeddedModule)
  @assert is_compatible(M, N)
  return +(M, N, _ring_type(M), _equi_type(M))
end

function Base.:(+)(M::EmbeddedModule, N::EmbeddedModule, ::Type{_PID}, ::Any)
  #if M === M
  #  return M
  #end
  R = ring(M)
  Mg = _short_generator_matrix(M)
  Ng = _short_generator_matrix(N)
  g = zero(R)
  if is_known(index_multiple, M)
    g = index_multiple(M)
    g = _multiply_with_denominator(g, N)
  end
  if is_known(index_multiple, N)
    g = gcd(g, _multiply_with_denominator(index_multiple(N), M))
  end
  if !is_zero(g)
    B = _hnf_integral_modular_eldiv(vcat(Mg, Ng), R, g; shape = :lowerleft, cutoff = true)
  else
    B = _hnf_integral(vcat(Mg, Ng), R; shape = :lowerleft, cutoff = true)
  end
  return embedded_module(R, overring(M), B; overstructure = overstructure(M), is_basis_matrix = true)
end

function Base.intersect(M::EmbeddedModule, N::EmbeddedModule)
  @assert is_compatible(M, N)
  return intersect(M, N, _ring_type(M), _equi_type(M))
end

function intersect(M::EmbeddedModule, N::EmbeddedModule, ::Type{_PID}, ::Any)
  @assert is_compatible(M, N)
  # this is not quite right
  R = ring(M)
  Mg = _short_generator_matrix(M)
  Mgint, d = integral_split(Mg, ring(M))
  K = _kernel_integral(vcat(Mg, _short_generator_matrix(N)), R; side = :left)
  _N = vcat(Mg, _short_generator_matrix(N))
  KK = view(K, 1:nrows(K), 1:nrows(Mg)) * Mgint
  # TODO: is this a basis?
  return embedded_module(R, overring(M), KK; overstructure = overstructure(M))
end

function Base.:(*)(a::RingElement, M::EmbeddedModule)
  if is_zero(a)
    return embedded_module(ring(M), overring(M), zero_matrix(overring(M), 0, ambient_rank(M)); is_basis_matrix = true)
  end
  if is_known(basis_matrix, M)
    aMmat = a * basis_matrix(M)
    aM = embedded_module(ring(M), overring(M), aMmat; is_basis_matrix = true)
  else
    aMmat = a * generator_matrix(M)
    aM = embedded_module(ring(M), overring(M), aMmat)
  end
  return aM
end

################################################################################
#
#  Containment(?)
#
################################################################################

function Base.in(a::Vector, M::EmbeddedModule)
  can_solve(a, basis_matrix(M); side = :left)
end
