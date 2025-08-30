abstract type _RingType end
abstract type _PID <: _RingType end
abstract type _DD <: _RingType end
abstract type _Field <: _RingType end

_ring_type(::Type{ZZRing}) = _PID
_ring_type(::Type{<:PolyRing{<:T}}) where {T <: FieldElement} = _PID
_ring_type(::Type{KInftyRing{T}}) where {T <: FieldElement} = _PID
_ring_type(::Type{<:AbsNumFieldOrder}) = _DD
_ring_type(R::Ring) = _ring_type(typeof(R))

struct PseudoElement{S, T}
  elem::S
  ideal::T

  PseudoElement(elem, ideal) = new{typeof(elem), typeof(ideal)}(elem, ideal)
end

element(p::PseudoElement) = p.elem
fractional_ideal(p::PseudoElement) = p.ideal

_pseudo_element(elem, R::Ring) = _pseudo_element(elem, R, _ring_type(R))

function _pseudo_element(elem, R::Ring, ::Type{_PID})
  return PseudoElement(elem, nothing)
end

function _pseudo_element(elem, id)
  return PseudoElement(elem, id)
end

function _pseudo_element(elem, R::Ring, ::Type{_DD})
  return PseudoElement(elem, fractional_ideal(R, one(R)))
end

function Base.:(*)(x::PseudoElement, y::PseudoElement)
  return PseudoElement(x.elem * y.elem, x.ideal === nothing ? nothing : x.ideal * y.ideal)
end


# Structure to represent R-modules inside S^n, where R <= S are commutative rings and
# S = Frac(R)
mutable struct EmbeddedModule{RingTypeType, RingType, OverringType}
  overstructure::Any # only used to check whether modules are compatible
  generator_matrix
  ring::RingType
  overring::OverringType
  fractionmap::FractionFieldMap{RingType, OverringType}
  fullrank::Int # 0 (unknown) 1 (yes) 2 (no)
  rank::Int
  index_multiple
  basis_matrix       # might also be a pseudo-matrix? unique?
  basis_matrix_inverse
  basis_matrix_numerator
  denominator
  solve_context
  basis
  canonical_basis_matrix
  tmp_vec_ring
  tmp_vec_overring
  tmp_mat_overring

  function EmbeddedModule(overstructure,
                          generator_matrix,
                          ring::RingType,
                          overring::OverringType
      ) where {RingType, OverringType}
    z = new{_ring_type(ring), RingType, OverringType}(overstructure, generator_matrix, ring, overring, fraction_field_map(ring, overring), 0, -1)
  end
end

_ring_type(M::EmbeddedModule) = _ring_type(ring(M))

ring(M::EmbeddedModule) = M.ring

overring(M::EmbeddedModule) = M.overring

overstructure(M::EmbeddedModule) = M.overstructure

ambient_rank(M::EmbeddedModule) = ncols(generator_matrix(M))

index_multiple(M::EmbeddedModule) = M.index_multiple

fraction_map(M::EmbeddedModule) = M.fractionmap

is_known(::typeof(rank), M::EmbeddedModule) = M.rank != -1

_tmp_vec_ring(M::EmbeddedModule) = (isdefined(M, :tmp_vec_ring) ? M.tmp_vec_ring : M.tmp_vec_ring = [zero(ring(M)) for i in ambient_rank(M)])::Vector{elem_type(ring(M))}

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
    return M.basis_matrix::pseudo_matrix_type(RingType, OverringType)
  end
  N = pseudo_hnf(generator_matrix(M), :lowerleft)
  # trim myself :(
  NN = matrix(N)
  k = findfirst(i -> !is_zero_row(NN, i), 1:nrows(NN))
  N = sub(N, k:nrows(N), 1:ncols(N))
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

  if M.fullrank == 1 && !is_known(index_multiple, M) && is_triangular(B)
    #@assert is_triangular(B)
    # this is wrong if the matrix is not triangular
    # also wrong if not integral
    M.index_multiple = prod(diagonal(B))
  end

  return M
end

function rank(M::EmbeddedModule)
  if M.rank == -1
    M.rank = nrows(basis_matrix_numerator(M))
  end
  return M.rank
end
# #
# function embedded_module(R::Ring, M#=::MatrixElem or PMat=#; overstructure = nothing, is_basis_matrix = false)
#   S = _ring_type(R) === _DD ? nf(base_ring(M)) : base_ring(M) # fix this
#   n = nrows(M)
#   return EmbeddedModule(overstructure, M, R, S)
# end

zero_embedded_module(R, S, n::Int) = embedded_module(R, S, zero_matrix(S, 0, n))

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
#
#function is_compatible(M::EmbeddedModule, N::EmbeddedModule)
#  ring(M) !== ring(N) && return false
#  overring(M) !== overring(N) && return false
#  if overstructure(M) === nothing === overstructure(N)
#    return ambient_rank(M) == ambient_rank(N)
#  end
#  return overstructure(M) === overstructure(N)
#end
#
#abstract type _EquiType end
#abstract type _Equi <: _EquiType end
#abstract type _NonEqui <: _EquiType end
#
#_equi_type(M::EmbeddedModule{RingType, RingType}) where {RingType} = _Equi
#
#_equi_type(M::EmbeddedModule{RingType, OverringType}) where {RingType, OverringType} = _NonEqui
#
##function is_equistructural(M::EmbeddedModule{RingType, RingType}) where {RingType}
##  return ring(M) === overring(M)
##end
##
##is_equistructural(M::EmbeddedModule{RingType, OverringType}) where {RingType, OverringType} = false
#
is_known(::typeof(basis_matrix), M::EmbeddedModule) = isdefined(M, :basis_matrix)

is_known(::typeof(index_multiple), M::EmbeddedModule) = isdefined(M, :index_multiple)

#is_known(::typeof(is_full_rank), M::EmbeddedModule) = M.fullrank == 1

has_full_rank(M::EmbeddedModule) = rank(M) == ambient_rank(M)
#
#function _short_generator_matrix(M::EmbeddedModule)
#  if is_known(basis_matrix, M)
#    return basis_matrix(M)
#  else
#    return generator_matrix(M)
#  end
#end
#
#################################################################################
##
##  Show
##
#################################################################################
#
#function Base.show(io::IO, M::EmbeddedModule)
#  println(io, "Embedded module over $(ring(M)) with generator matrix")
#  show(io, "text/plain", _short_generator_matrix(M))
#end
#
#################################################################################
##
##  Arithmetic
##
#################################################################################
#
#_multiply_with_denominator(a::RingElement, M::EmbeddedModule) = _multiply_with_denominator(a, M, _equi_type(M))
#
#_multiply_with_denominator(a::RingElement, M, ::Type{_Equi}) = a
#_multiply_with_denominator(a::RingElement, M, ::Type{_NonEqui}) = a * denominator(M)
#
#function Base.:(+)(M::EmbeddedModule, N::EmbeddedModule)
#  @assert is_compatible(M, N)
#  return +(M, N, _ring_type(M), _equi_type(M))
#end
#
## the implementation is cheating, since _hnf_integral takes care of the
## HNF of rational matrices
#function Base.:(+)(M::EmbeddedModule, N::EmbeddedModule, ::Type{_PID}, ::Any)
#  #if M === M
#  #  return M
#  #end
#  R = ring(M)
#  Mg = _short_generator_matrix(M)
#  Ng = _short_generator_matrix(N)
#  g = zero(R)
#  if is_known(index_multiple, M)
#    g = index_multiple(M)
#    g = _multiply_with_denominator(g, N)
#  end
#  if is_known(index_multiple, N)
#    g = gcd(g, _multiply_with_denominator(index_multiple(N), M))
#  end
#  if !is_zero(g)
#    B = _hnf_integral_modular_eldiv(vcat(Mg, Ng), R, g; shape = :lowerleft, cutoff = true)
#  else
#    B = _hnf_integral(vcat(Mg, Ng), R; shape = :lowerleft, cutoff = true)
#  end
#  return embedded_module(R, overring(M), B; overstructure = overstructure(M), is_basis_matrix = true)
#end
#
#function Base.intersect(M::EmbeddedModule, N::EmbeddedModule)
#  @assert is_compatible(M, N)
#  return intersect(M, N, _ring_type(M), _equi_type(M))
#end
#
#function intersect(M::EmbeddedModule, N::EmbeddedModule, ::Type{_PID}, ::Any)
#  @assert is_compatible(M, N)
#  # this is not quite right
#  R = ring(M)
#  Mg = _short_generator_matrix(M)
#  Mgint, d = integral_split(Mg, ring(M))
#  K = _kernel_integral(vcat(Mg, _short_generator_matrix(N)), R; side = :left)
#  _N = vcat(Mg, _short_generator_matrix(N))
#  KK = view(K, 1:nrows(K), 1:nrows(Mg)) * Mgint
#  # TODO: is this a basis?
#  return embedded_module(R, overring(M), KK; overstructure = overstructure(M))
#end
#
#function Base.:(*)(a::RingElement, M::EmbeddedModule)
#  if is_zero(a)
#    return embedded_module(ring(M), overring(M), zero_matrix(overring(M), 0, ambient_rank(M)); is_basis_matrix = true)
#  end
#  if is_known(basis_matrix, M)
#    aMmat = a * basis_matrix(M)
#    aM = embedded_module(ring(M), overring(M), aMmat; is_basis_matrix = true)
#  else
#    aMmat = a * generator_matrix(M)
#    aM = embedded_module(ring(M), overring(M), aMmat)
#  end
#  return aM
#end

################################################################################
#
#  Containment(?)
#
################################################################################

# PIP
function _in(a::Vector, M::EmbeddedModule{_PID})
  if isdefined(M, :basis_matrix_inverse)
    t = _tmp_vec_overring(M)
    mul!(t, a, basis_matrix_inverse(M))
    return _has_preimage(fraction_map(M), t)
  end
  x, y = decompose(fraction_map(M), a)
  Mn, Md = basis_matrix_components(M)
  fl = is_divisible_by(Md, y)
  if !fl
    return false
  end
  return can_solve(Mn, x; side = :left)
end

function _in(a::MatrixElem, M::EmbeddedModule{_PID})
  if isdefined(M, :basis_matrix_inverse)
    mul!(a, a, basis_matrix_inverse(M))
    return _has_preimage(fraction_map(M), a)
  end
  x, y = decompose(fraction_map(M), a)
  Mn, Md = basis_matrix_components(M)
  fl = is_divisible_by(Md, y)
  if !fl
    return false
  end
  return can_solve(Mn, x; side = :left)
end

# Dedekind domain with given pseudo-element
function _in((a, id)::Tuple, M::EmbeddedModule{_DD})
  MB = basis_matrix(M)
  return _contained_in_span_of_pseudohnf(a, id, MB; shape = :lowerleft)
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
