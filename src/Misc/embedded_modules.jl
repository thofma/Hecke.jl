abstract type _RingType end
abstract type _PID <: _RingType end
abstract type _DD <: _RingType end
abstract type _Field <: _RingType end

_ring_type(::Type{ZZRing}) = _PID
_ring_type(::Type{<:PolyRing{<:T}}) where {T <: FieldElement} = _PID
_ring_type(::Type{<:KInftyRing{T}}) where {T <: FieldElement} = _PID
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

mutable struct EmbeddedModuleElem{ModuleType, RingType, OverringType}
  mod::ModuleType
  coords#::Vector{elem_type(RingType)}
  ambientcoords#::Vector{elem_type(OverringType)}
  pseudocoords#::Vector{elem_type(OverringType)} # Dedekind module case

  function EmbeddedModuleElem(M::EmbeddedModule{S, RingType, OverringType}) where {S, RingType, OverringType}
    return new{typeof(M), RingType, OverringType}(M)
  end
end

parent(x::EmbeddedModuleElem) = x.mod

elem_type(M::EmbeddedModule{RingTypeType, RingType, OverringType}) where {RingTypeType, RingType, OverringType} = EmbeddedModuleElem{typeof(M), RingType, OverringType}

function Base.deepcopy_internal(x::EmbeddedModuleElem, dict::IdDict)
  haskey(dict, x) && return dict[x]
  y = EmbeddedModuleElem(parent(x))
  dict[x] = y
  isdefined(x, :coords) && (y.coords = Base.deepcopy_internal(x.coords, dict))
  isdefined(x, :ambientcoords) && (y.ambientcoords = Base.deepcopy_internal(x.ambientcoords, dict))
  isdefined(x, :pseudocoords) && (y.pseudocoords = Base.deepcopy_internal(x.pseudocoords, dict))
  return y
end

function _element_from_ambient_coordinates(M::EmbeddedModule{S, T, OverringType}, x::Vector; check::Bool = true) where {S, T, OverringType}
  z = EmbeddedModuleElem(M)
  @assert eltype(x) === elem_type(OverringType)
  z.ambientcoords = x
  if check
    fl, c = _in(x, M, Val(true))
    @req fl "Element not contained in module"
    z.coords = c
  end
  return z
end

function _element_from_coordinates(M::EmbeddedModule{S, RingType, OverringType}, x::MatElem; check::Bool = true) where {S, RingType, OverringType}
  return _element_from_coordinates(M, x[1, :]; check)
end

function _element_from_coordinates(M::EmbeddedModule{S, RingType, OverringType}, x::Vector; check::Bool = true) where {S, RingType, OverringType}
  z = EmbeddedModuleElem(M)
  @assert eltype(x) === elem_type(RingType)
  z.coords = x
  return z
end

function _element_from_coordinates_and_ambient_coordinates(M::EmbeddedModule{S, RingType, OverringType}, x::Vector, y::Vector; check::Bool = true) where {S, RingType, OverringType}
  z = EmbeddedModuleElem(M)
  @assert eltype(x) === elem_type(RingType)
  @assert eltype(y) === elem_type(OverringType)
  z.coords = x
  z.ambientcoords = y
  if check
    fl, c = _in(y, M, Val(true))
    @req c == x "Element not contained in module"
  end
  return z
end

function coordinates(x::EmbeddedModuleElem{S, RingType}; copy::Bool = true) where {S, RingType}
  if isdefined(x, :coords)
    r = x.coords::Vector{elem_type(RingType)}
    return copy ? deepcopy(r) : r
  else
    fl, c = _in(x.ambientcoords, x.mod, Val(true))
    !fl && error("internal error: element not in module")
    x.coords = c
    r = x.coords::Vector{elem_type(RingType)}
    return copy ? deepcopy(r) : r
  end
end

function ambient_coordinates(x::EmbeddedModuleElem{<:Any, RingType, OverringType}) where {RingType, OverringType}
  if isdefined(x, :ambientcoords)
    return x.ambientcoords::Vector{elem_type(OverringType)}

  else
    x.ambientcoords = coordinates(x) * basis_matrix(parent(x))
    return x.ambientcoords::Vector{elem_type(OverringType)}
  end
end

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
    return M.basis_matrix::pseudo_matrix_type(RingType, OverringType)
  end
  N = pseudo_hnf(generator_matrix(M), :lowerleft)
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
  return N.basis_matrix::pseudo_matrix_type(RingType, OverringType)
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
#
function _short_generator_matrix(M::EmbeddedModule)
  if is_known(basis_matrix, M)
    return basis_matrix(M)
  else
    return generator_matrix(M)
  end
end
################################################################################
#
#  Arithmetic
#
################################################################################

function _zero_module_like(M::EmbeddedModule{_PID})
  B = zero_matrix(overring(M), 0, ambient_rank(M))
  return embedded_module(ring(M), overring(M), B;
                         overstructure = overstructure(M), is_basis_matrix = true)
end

function _zero_module_like(M::EmbeddedModule{_DD})
  B = zero_matrix(overring(M), 0, ambient_rank(M))
  C = typeof(fractional_ideal(ring(M), one(ring(M))))[]
  P = pseudo_matrix(ring(M), B, C)
  return embedded_module(ring(M), overring(M), P;
                         overstructure = overstructure(M), is_basis_matrix = true)
end

function _sum(M::EmbeddedModule, N::EmbeddedModule, ::Type{_PID})
  B = vcat(basis_matrix(M), basis_matrix(N))
  return embedded_module(ring(M), overring(M), B; overstructure = overstructure(M))
end

function _sum(M::EmbeddedModule, N::EmbeddedModule, ::Type{_DD})
  P = vcat(basis_matrix(M), basis_matrix(N))
  return embedded_module(ring(M), overring(M), P; overstructure = overstructure(M))
end

function +(M::EmbeddedModule, N::EmbeddedModule)
  _check_compatible(M, N)
  return _sum(M, N, _ring_type(M))
end

function _intersect(M::EmbeddedModule, N::EmbeddedModule, ::Type{_PID})
  if iszero(rank(M)) || iszero(rank(N))
    return _zero_module_like(M)
  end

  BM = basis_matrix(M)
  BN = basis_matrix(N)
  # Integral relations (u, v) with u*BM = v*BN parametrize M intersect N.
  C, _ = decompose(fraction_map(M), vcat(BM, -BN))
  relations = kernel(C; side = :left)
  if iszero(nrows(relations))
    return _zero_module_like(M)
  end

  KM = sub(relations, 1:nrows(relations), 1:nrows(BM))
  B = change_base_ring(overring(M), KM)*BM
  return embedded_module(ring(M), overring(M), B; overstructure = overstructure(M))
end

function _intersect(M::EmbeddedModule, N::EmbeddedModule, ::Type{_DD})
  if iszero(rank(M)) || iszero(rank(N))
    return _zero_module_like(M)
  end

  PM = deepcopy(basis_matrix(M))
  PN = deepcopy(basis_matrix(N))
  if nrows(PN) > nrows(PM)
    PM, PN = PN, PM
  end

  # In the module generated by (x, x), x in M, and (y, 0), y in N,
  # the rows whose first component vanishes project onto M intersect N.
  P1 = hcat(PM, deepcopy(PM))
  Z = pseudo_matrix(ring(M),
                    zero_matrix(overring(M), nrows(PN), ncols(PN)),
                    deepcopy(coefficient_ideals(PN)))
  P2 = hcat(PN, Z)
  H = pseudo_hnf(vcat(P1, P2), :upperright)
  r = nrows(PM)
  n = ncols(PM)
  P = sub(H, r + 1:r + nrows(PN), n + 1:2*n)
  return embedded_module(ring(M), overring(M), P; overstructure = overstructure(M))
end

function intersect(M::EmbeddedModule, N::EmbeddedModule)
  _check_compatible(M, N)
  return _intersect(M, N, _ring_type(M))
end

################################################################################
#
#  Containment(?)
#
################################################################################

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
  return _contained_in_span_of_pseudohnf(a, id, MB; shape = :lowerleft)
end

function _in(a::MatrixElem, M::EmbeddedModule{_DD})
  return _contained_in_span_of_pseudohnf(a, basis_matrix(M); shape = :lowerleft)
end

function _in(N::PMat, M::EmbeddedModule{_DD})
  return _spans_subset_of_pseudohnf(N, basis_matrix(M); shape = :lowerleft)
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

################################################################################
#
#  Subset
#
################################################################################

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
  return hash(coefficient_ideals(P), hash(matrix(P), h))
end

function Base.hash(M::EmbeddedModule, h::UInt)
  h = hash(ring(M), h)
  h = hash(overring(M), h)
  h = hash(overstructure(M), h)
  return _embedded_module_hash(M, h)
end

################################################################################
#
#  Index
#
################################################################################

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

################################################################################
#
#  Quotient
#
################################################################################

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
  QQ, MapFromFunc(M, QQ, x -> QQ(RtoF.(Generic._matrix(preimage(StoQ, MtoQ(x))))), y -> preimage(MtoQ, StoQ(S(preimage.(RtoF, Generic._matrix(y)))))), RtoF
end
