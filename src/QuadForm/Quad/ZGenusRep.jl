###############################################################################
#
#  General interface for enumeration of genera for definite ZZLat
#
###############################################################################

###############################################################################
#
#  Neighbours
#
###############################################################################

function neighbour(L::ZZLat, v::ZZMatrix, p::ZZRingElem)
  M = gram_matrix(L)*v
  K = kernel(matrix(GF(p), rank(L), 1, collect(M)))
  _B = map_entries(a -> lift(ZZ, a), K)
  LL = lattice_in_same_ambient_space(L, _B*basis_matrix(L)) + lattice_in_same_ambient_space(L, 1//p*(transpose(v)*basis_matrix(L))) + p*L
  return LL
end

function make_admissible!(w::ZZMatrix, form::ZZMatrix, p::ZZRingElem, K::FinField)
  m = only(transpose(w)*form*w)
  _a = mod(m, p^2)
  iszero(_a) && return nothing
  a = K(div(_a, p))
  v = 2*form*w
  vK = map_entries(b -> K(b)//a, v)
  vK = reduce(vcat, dense_matrix_type(K)[identity_matrix(K, 1), vK])
  L = kernel(vK)
  @hassert :GenRep 3 !iszero(view(L, :, 1))
  j = findfirst(j -> !iszero(L[j, 1]), 1:nrows(L))
  @hassert :GenRep 3 !isnothing(j)
  L = map_entries(b -> b//L[j, 1], L)
  v = ZZRingElem[lift(ZZ, a) for a in L[j, 2:ncols(L)]]
  for i in 1:nrows(w)
    w[i, 1] += p*v[i]
  end
  @hassert :GenRep 3 iszero(mod(transpose(w)*form*w, p^2))
  return nothing
end

################################################################################
#
#  Algorithms
#
################################################################################

#TODO: implement an algorithm selection after the benchmarking
function _choose_algorithm(G::ZZGenus)
  if rank(G) > 9
    return :random
  end
  return :orbit
end

_choose_algorithm(L::ZZLat) = _choose_algorithm(genus(L))

function _neighbours_definite_orbit(L::ZZLat, p::ZZRingElem; callback::Function,
                                                             inv_dict::Dict,
                                                             _invariants::Function,
                                                             save_partial::Bool = false,
                                                             save_path::Union{Nothing, String} = nothing,
                                                             use_mass::Bool = true,
                                                             missing_mass::Union{Nothing, Base.RefValue{QQFieldElem}} = nothing,
                                                             vain::Base.RefValue{Int} = Ref{Int}(0),
                                                             stop_after::IntExt = inf,
                                                             max::IntExt = inf)
  @assert !save_partial || !isnothing(save_path)
  K = GF(p)
  form = map_entries(ZZ, gram_matrix(L))
  B = basis_matrix(L)
  Tp = torsion_quadratic_module(L, p*L)
  _, jp = radical_bilinear(Tp)

  if use_mass
    __mass = missing_mass[]
  end

  G = automorphism_group_generators(L)
  _gensp = ZZMatrix[matrix(hom(Tp, Tp, TorQuadModuleElem[Tp(lift(a)*g) for a in gens(Tp)])) for g in G]
  gensp = dense_matrix_type(K)[map_entries(K, g) for g in G]
  filter!(!is_diagonal, gensp)
  LO = Vector{elem_type(K)}[orb[1] for orb in line_orbits(gensp)]

  result = typeof(L)[]

  @vprintln :GenRep 3 "$(length(LO)) orbits of lines to try"

  for x in LO
    vain[] > stop_after && break
    w = ZZRingElem[lift(ZZ, k) for k in x]
    a = Tp(abelian_group(Tp)(w))
    if !iszero(quadratic_product(a))
      vain[] += 1
      continue
    end
    if has_preimage(jp, a)[1]
      vain[] += 1
      continue
    end

    w = matrix(ZZ, length(w), 1, w)
    make_admissible!(w, form, p, K)
    LL = lll(neighbour(L, w, p))

    @hassert :GenRep 3 is_locally_isometric(LL, L, p)

    keep = callback(LL)
    if !keep
      vain[] += 1
      continue
    end

    vain[] = Int(0)
    @vprintln :GenRep 3 "Keep an isometry class"
    invLL = _invariants(LL)
    if haskey(inv_dict, invLL)
      push!(inv_dict[invLL], LL)
    else
      inv_dict[invLL] = ZZLat[LL]
    end
    push!(result, LL)
    if save_partial
      save_partial_lattice(LL, save_path)
    end
    if use_mass
      s = automorphism_group_order(LL)
      sub!(__mass, __mass, 1//s)
      is_zero(__mass) && return result
    end
    length(result) == max && break
  end
  return result
end

function _neighbours_definite_rand(L::ZZLat, p::ZZRingElem; rand_neigh::Union{Nothing, Int} = nothing,
                                                            callback::Function,
                                                            inv_dict::Dict,
                                                            _invariants::Function,
                                                            save_partial::Bool = false,
                                                            save_path::Union{Nothing, String} = nothing,
                                                            use_mass::Bool = true,
                                                            missing_mass::Union{Nothing, Base.RefValue{QQFieldElem}} = nothing,
                                                            vain::Base.RefValue{Int} = Ref{Int}(0),
                                                            stop_after::IntExt = inf,
                                                            max::IntExt=inf)
  @assert !save_partial || !isnothing(save_path)
  K = GF(p)
  form = map_entries(ZZ, gram_matrix(L))
  Tp = torsion_quadratic_module(L, p*L)
  _, jp = radical_bilinear(Tp)

  if use_mass
    __mass = missing_mass[]
  end

  P = enumerate_lines(K, rank(L))

  result = typeof(L)[]

  maxlines = isnothing(rand_neigh) ? min(100, length(P)) : min(rand_neigh, length(P))

  @vprintln :GenRep 3 "Try $(maxlines) random lines"

  for i in 1:maxlines
    vain[] > stop_after && break
    w = ZZRingElem[lift(ZZ, k) for k in rand(P)]
    a = Tp(abelian_group(Tp)(w))
    if !iszero(quadratic_product(a))
      vain[] += 1
      continue
    end
    if has_preimage(jp, a)[1]
      vain[] += 1
      continue
    end

    w = matrix(ZZ, length(w), 1, w)
    make_admissible!(w, form, p, K)
    LL = lll(neighbour(L, w, p))
    @hassert :GenRep 3 is_locally_isometric(LL, L, p)

    keep = callback(LL)
    if !keep
      vain[] += 1
      continue
    end
    vain[] = Int(0)

    @vprintln :GenRep 3 "Keep an isometry class"
    invLL = _invariants(LL)
    if haskey(inv_dict, invLL)
      push!(inv_dict[invLL], LL)
    else
      inv_dict[invLL] = ZZLat[LL]
    end
    push!(result, LL)
    if save_partial
      save_partial_lattice(LL, save_path)
    end
    if use_mass
      s = automorphism_group_order(LL)
      sub!(__mass, __mass, 1//s)
      is_zero(__mass) && return result
    end
    length(result) == max && break
  end
  return result
end

###############################################################################
#
#  Invariants
#
###############################################################################

function _unique_iso_class!(L::Vector{ZZLat})
  isempty(A) && return A
  idxs = eachindex(A)
  y = first(A)
  T = NTuple{2, Any}
  it = iterate(idxs, (iterate(idxs)::T)[2])
  count = 1
  for x in Iterators.drop(A, 1)
    if !is_isometric(x, y)
      it = it::T
      y = A[it[1]] = x
      count += 1
      it = iterate(idxs, it[2])
    end
  end
  resize!(A, count)::typeof(A)
end

# Could complement with other invariants at some point if we want
function default_func(L::ZZLat)
  m = minimum(L)
  rlr = root_lattice_recognition(L)
  kn = kissing_number(L)::Int
  igo = automorphism_group_order(L)::ZZRingElem
  return (m, rlr, kn, igo)
end

###############################################################################
#
#  User interface
#
###############################################################################

#======
Input:
- known -> finite list of known isometry classes (always non-empty by starting from a single lattice)
- alg_type -> how to enumerate neighbours: all of them (:exhaustive), orbits of them (:orbit), a random number (:random)
Optional:
- rand_neigh -> for random enumeration, how many randome neighbours are computed
- distinct -> if the lattices in "known" are known to be pairwise non-isometric
- invariant_func -> functions to compute isometry invariants for comparing lattices
- save_partial -> whether one wants to save iteratively new isometry classes (for instance for large genera)
- save_path -> in the case "save_partial" is true, where to save the lattices
- use_mass -> whether to use the mass formula as termination condition
- missing_mass -> if "use_mass" and "distinct" are true, and the partial mass of "known" is known, mention what is the part of the mass missing
- vain -> count the number of vain iterations without finding a new lattice in the given spinor genus
- stop_after -> the algorithm breaks if we have done that amount of iterations without finding a new lattice
- max -> maximum number of lattices to be found
======#

function enumerate_definite_genus(
    known::Vector{ZZLat},
    algorithm::Symbol = _choose_algorithm(known[1]);
    rand_neigh::Union{Int, Nothing} = nothing,
    distinct::Bool = true,
    invariant_func::Function = default_func,
    save_partial::Bool = false,
    save_path::Union{String, Nothing} = nothing,
    use_mass::Bool = true,
    _missing_mass::Union{QQFieldElem, Nothing} = nothing,
    vain::Base.RefValue{Int} = Ref{Int}(0),
    stop_after::IntExt = inf,
    max::IntExt = inf
  )
  @req !save_partial || !isnothing(save_path) "No path mentioned for saving partial results"
  @req !is_empty(known) "Should know at least one lattice in the genus"
  @req all(LL -> genus(LL) == genus(known[1]), known) "Known lattices must be in the same genus"
  @req algorithm == :orbit || algorithm == :random "Only :random and :orbit algorithms are currently implemented"
  @req !is_finite(max) || max > 0 "max must be infinite or positive"

  res = copy(known)
  !distinct && _unique_iso_class!(res)

  L, itk = Iterators.peel(res)
  inv_lat = invariant_func(L)
  inv_dict = Dict{typeof(inv_lat), Vector{ZZLat}}(inv_lat => ZZLat[L])
  for N in itk
    inv_lat = invariant_func(N)
    if haskey(inv_dict, inv_lat)
      push!(inv_dict[inv_lat], N)
    else
      inv_dict[inv_lat] = ZZLat[N]
    end
  end

  function _invariants(M::ZZLat)
    for (I, Z) in keys(inv_dict)
      M in Z && return I
    end
    return invariant_func(M)
  end

  callback = function(M::ZZLat)
    any(isequal(M), known) && return false
    invM = _invariants(M)
    !haskey(inv_dict, invM) && return true
    keep = all(N -> !is_isometric(N, M), inv_dict[invM])
    return keep
  end

  if use_mass
    _mass = mass(L)
    if isnothing(_missing_mass)
      found = sum(1//automorphism_group_order(M) for M in res; init=QQ(0))
      missing_mass = Ref{QQFieldElem}(_mass-found)
    else
      @hassert :GenRep 3 _missing_mass <= _mass
      missing_mass = Ref{QQFieldElem}(_missing_mass)
    end
  end

  ps = primes(genus(L))
  p = ZZ(3)
  while p in ps
    p = next_prime(p)
  end

  tbv = trues(length(res))
  while any(tbv)
    i = findfirst(tbv)
    tbv[i] = false
    if algorithm == :orbit
      N = _neighbours_definite_orbit(res[i], p; callback, inv_dict, _invariants, use_mass, missing_mass, save_partial, save_path, vain, stop_after, max)
    elseif algorithm == :random
      N = _neighbours_definite_rand(res[i], p; rand_neigh, callback, inv_dict, _invariants, use_mass, missing_mass, save_partial, save_path, vain, stop_after, max)
    end
    
    if !is_empty(N)
      for M in N
        push!(tbv, true)
        push!(res, M)
        if length(M) >= max
          return res, use_mass ? missing_mass[] : zero(QQ)
        end
      end
      use_mass && is_zero(missing_mass[]) && break
      if use_mass
        @v_do :GenRep 1 perc = Float64(missing_mass[]//_mass) * 100
        @vprintln :GenRep 1 "Lattices: $(length(res)), Target mass: $(_mass). missing: $(missing_mass[]) ($(perc)%)"
      else
        @vprintln :GenRep 1 "Lattices: $(length(res))"
      end
    elseif vain[] > stop_after
      break
    end
  end
  return res, use_mass ? missing_mass[] : zero(QQ)
end

function enumerate_definite_genus(
    L::ZZLat,
    algorithm::Symbol = _choose_algorithm(L);
    rand_neigh::Union{Int, Nothing} = nothing,
    invariant_func::Function = default_func,
    save_partial::Bool = false,
    save_path::Union{IO, String, Nothing} = nothing,
    use_mass::Bool = true,
    stop_after::IntExt = inf,
    max::IntExt = inf
  )
  @req !save_partial || !isnothing(save_path) "No path mentioned for saving partial results"

  edg = ZZLat[]
  LL = _to_number_field_lattice(L)
  p = _smallest_norm_good_prime(LL)
  spinor_genera = ZZLat[_to_ZLat(N; K=QQ) for N in spinor_genera_in_genus(LL, typeof(p)[p])]
  @vprintln :GenRep 1 "$(length(spinor_genera)) spinor genera to enumerate"

  for M in spinor_genera
    vain = Ref{Int}(0)
    if use_mass
      _missing_mass = mass(M)//length(spinor_genera)
      s = automorphism_group_order(M)
      sub!(_missing_mass, _missing_mass, 1//s)
      if is_zero(_missing_mass)
        push!(edg, M)
        continue
      end
    end
    _edg, mm = enumerate_definite_genus(ZZLat[M], algorithm; rand_neigh,
                                                             invariant_func,
                                                             save_partial,
                                                             save_path,
                                                             use_mass,
                                                             _missing_mass,
                                                             vain,
                                                             stop_after,
                                                             max=max-length(edg))

    while (use_mass && !is_zero(mm)) || (vain[] < stop_after)
      vain[] >= stop_after && break
      (length(edg) + length(_edg)) >= max && break
      _edg, mm = enumerate_definite_genus(_edg, algorithm; distinct=true,
                                                           rand_neigh,
                                                           invariant_func,
                                                           save_partial,
                                                           save_path,
                                                           use_mass,
                                                           _missing_mass = mm,
                                                           stop_after,
                                                           max=max-length(edg)-length(_edg))
    end
    append!(edg, _edg)
  end
  return edg
end

function enumerate_definite_genus(
    G::ZZGenus,
    algorithm::Symbol = _choose_algorithm(G);
    rand_neigh::Union{Int, Nothing} = nothing,
    invariant_func::Function = default_func,
    save_partial::Bool = false,
    save_path::Union{IO, String, Nothing} = nothing,
    use_mass::Bool = true,
    stop_after::IntExt = inf,
    max::IntExt = inf
  )
  L = representative(G)
  max == 1 && return ZZLat[L]
  return enumerate_definite_genus(L, algorithm; rand_neigh,
                                                invariant_func,
                                                save_partial,
                                                save_path,
                                                use_mass,
                                                stop_after,
                                                max)
end

###############################################################################
#
#  Compact serialization
#
###############################################################################

# Should only consist of integers
function _get_half_gram(L::ZZLat)
  M = gram_matrix(L)
  str = "$(rank(L))\n["
  for i in 1:nrows(M), j in i:ncols(M)
    str *= "$(M[i,j]),"
  end
  str = str[1:end-1]*"]"
  return str
end

function _gram_from_list(V::Vector{QQFieldElem}, n::Int)
  M = zero_matrix(QQ, n, n)
  k = 0
  for i in 1:n
    for j in i:n
      k += 1
      M[i, j] = M[j, i] = V[k]
    end
  end
  return integer_lattice(; gram = M)
end

# We consider f as the relative path to a directory where
# each file is an object, stored as a list of integers
function load_genus(f::String)
  gg = ZZLat[]
  files = readdir(f; join=true)
  for file in files
    _n, _V = readlines(files)
    n = Base.parse(Int, _n)
    _, V = _parse(Vector{QQFieldElem}, IOBuffer(_V))
    push!(gg, _gram_from_list(V, n))
  end
  return gg
end

function save_partial_lattice(L::ZZLat, f::String)
  n = length(readdir(f))
  _f = open(f*"/lat_$(n+1).jl", "w")
  write(_f, _get_half_gram(L))
  close(_f)
  return nothing
end
