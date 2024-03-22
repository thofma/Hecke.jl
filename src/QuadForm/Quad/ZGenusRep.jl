###############################################################################
#
#  General interface for enumeration of genera for definite ZZLat
#  ==============================================================
#  References:
#    - [Kne57] M. Kneser "Klassenzahlen definiter quadratischer Formen", 1957;
#    - [SP91] R. Schulze-Pillot "An algorithm for computing genera of ternary
#                                and quaternary quadratic forms", 1991;
#
###############################################################################

add_verbosity_scope(:ZGenRep)
add_assertion_scope(:ZGenRep)

###############################################################################
#
#  Neighbours
#
###############################################################################

@doc raw"""
    prime_dual(L::ZZLat, v::ZZMatrix, p::ZZRingElem) -> ZZLat

Return the sublattice of `(L, b)` consisting of vectors `w` such that `b(v, w)`
is divisible by `p`.

Input:
  - An integral integer lattice `(L, b)`;
  - A prime number `p` not dividing `det(L, b)`;
  - A vector `v` of `L` not lying in `p*L`.

Output:
  - The sublattice `L_{v, p} := {w in L: b(v, w) in p*ZZ}` of `L`.
"""
function prime_dual(L::ZZLat, v::QQMatrix, p::ZZRingElem)
  M = gram_matrix(L)*transpose(v)
  K = kernel(map_entries(GF(p), M))
  M = matrix(QQ, nrows(K), ncols(K), ZZRingElem[lift(ZZ, k) for k in K])
  return lattice_in_same_ambient_space(L, M*basis_matrix(L)) + p*L
end

@doc raw"""
    neighbour(L::ZZLat, v::ZZMatrix, p::ZZRingElem) -> ZZLat

Return the `p`-neighbour of `L` associated to the admissible vector `v`.

Input:
  - An integer lattice `(L, b)`;
  - A prime number `p` which does not divide `det(L)`;
  - A vector `v` of `L` not lying in `p*L` such that `b(v, v)` is divisible
    by `p^2`.

Output:
  - The `p`-neighbour of `L` defined as `L_{v, p} + 1//p*v` where
    `L_{v, p} := {w in L: b(v, w) in p*ZZ}`.
"""
function neighbour(L::ZZLat, v::QQMatrix, p::ZZRingElem)
  Lvp = prime_dual(L, v, p)
  LL = Lvp + lattice_in_same_ambient_space(L, 1//p*(v*basis_matrix(L)))
  return LL
end

@doc raw"""
    make_admissible!(w::ZZMatrix, form::ZZMatrix, m::ZZRingElem, K::FinField) -> Nothing

Return a vector `v` congruent to `w` modulo `p*L0` whose square with respect to
`form` is divisible by `m`, where `L0` is a lattice with Gram matrix `form`.

Input:
  - A prime field `K` of characteristic `p`;
  - A symmetric integer matrix `form` of full rank representing the quadratic
    form on the even sublattice `(L0, b)` of an integer lattice `(L, b)`;
  - An integer `m`;
  - A vector `w` in `L0` not lying in `p*L0` such that:
    * `b(w, w)` is divisible by `2*p` if `(L, b)` is even or `p == 2`; by `p` otherwise;
    * if `p == 2` and the prime dual lattice `L_{w, 2}` is equal to `(L0, b)`,
      then `b(w, w)` is divisible by `m`.

Output:
  - A vector `v` congruent to `w` modulo `p*L0` such that `b(v, v)` is divisible
    by `m`.

The existence of `v` is ensured by the conditions on `w`
(see [SP91, Chapter 1, conditions (i) & (vii)])
"""
function make_admissible!(w::QQMatrix, form::QQMatrix, m::ZZRingElem, K::FinField, _a::ZZRingElem)
  p = characteristic(K)
  # If p == 2, `form` is actually the Gram matrix of the maximal even sublattice
  # of the original lattice we started with. Otherwise, `form` is the Gram
  # matrix of the original lattice.
  #
  # If the original lattice was even, `m = 2*p^2`, otherwise `m = p^2`.
  #
  # In the case where `p == 2`, [SP91] ensures existence of an admissible
  # vector `v` only if the prime dual lattice `L_{w, p}` is not equal to the even
  # lattice `form`. Otherwise, `w` should already be admissible.
  #
  # For `p = 2`, if the original lattice was odd, then `m = 4` and `w` in input has
  # always square divisible by `4` (could be also divisible by `8` when `L_{w, 2}`
  # and `form` are distinct). So in particular, the rest of the function in the
  # case `p == 2` is only triggered when the original lattice was even, and
  # thus `m = 8`.

  # In the case where `p` is odd, we can find a good vector `v` by solving the
  # linear system `x+2*y*b(w, v) == 0 mod p` in `(x, y)`. We can solve it because
  # `p` was chosen not to divide the determinant of `form`.
  #
  # If `p == 2`, since the prime dual `L_{w, 2}` and `form` are distinct, and
  # moreover `b(w, w)` is disivible by 4 but not by 8, there exists `v'` such
  # that `b(w, v')` is odd, and the vector `v := w + 2v'` has square divisible
  # by 8. We can find such `v'` by solving `x+y*b(w, v') == 0 mod 2` in `(x, y)`.
  if p != 2
    a = K(div(_a, p))
    v = 2*form*transpose(w)
    vK = map_entries(b -> K(b)//a, v)
  else
    v = form*transpose(w)
    vK = map_entries(K, v)
  end
  vK = reduce(vcat, dense_matrix_type(K)[identity_matrix(K, 1), vK])
  L = kernel(vK)
  @hassert :ZGenRep 3 !iszero(view(L, :, 1))
  j = findfirst(j -> !iszero(L[j, 1]), 1:nrows(L))
  @hassert :ZGenRep 3 !isnothing(j)
  L = map_entries(b -> b//L[j, 1], L)
  v = ZZRingElem[lift(ZZ, a) for a in L[j, 2:ncols(L)]]
  for i in 1:ncols(w)
    w[1, i] += p*v[i]
  end
  @hassert :ZGenRep 3 iszero(mod(only(w*form*transpose(w)), m))
  return nothing
end

################################################################################
#
#  Algorithms
#
################################################################################

# Since L is integral, for two vectors v,w in L, if both have odd
# square, then b(v-w, v-w) = q(v)+q(w)-b(v,w) is even and w+L0 = v+L0.
@doc raw"""
    even_sublattice(L::ZZLat) -> ZZLat

Given an integral $\mathbb{Z}$-lattice `L`, return the even sublattice $L_0$ of
`L`.

The lattice $L_0$ consists of vectors $v\in L$ such that $v^2\in 2\mathbb{Z}$.
If `L` is already even, then $L_0 = L$, otherwise $[L:L_0] = 2$.
"""
function even_sublattice(L::ZZLat)
  is_even(L) && return L
  TT = normal_form(torsion_quadratic_module(L, 2*L; modulus_qf=QQ(2)))[1]
  l = ngens(TT)
  if is_even(l)
    gensT2 = push!(gens(TT)[1:end-2], TT[l-1]+TT[l])
  else
    gensT2 = gens(TT)[1:l-1]
  end
  T2 = sub(TT, gensT2)[1]
  L0 = cover(T2)
  @hassert :ZGenRep 1 index(L, L0) == 2
  return L0
end

# Neighbour algorithm using orbits of lines in finite dimensional vector spaces
# over prime field
#
# - L is the lattice from which we compute neighbours;
# - `p` is a good prime: `p` does not divides `det(L)`, `L_p` is isotropic and
#   we chose `p` to be the smallest prime satisfying these two properties;
# - `callback` is a function to compare new neighbours with lattices already
#   collected in the outer scope;
# - `inv_dict` is a dictionary of invariants to make `callback` faster;
# - `_invariants` is the function that computes the invariants of any
#   new neighbour, and store them in `inv_dict`;
# - `save_partial` tells us whether to save partial results on the machine;
# - `save_path` is a path where to store the lattice in case `save_partial` is
#   `true`.
# - `use_mass` tells whether to use the mass of the genus of `L` for the
#   termination of the algorithm;
# - `missing_mass` tells us what proportion of the mass has not been computed
#   yet in the outer scope;
# - `vain` refers to the number of vain iteration, i.e. how many new neighbours
#   did not give rise to a non-explored isometry class in the neighbour graph;
# - `stop_after` tells after how many vain iterations the algorithm should
#   stop;
# - if `max` is not infinity, then the function stops as soon as we have
#   representatives for `max` isometry classes in the genus of `L`, in the
#   outer scope.
function _neighbours_definite_orbit(L::ZZLat, p::ZZRingElem; callback::Function,
                                                             inv_dict::Dict,
                                                             _invariants::Function,
                                                             save_partial::Bool = false,
                                                             save_path::Union{Nothing, String} = nothing,
                                                             use_mass::Bool = true,
                                                             missing_mass::Base.RefValue{QQFieldElem},
                                                             vain::Base.RefValue{Int} = Ref{Int}(0),
                                                             stop_after::IntExt = inf,
                                                             max::IntExt = inf)
  @assert !save_partial || !isnothing(save_path)
  even = is_even(L)
  K = GF(p)

  # A vector in `L\p*L` is called admissible if it gives rise to a neighbour
  # of `L` which is in the genus of `L`.
  #
  # If `p` is odd, the admissible vectors `w` in `L\p*L` are such that `w^2`
  # is divisible by `p^2` (and thus `2*p^2` in the case where `L` is even).
  # Such an admissible vector exists if and only if there exists a vector `w` in
  # `L\p*L` whose square is divisible by `p`. One can make such a `w` admissible
  # by adding to it a suitable vector from `p*L`.
  #
  # In the case where `p == 2`, by [SP91, Chapter 1, condition (v)], all
  # admissible vectors `w` in `L\2*L` are such that:
  # - `w^2` is disivible by `8` if `L` is even, or
  # - `w^2` is divisible by 4 if `L` odd, with `w^2` divisible by 8 only if the
  #   prime dual lattice `L_{w, 2}` is not equal to `L0`, the maximal even
  #   sublattice of `L`.
  # Such an admissible vector exists if and only if there exists a vector `w` in
  # `L0\2*L0` whose square is divisible by 4 and either `w` is already admissible,
  # or `L_{w, 2}` must be different from `L0`. In the latter case, one can make
  # `w` admissible by adding to it a suitable vector from `2*L0`.
  flag = (p == 2 && !even)
  if flag
    L0 = even_sublattice(L)
    L0toL = solve(basis_matrix(L), basis_matrix(L0)) # To change the coordinates of vectors in L0
    LtoL0 = inv(L0toL)
  else
    L0 = L
  end
  form0 = gram_matrix(L0)

  # As stated before, to look for admissible vectors, we need to start by
  # finding lines in `L/p*L` for which the square of a representative is
  # divisible by `mqf`.
  #
  # A vector will be admissible if its square is divisible by `m`.
  if even
    mqf = 2*p
    m = 2*p^2
  else
    mqf = p == 2 ? 4 : p
    m = p^2
  end

  # Note that since we chose `p` not to divide `det(L)`, we have that for all
  # `w` in `L\p*L`, the lattice `L_{w, p}` is different from `L`. In particular,
  # if `w^2` is divisible by `mqf`, the line `[w]` in `Tp` is (regular) isotropic.
  if use_mass
    __mass = missing_mass[]
  end

  # For the orbit algorithm, we identify isotropic lines in `L0/p*L0` which are in
  # the same `O(L)`-orbit (because they give rise to isometric `p`-neighbours of
  # `L`).
  G = automorphism_group_generators(L; ambient_representation=false)
  if flag
    gensp = dense_matrix_type(K)[map_entries(K, L0toL*g*LtoL0) for g in G]
  else
    gensp = dense_matrix_type(K)[map_entries(K, g) for g in G]
  end
  any(isone, gensp) || push!(gensp, identity_matrix(K, rank(L))) # To avoid empty lists for `line_orbits`
  filter!(m -> isone(m) || !is_diagonal(m), gensp)
  orbs = Vector{elem_type(K)}[orb[1] for orb in line_orbits(gensp)] # Hopefully we took care prior to this that `line_orbits`
                                                                    # terminates and do not blow the memory up...

  result = typeof(L)[]

  @vprintln :ZGenRep 3 "$(length(orbs)) orbits of lines to try"

  for x in orbs
    vain[] > stop_after && break
    w = matrix(QQ, 1, rank(L0), ZZRingElem[lift(ZZ, k) for k in x])
    a = numerator(only(w*form0*transpose(w)))
    if !is_divisible_by(a, mqf)
      vain[] += 1
      continue
    end

    lifts = typeof(w)[]
    if p == 2
      bo = is_divisible_by(a, 8)
      if even && !bo # Corner case: `w` is admissible if `bo`; if not, we can make it admissible only if `L_{w, 2} != L0`
        if prime_dual(L, w, p) != L0
          vain[] += 1
          continue
        end
        make_admissible!(w, form0, m, K, a)
        push!(lifts, w)
      elseif even && bo # `w` is admissible so it is good
        push!(lifts, w)
      elseif !even && bo # Another corner case: `w` is admissible but if `L_{w, 2} == L0` then the neighbour is even, and we want an odd one
        if prime_dual(L, w*L0toL, p) != L0
          vain[] += 1
          continue
        end
        push!(lifts, w*L0toL)
      else
        # Here `w` is admissible of square 4 mod 8 so w/2 has odd square. Hence
        # `L_{w, 2} == L0` is allowed.
        #
        # If `L0_{w, 2} != L0`, we could allow another vector congruent to `w`
        # modulo 2*L0 with square divisible by 8. It is going to be another
        # admissible vector, and the neighbour might not be isometric to the one
        # obtained via `w`. The existence of such vectors is ensured only if
        # there exists a vector in `L0` with odd product with `w`, i.e. if
        # `L0_{w, 2} != L0` (which itself implies that `L_{w, 2} != L0`)
        if prime_dual(L0, w, p) == L0
          push!(lifts, w*L0toL)
        else
          push!(lifts, w*L0toL)
          make_admissible!(w, form0, ZZ(8), K, a)
          push!(lifts, w*L0toL)
        end
      end
    else
      !is_divisible_by(a, m) && make_admissible!(w, form0, m, K, a)
      w = flag ? w*L0toL : w # Now that `w` is admissible, we map it back to `L`
      push!(lifts, w)
    end

    for v in lifts
      LL = lll(neighbour(L, v, p))
      @hassert :ZGenRep 3 is_locally_isometric(LL, L, p) # Should always hold by the neighbour construction

      keep = callback(LL)
      if !keep
        vain[] += 1
        continue
      end

      vain[] = Int(0)
      @vprintln :ZGenRep 3 "Keep an isometry class"
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
  end
  return result
end

# Comments and details about the process in the code are in the previous
# function.
#
# - rand_neigh -> how many random neighbours are computed at each iteration;
function _neighbours_definite_rand(L::ZZLat, p::ZZRingElem; rand_neigh::Int = 10,
                                                            callback::Function,
                                                            inv_dict::Dict,
                                                            _invariants::Function,
                                                            save_partial::Bool = false,
                                                            save_path::Union{Nothing, String} = nothing,
                                                            use_mass::Bool = true,
                                                            missing_mass::Base.RefValue{QQFieldElem},
                                                            vain::Base.RefValue{Int} = Ref{Int}(0),
                                                            stop_after::IntExt = inf,
                                                            max::IntExt=inf)
  @assert !save_partial || !isnothing(save_path)
  even = is_even(L)
  K = GF(p)

  flag = (p == 2 && !even)
  if flag
    L0 = even_sublattice(L)
    L0toL = solve(basis_matrix(L), basis_matrix(L0))
  else
    L0 = L
  end
  form0 = gram_matrix(L0)

  if even
    mqf = 2*p
    m = 2*p^2
  else
    mqf = p == 2 ? 4 : p
    m = p^2
  end

  if use_mass
    __mass = missing_mass[]
  end

  # For the random algorithm, we create an iterator on the set of lines
  # in `K^{rank(L)}`, and we then test a random sample of lines. By default,
  # we test at most 10 lines, but the user can choose to change this parameter.
  P = enumerate_lines(K, rank(L))

  maxlines = min(rand_neigh, length(P))

  result = typeof(L)[]

  @vprintln :ZGenRep 3 "Try $(maxlines) random lines"

  for i in 1:maxlines
    vain[] > stop_after && break
    w = matrix(QQ, 1, rank(L), ZZRingElem[lift(ZZ, k) for k in rand(P)])
    a = numerator(only(w*form0*transpose(w)))
    if !is_divisible_by(a, mqf)
      vain[] += 1
      continue
    end

    lifts = typeof(w)[]
    if p == 2
      bo = is_divisible_by(a, 8)
      if even && !bo
        if prime_dual(L, w, p) != L0
          vain[] += 1
          continue
        end
        make_admissible!(w, form0, m, K, a)
        push!(lifts, w)
      elseif even && bo
        push!(lifts, w)
      elseif !even && bo
        if prime_dual(L, w*L0toL, p) != L0
          vain[] += 1
          continue
        end
        push!(lifts, w*L0toL)
      else
        if prime_dual(L, w*L0toL, p) == L0
          push!(lifts, w*L0toL)
        elseif prime_dual(L0, w, p) == L0
          push!(lifts, w*L0toL)
        else
          push!(lifts, w*L0toL)
          make_admissible!(w, form0, ZZ(8), K, a)
          push!(lifts, w*L0toL)
        end
      end
    else
      !is_divisible_by(a, m) && make_admissible!(w, form0, m, K, a)
      w = flag ? w*L0toL : w
      push!(lifts, w)
    end

    for v in lifts
      LL = lll(neighbour(L, v, p))
      @hassert :ZGenRep 3 is_locally_isometric(LL, L, p)

      keep = callback(LL)
      if !keep
        vain[] += 1
        continue
      end

      vain[] = Int(0)
      @vprintln :ZGenRep 3 "Keep an isometry class"
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
  end
  return result
end

###############################################################################
#
#  Invariants
#
###############################################################################

# Resize `A` to only keep one representative for each isometry class
# represented by the lattices in `A`.
function _unique_iso_class!(A::Vector{ZZLat})
  isempty(A) && return A
  idxs = eachindex(A)
  T = NTuple{2, Any}
  it = iterate(idxs, (iterate(idxs)::T)[2])
  count = 1
  for x in Iterators.drop(A, 1)
    if all(y -> !is_isometric(x, y), A[1:count])
      A[it[1]] = x
      count += 1
      it = iterate(idxs, it[2])
    end
  end
  resize!(A, count)::typeof(A)
end

# Could complement with other invariants at some point if we want.
# We use it to compute invariants of lattices in order to make
# comparison faster (two lattices with distinct invariants cannot
# be isometric). In such a way, `is_isometric` is triggered at the last
# moment (since it can be expensive).
function default_func(L::ZZLat)
  m = minimum(L)
  rlr, _ = root_lattice_recognition(L)
  kn = kissing_number(L)::Int
  ago = automorphism_group_order(L)::ZZRingElem
  return (m, rlr, kn, ago)
end

###############################################################################
#
#  User interface
#
###############################################################################

#======
Input:
- known -> finite list of known isometry classes (always non-empty by starting
           from a single lattice);
- algorithm -> how to enumerate neighbours: using orbits of lines (:orbit) or
               doing a random search (:random);

Optional:
- rand_neigh -> for random enumeration, how many random neighbours are computed
                at each iteration;
- distinct -> if the lattices in "known" are known to be pairwise non-isometric;
- invariant_func -> functions to compute isometry invariants for comparing
                    lattices;
- save_partial -> whether one wants to save iteratively new isometry classes
                  (for instance for large genera);
- save_path -> in the case "save_partial" is true, where to save the lattices;
- use_mass -> whether to use the mass formula as termination condition;
- missing_mass -> if "use_mass" and "distinct" are true, and the partial mass of
                  "known" is known, mention what is the part of the mass missing;
- vain -> count the number of vain iterations without finding a new lattice in
          the given spinor genus;
- stop_after -> the algorithm stops if we have done that amount of iterations
                without finding a new isometry class;
- max -> maximum number of lattices to be found.
======#
@doc raw"""
    enumerate_definite_genus(known::Vector{ZZLat}, algorithm::Symbol = :default;
                                                   rand_neigh::Int = 10,
                                                   distinct::Bool = false,
                                                   invariant_func::Function = default_func,
                                                   save_partial::Bool = false,
                                                   save_path::String = nothing,
                                                   use_mass::Bool = true,
                                                   _missing_mass::QQFieldElem = nothing,
                                                   stop_after::IntExt = inf,
                                                   max::IntExt = inf)
                                                                   -> Vector{ZZLat}, QQFieldElem

Given a non-empty list `known` of definite integral lattices which are in the
same (spinor) genus, compute new representatives of isometry classes of
lattices which are not represented by the lattices in `known` using Kneser's
neighbour algorithm. The output consists of a copy of `known` together with new
lattices (if any found), and a rational number which corresponds to the portion of
the mass of the (spinor) genus which is missing.

The second argument gives the choice to which algorithm to use for the enumeration.
We currently support two algorithms:
- `:random` which finds new isometry classes by constructing neighbours from random isotropic lines;
- `:orbit` which makes a smart search by classifying orbits of isotropic lines before constructing neighbours.
If `algorithm = :default`, the function chooses the most appropriate algorithm
depending on the rank and determinant of the genus to be enumerated.

The possible extra arguments are as follows:
- `rand_neigh` -> for random enumeration, how many random neighbours are computed at each iteration;
- `distinct` -> whether the lattices in `known` are known to be pairwise non-isometric;
- `invariant_func` -> a function to compute isometry invariants in order to check (faster) whether a new neighbour is already represented by a known isometry class;
- `save_partial` -> whether one wants to save iteratively new isometry classes (for instance for large genera);
- `save_path` -> a path to a folder where to save new lattices in the case where `save_partial` is true;
- `use_mass` -> whether to use the mass formula as termination condition;
- `missing_mass` -> if `use_mass` and `distinct` are true, and the partial mass of `known` is known, mention what is the part of the mass which is missing;
- `stop_after` -> the algorithm stops if we have done that amount of iterations without finding a new isometry class;
- `max` -> the algorithm stops after finding `max` new isometry classes.

If `distinct == false`, the function first compare all the lattices in `known`
to only keep one representative for each isometry class represented.

If `save_partial == true`, the lattices are stored in a compact way in a `.jl`
file. The storing only remembers the rank of a lattice and half of its Gram
matrix (which is enough to reconstruct the lattice as a standalone object).

The default function for `invariant_func` currently computes:
- the absolute length of a shortest vector in the given lattice (also known as [`minimum`](@ref));
- an ordered list of tuples consisting of the decomposition of the root sublattice of the given lattice (see [`root_lattice_recognition`](@ref));
- the kissing number of the given lattice, which is proportional to the number of vectors of shortest length;
- the order of the isometry group of the given lattice.
"""
function enumerate_definite_genus(
    known::Vector{ZZLat},
    algorithm::Symbol = :default;
    rand_neigh::Int = 10,
    distinct::Bool = false,
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
  if algorithm != :default
    @req algorithm == :orbit || algorithm == :random "Only :random and :orbit algorithms are currently implemented"
  end

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
    any(isequal(M), res) && return false
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
  else
    missing_mass = Ref{QQFieldElem}(0)
  end

  r = rank(L)
  d = abs(det(L))
  p = ZZ(2)
  while valuation(d, p) != 0 || !is_isotropic(L, p)
    p = next_prime(p)
  end

  if algorithm == :default
    # Seems to be a reasonable bound for now, less than 1,000,000 lines
    if ndigits(divexact(ZZ(p)^r-1, p-1)) < 7
      algorithm = :orbit
    else
      algorithm = :random
    end
  end

  i = Int(0)
  while i != length(res)
    i += 1
    if algorithm == :orbit
      N = _neighbours_definite_orbit(res[i], p; callback, inv_dict, _invariants, use_mass, missing_mass, save_partial, save_path, vain, stop_after, max)
    elseif algorithm == :random
      N = _neighbours_definite_rand(res[i], p; rand_neigh, callback, inv_dict, _invariants, use_mass, missing_mass, save_partial, save_path, vain, stop_after, max)
    end
    if !is_empty(N)
      for M in N
        push!(res, M)
        if length(res) >= max
          return res, missing_mass[]
        end
      end
      use_mass && is_zero(missing_mass[]) && break
      if use_mass
        @v_do :ZGenRep 1 perc = Float64(missing_mass[]//_mass) * 100
        @vprintln :ZGenRep 1 "Lattices: $(length(res)), Target mass: $(_mass). missing: $(missing_mass[]) ($(perc)%)"
      else
        @vprintln :ZGenRep 1 "Lattices: $(length(res))"
      end
    elseif vain[] > stop_after
      break
    end
  end
  return res, missing_mass[]
end

@doc raw"""
    enumerate_definite_genus(L::ZZLat, algorithm::Symbol = :default;
                                       rand_neigh::Int = 10,
                                       invariant_func::Function = default_func,
                                       save_partial::Bool = false,
                                       save_path::String = nothing,
                                       use_mass::Bool = true,
                                       stop_after::IntExt = inf,
                                       max::IntExt = inf)
                                                                   -> Vector{ZZLat}

Given a definite integral lattice `L`, compute representatives for the isometry
classes of lattices in the genus of `L` using Kneser's neighbour algorithm.

The second argument gives the choice to which algorithm to use for the enumeration.
We currently support two algorithms:
- `:random` which finds new isometry classes by constructing neighbours from random isotropic lines;
- `:orbit` which makes a smart search by classifying orbits of isotropic lines before constructing neighbours.
If `algorithm = :default`, the function choose the more appropriate algorithm
depending on the rank and determinant of the genus to be enumerated.

The possible extra arguments are as follows:
- `rand_neigh` -> for random enumeration, how many random neighbours are computed at each iteration;
- `invariant_func` -> a function to compute isometry invariants in order to check (faster) whether a new neighbour is already represented by a known isometry class;
- `save_partial` -> whether one wants to save iteratively new isometry classes (for instance for large genera);
- `save_path` -> a path to a folder where to save new lattices in the case where `save_partial` is true;
- `use_mass` -> whether to use the mass formula as termination condition;
- `stop_after` -> the algorithm stops if we have done that amount of iterations without finding a new isometry class;
- `max` -> the algorithm stops after finding `max` new isometry classes.

If `save_partial == true`, the lattices are stored in a compact way in a `.jl`
file. The storing only remembers the rank of a lattice and half its Gram
matrix (which is enough to reconstruct the lattice as a standalone object).

The default function for `invariant_func` currently computes:
- the absolute length of a shortest vector in the given lattice (also known as [`minimum`](@ref));
- an ordered list of tuples consisting of the decomposition of the root sublattice of the given lattice (see [`root_lattice_recognition`](@ref));
- the kissing number of the given lattice, which is proportional to the number of vectors of shortest length;
- the order of the isometry group of the given lattice.

Note: since we first compute a representative of an isometry class for each spinor
genus in the genus of `L`, the lattice `L` must have rank at least 3. For rank
1 and 2 lattices, please use the function [`genus_representatives`](@ref).
"""
function enumerate_definite_genus(
    L::ZZLat,
    algorithm::Symbol = :default;
    rand_neigh::Int = 10,
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
  @vprintln :ZGenRep 1 "$(length(spinor_genera)) spinor genera to enumerate"

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
    else
      @req 0 < stop_after < inf "Need to provide a finite positive value for stop_after if the mass is not used. Otherwise the algorithm may eventually never stops"
      _missing_mass = QQ(0)
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
    while vain[] <= stop_after && length(edg) + length(_edg) < max
      use_mass && is_zero(mm) && break
      _edg, mm = enumerate_definite_genus(_edg, algorithm; distinct=true,
                                                           rand_neigh,
                                                           invariant_func,
                                                           save_partial,
                                                           save_path,
                                                           use_mass,
                                                           _missing_mass=mm,
                                                           vain,
                                                           stop_after,
                                                           max=max-length(edg)-length(_edg))
    end
    append!(edg, _edg)
    length(edg) >= max && return edg
  end
  return edg
end

@doc raw"""
    enumerate_definite_genus(G::ZZGenus, algorithm::Symbol = :default;
                                         rand_neigh::Int = 10,
                                         invariant_func::Function = default_func,
                                         save_partial::Bool = false,
                                         save_path::String = nothing,
                                         use_mass::Bool = true,
                                         stop_after::IntExt = inf,
                                         max::IntExt = inf)
                                                                   -> Vector{ZZLat}

Given a genus `G` of definite integral lattices, compute representatives for the
isometry classes of lattices in `G` using Kneser's neighbour algorithm.

The second argument gives the choice to which algorithm to use for the enumeration.
We currently support two algorithms:
- `:random` which finds new isometry classes by constructing neighbours from random isotropic lines;
- `:orbit` which makes a smart search by classifying orbits of isotropic lines before constructing neighbours.
If `algorithm = :default`, the function choose the more appropriate algorithm
depending on the rank and determinant of the genus to be enumerated.

The possible extra arguments are as follows:
- `rand_neigh` -> for random enumeration, how many random neighbours are computed at each iteration;
- `invariant_func` -> a function to compute isometry invariants in order to check (faster) whether a new neighbour is already represented by a known isometry class;
- `save_partial` -> whether one wants to save iteratively new isometry classes (for instance for large genera);
- `save_path` -> a path to a folder where to save new lattices in the case where `save_partial` is true;
- `use_mass` -> whether to use the mass formula as termination condition;
- `stop_after` -> the algorithm stops if we have done that amount of iterations without finding a new isometry class;
- `max` -> the algorithm stops after finding `max` new isometry classes.

If `save_partial == true`, the lattices are stored in a compact way in a `.jl`
file. The storing only remembers the rank of a lattice and half its Gram
matrix (which is enough to reconstruct the lattice as a standalone object).

The default function for `invariant_func` currently computes:
- the absolute length of a shortest vector in the given lattice (also known as [`minimum`](@ref));
- an ordered list of tuples consisting of the decomposition of the root sublattice of the given lattice (see [`root_lattice_recognition`](@ref));
- the kissing number of the given lattice, which is proportional to the number of vectors of shortest length;
- the order of the isometry group of the given lattice.

Note: since we first compute a representatives of an isometry for each spinor
genus in `G`, the genus `G` must have rank at least 3. For rank
1 and 2 lattices, please use the function [`representatives`](@ref).
"""
function enumerate_definite_genus(
    G::ZZGenus,
    algorithm::Symbol = :default;
    rand_neigh::Int = 10,
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

# Should only consist of integers.
# For light and efficient storing, since Gram matrices for integral matrices
# are symmetric with integer values, we only store half of the Gram matrices
# as a list of integers.
# To be able to reconstruct the lattice, we also store the rank.
function _get_half_gram(L::ZZLat)
  M = gram_matrix(L)
  str = "$(rank(L))\n["
  for i in 1:nrows(M), j in i:ncols(M)
    str *= "$(M[i,j]),"
  end
  str = str[1:end-1]*"]"
  return str
end

# Return the integral integer lattice of rank `n` whose "half"
# Gram matrix consists of the entries in `V`.
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
# each file is an object, stored as a list of integers.
function load_genus(f::String)
  gg = ZZLat[]
  files = readdir(f; join=true)
  for file in files
    _n, _V = readlines(file)
    n = Base.parse(Int, _n)
    _, V = _parse(Vector{QQFieldElem}, IOBuffer(_V))
    push!(gg, _gram_from_list(V, n))
  end
  return gg
end

# Save half of the Gram matrix of `L` in a file in the
# directory corresponding to `f`.
function save_partial_lattice(L::ZZLat, f::String)
  n = length(readdir(f))
  _f = open(f*"/lat_$(n+1).jl", "w")
  Base.write(_f, _get_half_gram(L))
  close(_f)
  return nothing
end
