###############################################################################
#
#  General interface for enumeration of genera for definite ZZLat
#  ===========================================================================
#  References:
#    - [Kne57] M. Kneser "Klassenzahlen definiter quadratischer Formen", 1957;
#    - [SP91] R. Schulze-Pillot "An algorithm for computing genera of ternary
#                                and quaternary quadratic forms", 1991;
#
#  ===========================================================================
#  Given a genus G of integral lattices and a prime number p, we say that
#  p is a Kneser prime of G if the neighbour iteration algorithm for the
#  spinor genera in G at the prime p works. p is Kneser if and only if:
#
#  - Any lattice in G is isotropic at p;
#  - The prime p is not improperly automorphous for G;
#  - For any lattice (L, b) in G, the p-adic lattice L_p is maximal
#    integral with respect to the bilinear form b_p.
#
#  These properties do not depend on a choice of a lattice in G,
#  and they can actually be checked from the genus symbol directly.
#
#  TODO: Most of the infrastructure is here for enumeration of odd genera
#  at the prime p = 2, but one needs to allow to move through the even
#  genus (is it actually uniquely determined ?).
#  For now, either the genera are even or the primes are odd.
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

Return the sublattice of ``(L, b)`` consisting of vectors ``w`` such that
``b(v, w)`` is divisible by ``p``.

Input:
  - An integral integer lattice ``(L, b)``;
  - A prime number ``p``;
  - A vector ``v`` of ``L``.

Output:
  - The sublattice ``L_{v, p} := {w in L: b(v, w) in p*ZZ}`` of ``L``.
"""
function prime_dual(L::ZZLat, v::QQMatrix, p::ZZRingElem)
  M = gram_matrix(L)*transpose(v)
  K = kernel(map_entries(GF(p; cached=false), M))
  M = matrix(QQ, nrows(K), ncols(K), ZZRingElem[lift(ZZ, k) for k in K])
  return lattice_in_same_ambient_space(L, M*basis_matrix(L)) + p*L
end

@doc raw"""
    neighbour(L::ZZLat, v::ZZMatrix, p::ZZRingElem) -> ZZLat

Return the ``p``-neighbour of ``L`` associated to the admissible vector ``v``.

Input:
  - An integer lattice ``(L, b)``;
  - A prime number ``p``;
  - A vector ``v`` of ``L`` not lying in ``p*L`` such that ``b(v, v)``
    is divisible by ``p^2``.

Output:
  - The ``p``-neighbour of ``L`` defined as ``L_{v, p} + 1/p*v`` where
    ``L_{v, p} := {w in L: b(v, w) in p*ZZ}``.
"""
function neighbour(L::ZZLat, v::QQMatrix, p::ZZRingElem)
  Lvp = prime_dual(L, v, p)
  LL = Lvp + lattice_in_same_ambient_space(L, 1//p*(v*basis_matrix(L)))
  return LL
end

@doc raw"""
    make_admissible!(w::ZZMatrix, form::ZZMatrix, m::ZZRingElem, K::FinField) -> Nothing

Modify the coordinates of ``w`` by adding an element ``p*v`` of ``p*L0``
such that the square of ``w + p*v`` with respect to `form` is divisible by ``m``,
where ``(L0, b)`` is an even lattice with Gram matrix `form`.

The even lattice ``(L0, b)`` is the even sublattice of the original integral
lattice ``(L, b)`` from the neighbour algorithm.

Input:
  - A prime field ``K`` of characteristic ``p`` such that ``p`` is a Kneser
    prime for the genus of ``(L, b)``.
  - A symmetric integer matrix `form` of full rank representing the quadratic
    form on the even sublattice ``(L0, b)`` of the integer lattice ``(L, b)``.
  - An integer ``m`` which is either:
      * ``2*p^2`` if ``L = L0`` or ``p=2``;
      * ``p^2`` if ``L != L0`` and ``p`` odd.
  - A vector ``w`` in ``L0`` not lying in ``p*L0`` such that ``b(w, w)`` is divisible
    by ``m/p`` but not by ``m``.

Output:
  - Nothing, but ``w`` has been modified by a vector in ``p*L0`` so that
    ``b(w, w)`` is now divisible by ``m``.

The existence of ``v`` in ``L0`` such that ``w + p*v`` has square divisible by
``m`` is ensured by the conditions on ``w``.
(see [SP91, Chapter 1, conditions (i) & (vii)])

In the case ``p == 2``, such a vector ``v`` exists only if the prime dual lattice
``L_{w, 2} != L0``. In such a case, ``b(w, w)`` is divisible by 4 but not by 8,
and there exists ``v' \in L0`` such that ``b(v', w)`` is odd: one finds such a
``v'`` by solving ``x+y*b(w, v') == 0 mod 2`` in ``(x, y)``. The vector
``v = w + 2*v'`` satisfies the requirement to be admissible.

In the case ``p`` odd, given that ``p`` was chosen to be Kneser and that
``L0_{w, p} != L0``, there exists a solution ``v'`` to the equation
``x + 2*y*b(w, v') == 0 mod p``. The vector ``v = w + p*v'`` satisfies the
requirement to be admissible.
"""
function make_admissible!(w::QQMatrix, form::QQMatrix, m::ZZRingElem, K::FinField, _a::ZZRingElem)
  p = characteristic(K)
  # We prepare the good system to solve depending on the parity of p
  if p != 2
    a = K(div(_a, p))
    v = 2*form*transpose(w)
    vK = map_entries(b -> K(b)//a, v)
  else
    v = form*transpose(w)
    vK = map_entries(K, v)
  end

  # Solve the system to find v'
  vK = reduce(vcat, dense_matrix_type(K)[identity_matrix(K, 1), vK])
  L = kernel(vK)
  @hassert :ZGenRep 3 !iszero(view(L, :, 1))
  j = findfirst(j -> !iszero(L[j, 1]), 1:nrows(L))
  @hassert :ZGenRep 3 !isnothing(j)
  L = map_entries(b -> b//L[j, 1], L)
  v = ZZRingElem[lift(ZZ, a) for a in L[j, 2:ncols(L)]]

  # Now we modify the entries in w by adding p*v
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

@doc raw"""
    neighbours(L::ZZLat, p::ZZRingElem, algorithm::Symbol = :orbit;
                                        rand_neigh::Int = 10,
                                        callback::Function,
                                        inv_dict::Dict,
                                        _invariants::Function,
                                        save_partial::Bool = false,
                                        save_path::Union{Nothing, String} = nothing,
                                        use_mass::Bool = true,
                                        missing_mass::Base.RefValue{QQFieldElem},
                                        vain::Base.RefValue{Int} = Ref{Int}(0),
                                        stop_after::IntExt = inf,
                                        max::IntExt = inf) -> Vector{ZZLat}

Return a list of $p$-neighbours of the integral lattice ``L``.

Input:
 - A lattice ``L`` from which we compute neighbours;
 - A prime number ``p`` which is the smallest prime number at which
   Kneser's neighbour algorithm retrieves all ``p``-neighbours of ``L``
   in the spinor genus of ``L`` (called here "Kneser prime");
 - A symbol `algorithm` to choose which algorithm between `:orbit` and
   `:random`;
 - An integer `rand_neigh` to specify how many lines to try for the algorithm
   `:random`;
 - A function `callback` to compare new neighbours with lattices already
   collected in the outer scope;
 - A dictionary of isometry invariants `inv_dict` to make `callback` faster;
 - A function `_invariants` that computes the invariants of any new neighbour,
   and stores them in `inv_dict`;
 - A boolean `save_partial` telling whether to save partial results on the machine;
 - A string `save_path` telling where to store the lattice in case `save_partial` is
   `true`.
 - A boolean `use_mass` telling whether to use the mass of the genus of ``L`` for
   the termination of the algorithm;
 - A rational number `missing_mass` telling what proportion of the mass has not
   been computed yet in the outer scope (if `use_masss == true`);
 - An integer `vain` refering the number of vain iteration, i.e. how many new
   neighbours did not give rise to a non-explored isometry class in the neighbour
   graph;
 - A value `stop_after` telling after how many vain iterations the algorithm should
   stop;
 - A value `max` telling the maximum number of representatives of isometry classes
   in the genus of ``L`` to compute in the outer scope before stopping the enumeration.
"""
function neighbours(L::ZZLat, p::ZZRingElem, algorithm::Symbol = :orbit;
                                             rand_neigh::Int = 10,
                                             callback::Function = (M -> M != L),
                                             inv_dict::Dict = Dict(),
                                             _invariants::Function = M -> [],
                                             save_partial::Bool = false,
                                             save_path::Union{Nothing, String} = nothing,
                                             use_mass::Bool = true,
                                             missing_mass::Base.RefValue{QQFieldElem} = Ref{QQFieldElem}(-1),
                                             vain::Base.RefValue{Int} = Ref{Int}(0),
                                             stop_after::IntExt = inf,
                                             max::IntExt = inf)
  @assert !save_partial || !isnothing(save_path)
  bad = is_divisible_by(numerator(det(L)), p)
  even = is_even(L)
  K = GF(p; cached=false)
  @assert algorithm in [:orbit, :random, :spinor]

  # A vector in `L\p*L` is called admissible if it gives rise to a neighbour
  # of `L` which is in the genus of `L`.
  #
  # If `p` is odd, a vector `w` in `L\p*L` is called admissible if `w^2`
  # is divisible by `p^2` when `L` is odd, or `2*p^2` when `L` is even.
  # Given that the prime number `p` was chosen to be Kneser, such an admissible
  # vector exists if and only if there exists a vector `w` in `L\p*L` whose
  # square is divisible by `p`. If `w` is not already admissible and `w` does
  # not lie in p*L^#, then one can make it admissible by adding to it a suitable
  # vector from `p*L`.
  #
  # In the case where `p == 2`, by [SP91, Chapter 1, condition (v)], a vector
  # `w` in `L\2*L` is admissible if:
  # - `w^2` is disivible by `8` if `L` is even, or
  # - `w^2` is divisible by 4 if `L` odd, with `w^2` divisible by 8 only if the
  #   prime dual lattice `L_{w, 2}` is odd.
  # Such an admissible vector exists if and only if there exists a vector `w` in
  # `L0\2*L0` whose square is divisible by 4 and either `w` is already admissible,
  # or `L_{w, 2}` must be different from `L0`. In the latter case, one can make
  # `w` admissible by adding to it a suitable vector from `2*L0`.
  flag = (p == 2 && !even)
  if flag
    L0 = L
    L0 = even_sublattice(L)
    L0toL = solve(basis_matrix(L), basis_matrix(L0)) # To change the coordinates of vectors in L0
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

  if use_mass
    __mass = missing_mass[]
  end

  # For the orbit algorithm, we identify isotropic lines in `L0/p*L0` which are in
  # the same `O(L)`-orbit (because they give rise to isometric `p`-neighbours of
  # `L`).
  if algorithm == :orbit
    G = automorphism_group_generators(L; ambient_representation=false)
    if flag
      LtoL0 = inv(L0toL)
      gensp = dense_matrix_type(K)[map_entries(K, L0toL*g*LtoL0) for g in G]
    else
      gensp = dense_matrix_type(K)[map_entries(K, g) for g in G]
    end
    @hassert :ZGenRep 3 !isempty(gensp)
    orbs = Vector{elem_type(K)}[orb[1] for orb in line_orbits(gensp)] # Hopefully we took care prior to this that `line_orbits`
                                                                      # terminates and do not blow the memory up...
    maxlines = length(orbs)
    @vprintln :ZGenRep 3 "$(maxlines) orbits of lines to try"
  else
    P = enumerate_lines(K, rank(L))
    maxlines = algorithm == :random ? min(rand_neigh, length(P)) : length(P)
    @vprintln :ZGenRep 3 "Try $(maxlines) random lines"
  end

  result = typeof(L)[]

  for i in 1:maxlines
    vain[] > stop_after && break
    if algorithm == :orbit
      x = orbs[i]
    elseif algorithm == :random
      x = rand(P)
    else
      x = next(P) # Only trigerred for :spinor, where we compute a representative in each spinor genus
    end
    w0 = matrix(QQ, 1, rank(L0), ZZRingElem[lift(ZZ, k) for k in x])
    a = numerator(only(w0*form0*transpose(w0)))
    if !is_divisible_by(a, mqf)
      vain[] += 1
      continue
    end

    lifts = typeof(w0)[]
    if p == 2
      bo = is_divisible_by(a, 8)
      if even && !bo # Corner case: `w` is admissible if `bo`; if not, we can make it admissible only if `L_{w, 2} != L`
        w = w0*basis_matrix(L0)
        if is_zero(mod(divisibility(L, w), p)) # L_{w, 2} == L iff w lies in 2*L^#
          vain[] += 1
          continue
        end
        make_admissible!(w0, form0, m, K, a)
        push!(lifts, w0)
      elseif even && bo # `w0` is admissible so it is good
        push!(lifts, w0)
      elseif !even && bo # Another corner case: `wL` is admissible but if `L_{wL, 2}` is even then the neighbour is even, and we want an odd one
        wL = w0*L0toL
        if is_even(prime_dual(L, wL, p))
          vain[] += 1
          continue
        end
        push!(lifts, wL)
      else
        w = w0*basis_matrix(L0)
        wL = w0*L0toL
        # Here `w` is admissible of square 4 mod 8 so w/2 has odd square. Hence
        # `L_{w, 2} == L0` is allowed.
        #
        # If `L0_{w, 2} != L0`, we could allow another vector congruent to `w`
        # modulo 2*L0 with square divisible by 8. It is going to be another
        # admissible vector, and the neighbour might not be isometric to the one
        # obtained using `w`. The existence of such a vector is ensured only if
        # there exists a vector in `L0` with odd product with `w`, i.e. if
        # `L0_{w, 2} != L0`
        if is_zero(mod(divisibility(L0, w), p)) # L0_{w, 2} == L0 iff w lies in 2*L0^#
          push!(lifts, wL)
        else
          push!(lifts, wL)
          make_admissible!(w0, form0, ZZ(8), K, a)
          push!(lifts, w0*L0toL)
        end
      end
    else
      if !is_divisible_by(a, m)
        w = w0*basis_matrix(L0)
        bad && is_zero(mod(divisibility(L, w), p)) && continue # In this case we cannot make w admissible because w lies in p*L^#
        make_admissible!(w0, form0, m, K, a)
      end
      push!(lifts, w0)
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
      if algorithm != :spinor
        invLL = _invariants(LL)
        if haskey(inv_dict, invLL)
          push!(inv_dict[invLL], LL)
        else
          inv_dict[invLL] = ZZLat[LL]
        end
        push!(result, LL)

        if save_partial
          save_lattice(LL, save_path)
        end

        if use_mass
          s = automorphism_group_order(LL)
          sub!(__mass, __mass, 1//s)
          is_zero(__mass) && return result
        end

        length(result) == max && return result
      else
        return ZZLat[LL] # For :spinor we just want one neighbour
      end
    end
  end
  return result
end

###############################################################################
#
#  Invariants
#
###############################################################################

@doc raw"""
    _unique_iso_class!(A::Vector{ZZLat}) -> Nothing

Reorder and resize ``A`` to keep only one representative for each isometry
class represented by the lattices in ``A``.

Similar to the function `unique` where we change the equality test to an
isometry test.
"""
function _unique_iso_class!(A::Vector{ZZLat})
  isempty(A) && return A
  idxs = eachindex(A)

  # We keep the first lattice, so we start iterating from the second state
  it = iterate(idxs, 1)

  # Count the number of elements eventually kept
  # The function will iteratively stack from the start all the new
  # isometry classes to keep
  count = 1
  for x in Iterators.drop(A, 1)
    if all(y -> !is_isometric(x, y), A[1:count])
      # In that case, x represents a new isometry class, so we stack it
      # after the first isometry classes kept at the beginning of `A`
      A[it[1]] = x
      count += 1
      it = iterate(idxs, it[2])
    end
  end
  # Now the lattices to keep are at the first `count` entries of `A`
  resize!(A, count)::typeof(A)
end

@doc raw"""
    default_invariant_function(L::ZZLat) -> Tuple

Return a list of isometry invariants of the definite lattice ``L``. For now,
the invariants by default are:
- the (absolute) minimum of ``L``;
- the combinatorial data of the root sublattice of ``L``;
- the kissing numbe of ``L``;
- the order of the isometry group of ``L``.
"""
function default_invariant_function(L::ZZLat)
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

@doc raw"""
    is_maximal_integral_bilinear(G::ZZGenus, p::ZZRingElem) -> Bool

Given a genus ``G`` of integral ``\mathbb{Z}``-lattices and a prime number
``p``, return whether the lattice ``L_p`` is maximal integral in
``\mathbb{Q}L_p``, for the bilinear form on ``L_p``.

Note that this does not depend on a choice of a lattice ``L`` in ``G``,
and this property can be checked directly from the genus symbol.
"""
function is_maximal_integral_bilinear(G::ZZGenus, p::ZZRingElem)
  @req is_integral(G) "Lattices in the genus must be globally integral"
  sym = symbol(local_symbol(G, p))

  # If the local lattice is unimodular, then the bilinear form on the
  # discriminant group `q_p` is trivial and it has no isotropic vector.
  #
  # If the p-adic level `l = p^k` is greater or equal than p^2, then the
  # bilinear form on `p^(k-1) * q_p` is totally isotropic, and `q_p` has an
  # isotropic vector.
  if sym[end][1] == 0
    return true
  elseif sym[end][1] >= 2
    return false
  end

  # If the Jordan constituent of scale p has rank 1 then there is
  # no isotropic vector for the bilinear form on the discriminant group.
  #
  # If it has rank 3 then as a consequence of Chevalley's theorem
  # the bilinear form on the discriminant group has an isotropic vector.
  if sym[end][2] == 1
    return true
  elseif sym[end][2] >= 3
    return false
  end

  # For the rank 2, there are only two possible normal forms for the
  # bilinear form on the discriminant group.
  # In the case p=2, they both admit an isotropic vector
  p == 2 && return false

  # For the odd case, one of them has an isotropic vector but
  # not the other one
  sym[end][3] == jacobi_symbol(-1, p) && return false
  return true
end

@doc raw"""
    smallest_kneser_prime(G::ZZGenus) -> ZZRingElem

Given a genus ``G`` of integral ``\mathbb{Z}``-lattice, return the
smallest Kneser prime ``p`` for ``G``.

A prime number ``p`` is called Kneser for ``G`` if:
- The lattices in ``G`` are isotropic locally at ``p``;
- The lattices in ``G`` are maximal integral locally at ``p`` with respect
  to the associated bilinear form;
- The prime ``p`` is not improperly automorphous for ``G``;
"""
function smallest_kneser_prime(G::ZZGenus)
  @req is_integral(G) "The lattices in the genus must be integral"
  p = is_even(G) ? ZZ(2) : ZZ(3)
  VG = rational_isometry_class(G)
  isg, f = _improper_spinor_generators(G)
  if is_empty(isg) # Unique spinor genus
    while !is_isotropic(local_symbol(VG, p)) || !is_maximal_integral_bilinear(G, p)
      p = next_prime(p)
    end
  else # Happens very rarely
    bps = bad_primes(G)
    while (p in bps) || !is_zero(f(QQ(p))) || !is_isotropic(local_symbol(VG, p)) || !is_maximal_integral_bilinear(G, p)
      p = next_prime(p)
    end
  end
  return p
end

smallest_kneser_prime(L::ZZLat) = smallest_kneser_prime(genus(L))

@doc raw"""
    enumerate_definite_genus(known::Vector{ZZLat}, algorithm::Symbol = :default) -> Vector{ZZLat}, QQFieldElem
    enumerate_definite_genus(L::ZZLat, algorithm::Symbol = :default) -> Vector{ZZLat}
    enumerate_definite_genus(G::ZZGenus, algorithm::Symbol = :default) -> Vector{ZZLat}

Enumerate lattices in a given genus of integral definite lattices of rank at
least `3`, using Kneser's neighbour algorithm.

The output consists of a list of lattices representing the isometry classes
in the given genus.

For the first argument, one can choose to give directly a genus symbol ``G`` or
a lattice ``L`` in ``G``. Otherwise, one can give a list of known lattices
``G`` to continue an incomplete enumeration (in which case the lattices are
assumed to be in the same spinor genus).

The second argument gives the choice to which algorithm to use for the enumeration.
We currently support two algorithms:
- `:random` which finds new isometry classes by constructing neighbours from random isotropic lines;
- `:orbit` which computes orbits of isotropic lines before constructing neighbours.
If `algorithm = :default`, the function chooses the most appropriate algorithm
depending on the rank and determinant of the genus to be enumerated.

There are possible extra optional arguments:
- `rand_neigh::Int` (default = `10`) -> for random enumeration, how many random neighbours are computed at each iteration;
- `invariant_function::Function` (default = `default_invariant_function`) -> a function to compute isometry invariants in order to avoid unnecessary isometry tests;
- `save_partial::Bool` (default = `false`) -> whether one wants to save iteratively new isometry classes (for instance for large genera);
- `save_path::String` (default = `nothing`) -> a path to a folder where to save new lattices in the case where `save_partial` is true;
- `use_mass::Bool` (default = `true`) -> whether to use the mass formula as termination condition;
- `stop_after::IntExt` (default = `inf`) -> the algorithm stops after the specified amount of vain iterations without finding a new isometry class is reached;
- `max::IntExt` (default = `inf`) -> the algorithm stops after finding `max` new isometry classes.

In the case where one gives a list of `known` lattices in input, the output list
contains a copy of `known` together with any new lattice computed. The extra
output of the function is a rational number giving the portion of the mass of
the (spinor) genus which is missing. It is set to be `0` whenever the mass is not
used (`use_mass = false`).
Moreover, there are two other possible extra optional arguments:
- `distinct::Bool` (default = `false`) -> whether the lattices in `known` are known to be pairwise non-isometric;
- `missing_mass::QQFieldElem` (default = `nothing`) -> if `use_mass` and `distinct` are true, and the partial mass of `known` is known, gives what is the part of the mass which is missing;
If `distinct == false`, the function first compares all the lattices in `known`
to only keep one representative for each isometry class represented.

If `save_partial == true`, the lattices are stored in a compact way in a `.txt`
file. The storing only remembers the rank of a lattice, half of its Gram matrix
(which is enough to reconstruct the lattice as a standalone object) and the order
of the isometry group of the lattice if it has been computed.

The `default_invariant_function` currently computes:
- the absolute length of a shortest vector in the given lattice (also known as [`minimum`](@ref));
- an ordered list of tuples consisting of the decomposition of the root sublattice of the given lattice (see [`root_lattice_recognition`](@ref));
- the kissing number of the given lattice, which is proportional to the number of vectors of shortest length;
- the order of the isometry group of the given lattice.
"""
enumerate_definite_genus(::Union{ZZLat, ZZGenus, Vector{ZZLat}}, ::Symbol)

function enumerate_definite_genus(
    known::Vector{ZZLat},
    algorithm::Symbol = :default;
    rand_neigh::Int = 10,
    distinct::Bool = false,
    invariant_function::Function = default_invariant_function,
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
  inv_lat = invariant_function(L)
  inv_dict = Dict{typeof(inv_lat), Vector{ZZLat}}(inv_lat => ZZLat[L])
  for N in itk
    inv_lat = invariant_function(N)
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
    return invariant_function(M)
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
  p = smallest_kneser_prime(L)

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
    N = neighbours(res[i], p, algorithm; rand_neigh, callback, inv_dict, _invariants, use_mass, missing_mass, save_partial, save_path, vain, stop_after, max)

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
    spinor_genera_in_genus(L::ZZLat) -> ZZLat

Given an integral ``\mathbb{Z}``-lattice ``L`` of rank at least 3,
return a list of representatives of the spinor genera in the
genus of ``L``.

# Examples

```jldoctest
julia> L = integer_lattice(; gram=QQ[2 1 0; 1 2 0; 0 0 18])
Integer lattice of rank 3 and degree 3
with gram matrix
[2   1    0]
[1   2    0]
[0   0   18]

julia> L1, L2 = Hecke.spinor_genera_in_genus(L)
2-element Vector{ZZLat}:
 Integer lattice of rank 3 and degree 3
 Integer lattice of rank 3 and degree 3

julia> index(L1, intersect(L1, L2)) == index(L2, intersect(L1, L2)) == 5
true

julia> L2
Integer lattice of rank 3 and degree 3
with gram matrix
[2   0   0]
[0   6   3]
[0   3   6]
```
"""
function spinor_genera_in_genus(L::ZZLat)
  @req !is_definite(L) || rank(L) >= 3 "The lattice must be indefinite or of rank at least 3"
  res = ZZLat[L]
  primes = improper_spinor_generators(genus(L))
  is_empty(primes) && return res
  for p in primes
    N = only(neighbours(L, p, :spinor))
    for i in 1:length(res)
      M = res[i]
      LL = lll(intersect(p*M+N, 1//p*M))
      push!(res, LL)
    end
  end
  return res
end

function enumerate_definite_genus(
    _L::ZZLat,
    algorithm::Symbol = :default;
    rand_neigh::Int = 10,
    invariant_function::Function = default_invariant_function,
    save_partial::Bool = false,
    save_path::Union{IO, String, Nothing} = nothing,
    use_mass::Bool = true,
    stop_after::IntExt = inf,
    max::IntExt = inf
  )
  @req !save_partial || !isnothing(save_path) "No path mentioned for saving partial results"

  edg = ZZLat[]

  sc = scale(_L)
  if sc != 1
    L = rescale(_L, 1//sc)
  else
    L = _L
  end
  # We first compute representatives for each spinor genus
  spinor_genera = spinor_genera_in_genus(L)
  @vprintln :ZGenRep 1 "$(length(spinor_genera)) spinor genera to enumerate"

  # We enumerate each spinor genus separately.
  for M in spinor_genera
    vain = Ref{Int}(0)
    # The mass of a genus is "evenly distributed" among its spinor genera.
    # Hence, by dividing the mass of the genus by the number of spinor genera,
    # we know what portion of the mass the lattices of one spinor genus recover,
    # and we get a termination condition for each spinor genus.
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
                                                             invariant_function,
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
                                                           invariant_function,
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
  sc != 1 && map!(L -> rescale(L, sc), edg, edg)
  return edg
end

function enumerate_definite_genus(
    G::ZZGenus,
    algorithm::Symbol = :default;
    rand_neigh::Int = 10,
    invariant_function::Function = default_invariant_function,
    save_partial::Bool = false,
    save_path::Union{IO, String, Nothing} = nothing,
    use_mass::Bool = true,
    stop_after::IntExt = inf,
    max::IntExt = inf
  )
  L = representative(G)
  max == 1 && return ZZLat[L]
  return enumerate_definite_genus(L, algorithm; rand_neigh,
                                                invariant_function,
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

@doc raw"""
    _storing_data(L::ZZLat) -> String

Return a chain of characters containing a minimal set of data to store and
reconstruct ``L``. The lattice ``L`` is assumed to be integral

When written on a .txt file, it consists of two lines:
- One containing an integer representing the rank of ``L``;
- One containing a list of integers representing half of the Gram matrix of
  ``L``.

In the case where the order of the automorphisms group of ``L`` is known, the
value is stored using an integer on a third line.
"""
function _storing_data(L::ZZLat)
  M = gram_matrix(L)
  str = "$(rank(L))\n["
  for i in 1:nrows(M), j in i:ncols(M)
    str *= "$(M[i,j]),"
  end
  str = str[1:end-1]*"]"
  if isdefined(L, :automorphism_group_order)
    str *= "\n$(automorphism_group_order(L))"
  end
  return str
end

@doc raw"""
    _lattice_from_half_gram_and_rank(V::Vector{QQFieldElem}, n::Int) -> ZZLat

Given an integer ``n`` and a list ``V`` consisting of ``n(n+1)/2`` elements,
return the ``\mathbb{Z}``-lattice of rank ``n`` and half Gram matrix given
by the elements in ``V``.
"""
function _lattice_from_half_gram_and_rank(V::Vector{QQFieldElem}, n::Int)
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

@doc raw"""
    load_genus(f::String) -> Vector{ZZLat}

Load the genus stored in the directory with path ``f``.
The directory should contain only files containing information
about a representative for each isometry class in the corresponding genus.

Such a file is composed of two lines:
- One containing an integer ``n`` representing the rank of the lattice;
- One containing a list of ``n(n+1)/2`` integers representing half of the
  Gram matrix of the correponding lattice.

A third line is allowed and must contained an integer ``o`` representing the
order of the isometry group of the corresponding lattice.
"""
function load_genus(f::String)
  gg = ZZLat[]
  files = readdir(f; join=true)
  for file in files
    rl = readlines(file)
    n = Base.parse(Int, rl[1])
    _, V = _parse(Vector{QQFieldElem}, IOBuffer(rl[2]))
    L = _lattice_from_half_gram_and_rank(V, n)
    if length(rl) == 3
      L.automorphism_group_order = Hecke._parse(ZZRingElem, IOBuffer(rl[3]))[1]
    end
    push!(gg, L)
  end
  return gg
end

@doc raw"""
    save_lattice(L::ZZLat, f::String) -> Nothing

Save (in a compact way) the lattice ``L`` in a file, in the directory
with path ``f``.
The lattice ``L`` is assumed to be integral.

Such a file is composed of two lines:
- One containing an integer ``n`` representing the rank of ``L``;
- One containing a list of ``n(n+1)/2`` integers representing half of the
  Gram matrix of ``L``.

If the order ``o`` of the isometry group of ``L`` has been computed, then
we had the value ``o`` to a third line of the file.
"""
function save_lattice(L::ZZLat, f::String)
  n = length(readdir(f))
  _f = open(f*"/lat_$(n+1).txt", "w")
  Base.write(_f, _storing_data(L))
  close(_f)
  return nothing
end
