# Algorithm for right class set of a quaternion order.
# See Appendix by Voight in Smit-Marseglia, "Ideal classes of orders in
# quaternion algebras".
#
# The code is inspired by the Magma implementation in
# https://github.com/dansme/hermite by Smertnig-Voight
#
# TODO: redo the calculations

struct _RightClassSetIsomorphismContext{A, M, O, I, J}
  algebra::A
  algebra_map::M
  order::O
  ideals::IdDict{I, J}
end

function _right_class_set_isomorphism_context(O::AlgAssRelOrd)
  A = algebra(O)
  AQ, AQtoA = restrict_scalars(A, QQ)
  OQ = order(AQ, preimage.(Ref(AQtoA), elem_in_algebra.(absolute_basis(O))))
  ideals = IdDict{ideal_type(typeof(O)), ideal_type(typeof(OQ))}()
  return _RightClassSetIsomorphismContext(AQ, AQtoA, OQ, ideals)
end

function _absolute_ideal(C::_RightClassSetIsomorphismContext, I)
  return get!(C.ideals, I) do
    ideal_from_lattice_gens(C.algebra, C.order,
                            preimage.(Ref(C.algebra_map), absolute_basis(I)))
  end
end

function _prepare_for_class_set_isomorphism!(I)
  O = left_order(I)
  if !has_attribute(O, :maximal_order)
    # Keep the maximal order stable across comparisons so that the PIP caches
    # attached to it, in particular the unit representatives, can be reused.
    set_attribute!(O, :maximal_order, maximal_order(O))
  end
  return nothing
end

function _isomorphic_for_right_class_set(C::_RightClassSetIsomorphismContext, I, J)
  IQ = _absolute_ideal(C, I)
  JQ = _absolute_ideal(C, J)
  _prepare_for_class_set_isomorphism!(IQ)
  return _isisomorphic_generic(IQ, JQ; side = :right)[1]
end

@doc raw"""
    right_class_set(O::Union{AlgAssAbsOrd, AlgAssRelOrd}) -> Vector

Return representatives of the classes of locally principal right ideals of
the order $O$ of a quaternion algebra $A$ over $\mathbf{Q}$ or a number field.
Two ideals $I$ and $J$ lie in the same class if $J = \alpha I$ for some
$\alpha \in A^\times$.

The representatives are integral right ideals of $O$.

# Examples

```jldoctest
julia> O = maximal_order(quaternion_algebra_ramified_at(QQ, 97));

julia> C = right_class_set(O);

julia> length(C), all(I -> right_order(I) == O, C)
(8, true)

julia> length(right_class_set(maximal_order(quaternion_algebra(QQ, -1, 3))))
1
```
"""
@attr Vector{ideal_type(typeof(O))} function right_class_set(O::Union{AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}}, AlgAssRelOrd})
  return _right_class_set(O)
end

function _right_class_set(O::AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}})
  if _is_totally_definite_quaternion(algebra(O))
    return _right_class_set_definite(O)
  end
  return _right_class_set_indefinite(O)
end

function _right_class_set(
    O::AlgAssRelOrd{AbsSimpleNumFieldElem, <:Any, <:QuaternionAlgebra})
  if _is_totally_definite_quaternion(algebra(O))
    return _right_class_set_definite(O)
  end
  return _right_class_set_indefinite(O)
end

_right_class_set(O::AlgAssRelOrd) = _right_class_set_naive(O)

function _right_class_set_naive(O::AlgAssRelOrd)
#    { Compute the right class set of a quaternion order O in a naive way.
#      This code is originally by Voight (also appears as commented out code in
#      ideals-jv.m). Some small modifications have been made.
#
#      We use this naive version, because it works for any order.
#    }
  avoidprimes = support(_reduced_disc(O))
  A = algebra(O)
  R = base_ring(O)
  massformula = 1//length(unit_group_modulo_scalars(O))
  masses = [massformula] # record the contribution of each ideal class to the total mass
  masstotal = mass(O)
  #    vprintf Quaternion:
  #        "Starting with the trivial ideal class. \nMass %o out of total mass %o\n", massformula, masstotal;
  ideals = [1*O]
  isomorphism_context = _right_class_set_isomorphism_context(O)
  pe = 1
  # We first try prime ideals of small norm
  primes = sort!(prime_ideals_up_to(R, 100), by = norm)
  while massformula != masstotal
    #@info pe, massformula, masstotal
    if length(primes) == 0
      # have not found anything, so we switch over to
      # enumerating prime ideals by minimum
      pe = next_prime(pe)
      primes = prime_ideals_over(R, pe)
    end
    pp = popfirst!(primes)
      if pp in avoidprimes
        continue
      end
      maxids = maximal_integral_ideals(O, pp; side = :right)
      for II in maxids
        found = false
        for J in ideals
          if _isomorphic_for_right_class_set(isomorphism_context, II, J)
            found = true
            break
          end
        end
        if !found
          push!(ideals, II)
          mass = 1//length(unit_group_modulo_scalars(left_order(II)))
          massformula += mass
          push!(masses, mass)
          if massformula == masstotal
            break
          end
        end
      #end
    end
  end
  return ideals
end

################################################################################
#
#  Right class sets of totally definite orders
#
################################################################################

# The right class set of an order O of a definite quaternion algebra over QQ.
#
# A breadth-first search of the neighbour graph at the prime ell, the first of
# _neighbour_primes: for a right O-ideal I with left order L and a right
# L-ideal P of reduced norm ell, P * I is again a locally principal right
# O-ideal. Two classes are joined by ell-neighbours if and only if their
# reduced norms agree in Cl_{G(O)} Z / <[ell]> (Voight, Quaternion Algebras,
# Theorem 28.5.5 applied to O[1/ell], as in the proof of Proposition
# 28.5.18). Over QQ that group is 2-torsion and generated by the other primes
# of _neighbour_primes, so whenever the search closes a component short of the
# mass, it restarts from an ideal whose reduced norm is the product of the
# next subset of those primes.
#
# Equivalent ideals have isomorphic left orders, so a candidate is compared
# only with the classes whose left orders have the same complete isomorphism
# invariant (_class_set_key). The search ends when the masses
# 1/#(L^x/Z^x) of the classes found add up to mass(O), which proves that every
# class has been found, as in Kirschmer-Voight, SIAM J. Comput. 39 (2010),
# 1714-1747, Algorithm 7.4 with Remark 7.5, there for Eichler orders.
function _right_class_set_definite(
    O::AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}})
  N = _reduced_disc(O)
  masstotal = mass(O)
  key_of = _class_set_key(O)
  # A prime reduced discriminant means a maximal order of B_p, for which the
  # number of classes per type is known.
  bp = is_prime(N)

  ideals = [1 * O]
  leftorders = [O]
  classmass = [QQ(1, length(unit_group_modulo_scalars(O)))]
  types = Dict(key_of(O) => [1])
  massformula = classmass[1]
  frontier = [1]
  # For a class reached as P * I from the class of I, the basis matrix of
  # conj(P), which leads back to the class of I, since conj(P) * P is ell
  # times the right order of P; nothing for the first class and the seeds.
  back_edges = Union{Nothing, QQMatrix}[nothing]

  # Add the class of the right O-ideal J, reached by the neighbour P or by
  # nothing, if it is new, and return its mass; return 0 otherwise.
  function consider!(J, P)
    # The product does not record the order of which J is a right ideal.
    J.order = O
    J.isright = 1
    L = left_order(J)
    key = key_of(L)
    found = get(types, key, Int[])
    limit = bp ? _classes_per_type(key, N) : typemax(Int)
    length(found) >= limit && return zero(QQ)
    any(k -> _right_ideals_equivalent(J, ideals[k]), found) && return zero(QQ)
    # Isomorphic left orders have unit groups of the same order.
    m = isempty(found) ? QQ(1, length(unit_group_modulo_scalars(L))) :
                         classmass[first(found)]
    push!(ideals, J)
    push!(leftorders, L)
    push!(classmass, m)
    push!(back_edges, P === nothing ? nothing : _conjugate_basis_matrix(P))
    push!(get!(types, key, Int[]), length(ideals))
    push!(frontier, length(ideals))
    return m
  end

  primes = _neighbour_primes(O)
  ell, others = first(primes), primes[2:end]
  seed = 1
  # A class counted twice makes the mass overshoot, so `<` rather than `!=`:
  # the search then stops and _check_mass reports it.
  while massformula < masstotal
    if isempty(frontier)
      seed < 2^length(others) || break
      massformula += consider!(_seed_ideal(O, others, seed), nothing)
      seed += 1
      continue
    end
    i = popfirst!(frontier)
    for P in maximal_integral_ideals(leftorders[i], ell; side = :right)
      basis_matrix(P) == back_edges[i] && continue
      massformula += consider!(P * ideals[i], P)
      massformula >= masstotal && break
    end
  end
  _check_mass(massformula, masstotal)
  return ideals
end

# The same over a totally real field: the neighbours are those at every prime
# of _neighbour_primes, which generate Cl_{G(O)} R, so the graph is connected.
# Candidates are compared only with the classes whose left orders have unit
# groups modulo scalars of the same order.
function _right_class_set_definite(
    O::AlgAssRelOrd{AbsSimpleNumFieldElem, <:Any, <:QuaternionAlgebra})
  masstotal = mass(O)
  ideals = [1 * O]
  leftorders = [left_order(ideals[1])]
  u = length(unit_group_modulo_scalars(leftorders[1]))
  by_units = Dict(u => [1])
  massformula = QQ(1, u)
  # For a class reached as Q * I from the class of I, conj(Q), if nrd(Q) is
  # principal: conj(Q) * Q is nrd(Q) times the right order of Q, so conj(Q)
  # then leads back to the class of I. Otherwise nothing.
  back_edges = Union{Nothing, eltype(ideals)}[nothing]
  primes = _neighbour_primes(O)
  principal = Dict(P => is_principal(P) for P in primes)
  frontier = [1]
  while massformula < masstotal && !isempty(frontier)
    i = popfirst!(frontier)
    for P in primes,
        Q in maximal_integral_ideals(leftorders[i], P; side = :right)
      back_edges[i] !== nothing && Q == back_edges[i] && continue
      J = Q * ideals[i]
      J.order = O
      J.isright = 1
      L = left_order(J)
      u = length(unit_group_modulo_scalars(L))
      found = get!(by_units, u, Int[])
      any(k -> _right_ideals_equivalent(J, ideals[k]), found) && continue
      push!(ideals, J)
      push!(leftorders, L)
      push!(back_edges, principal[P] ? _conjugate(Q) : nothing)
      push!(found, length(ideals))
      push!(frontier, length(ideals))
      massformula += QQ(1, u)
      massformula >= masstotal && break
    end
  end
  _check_mass(massformula, masstotal)
  return ideals
end

# The masses of the classes found add up to exactly mass(O): falling short
# means the search stalled, overshooting that a class was counted twice.
function _check_mass(found::QQFieldElem, total::QQFieldElem)
  found == total && return nothing
  why = found < total ? "the search stalled" : "a class was counted twice"
  error("Classes of mass $found found, not $total: $why")
end

# Whether the invertible right ideals X and Y of a totally definite quaternion
# algebra lie in the same class, that is, whether the colon ideal
# (Y : X) = Y X^(-1) (Voight, Quaternion Algebras, Proposition 16.5.8),
# scaled into an integral right ideal of the left order of X, is principal.
function _right_ideals_equivalent(X, Y)
  C = ideal(algebra(X), _colon_raw(Y, X, :right))
  Gamma = left_order(X)
  Cint = denominator(C, Gamma) * C
  Cint.order = Gamma
  return _is_principal(Cint, Gamma; side = :right)
end

# Primes not dividing the reduced discriminant N of the order O of a definite
# quaternion algebra over QQ, whose neighbours reach every right class of O:
# the least such prime if O is Eichler, and otherwise the least primes whose
# classes generate (Z/mZ)^x modulo squares, where m is the product of the odd
# primes q where O is not Eichler, and of 8 if 2 is one of them.
#
# Cl_{G(O)} Z is Zhat^x / prod_q nrd(O_q^x), and nrd(O_q^x) = Z_q^x where O_q
# is Eichler (Voight, Quaternion Algebras, Example 28.5.16), so only the primes
# q where it is not contribute. There nrd(O_q^x) contains the squares, the
# norms of scalars, so the group is a quotient of
# prod_q Z_q^x / (Z_q^x)^2, which is (Z/mZ)^x modulo squares; primes
# generating that generate any quotient, and then every class contains an
# ideal whose reduced norm is a product of them (Voight, Quaternion Algebras,
# Proposition 28.5.18).
function _neighbour_primes(O::AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}})
  N = _reduced_disc(O)
  # A prime reduced discriminant means a maximal order of B_p.
  S = is_prime(N) ? ZZRingElem[] : _non_eichler_primes(O)
  if isempty(S)
    ell = ZZ(2)
    while is_divisible_by(N, ell)
      ell = next_prime(ell)
    end
    return [ell]
  end
  m = prod(q^(valuation(ZZ(4), q) + 1) for q in S)
  Zm, = residue_ring(ZZ, m)
  U, mU = unit_group(Zm)
  G, UtoG = quo(U, 2)
  primes = ZZRingElem[]
  classes = elem_type(G)[]
  ell = ZZ(1)
  while order(sub(G, classes)[1]) < order(G)
    ell = next_prime(ell)
    is_divisible_by(N, ell) && continue
    g = UtoG(preimage(mU, Zm(ell)))
    has_preimage_with_preimage(sub(G, classes)[2], g)[1] && continue
    push!(primes, ell)
    push!(classes, g)
  end
  return primes
end

# Prime ideals of the base ring R of O, not dividing its reduced discriminant,
# whose neighbours reach every right class of O: the least ones by norm whose
# classes generate the narrow ray class group modulo m, where m is the product
# of p^e over the primes p where O is not Eichler, with e = 1 for odd p and
# e = 2 v_p(2) + 1 above 2.
#
# Cl_{G(O)} R is F_{>> 0}^x \ Fhat^x / prod_p nrd(O_p^x), with all real places
# ramified. nrd(O_p^x) is R_p^x where O_p is Eichler (Voight, Quaternion
# Algebras, Example 28.5.16), and contains the squares of R_p^x everywhere,
# hence 1 + p^e R_p by Hensel's lemma. So Cl_{G(O)} R is a quotient of the
# narrow ray class group modulo m, and primes generating that generate it;
# then every class contains an ideal whose reduced norm is a product of them
# (Voight, Quaternion Algebras, Proposition 28.5.18).
function _neighbour_primes(
    O::AlgAssRelOrd{AbsSimpleNumFieldElem, <:Any, <:QuaternionAlgebra})
  R = base_ring(O)
  K = base_ring(algebra(O))
  bad = support(_reduced_disc(O))
  m = 1 * R
  for P in _non_eichler_primes(O)
    e = is_divisible_by(minimum(P), 2) ? 2 * ramification_index(P) + 1 : 1
    m *= P^e
  end
  C, mC = ray_class_group(m, real_places(K); GRH = false)
  primes = eltype(bad)[]
  classes = elem_type(C)[]
  # Every class contains primes (Neukirch, Algebraic Number Theory, Theorem
  # VII.13.2), so the search ends.
  bound = 10
  while true
    for P in sort!(prime_ideals_up_to(R, bound); by = norm)
      (P in bad || P in primes) && continue
      g = mC \ P
      H, mH = sub(C, classes)
      # At least one prime, even if the group is trivial
      if isempty(primes) || !has_preimage_with_preimage(mH, g)[1]
        push!(primes, P)
        push!(classes, g)
        order(sub(C, classes)[1]) == order(C) && return primes
      end
    end
    bound *= 2
  end
end

# An integral right ideal of the order O over QQ whose reduced norm is the
# product of the primes primes[b] for which bit b - 1 of k is set, built as a
# chain of neighbours. The primes must not divide the reduced discriminant.
function _seed_ideal(O::AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}},
                     primes::Vector{ZZRingElem}, k::Int)
  I = 1 * O
  for (b, ell) in enumerate(primes)
    (k >> (b - 1)) & 1 == 1 || continue
    I = first(maximal_integral_ideals(left_order(I), ell; side = :right)) * I
    I.order = O
    I.isright = 1
  end
  return I
end

# The basis matrix of conj(P), for an ideal P of a quaternion algebra over QQ,
# in the Hermite normal form of the ideals of maximal_integral_ideals, so that
# equal matrices are equal lattices. Conjugation negates the coordinates on i,
# j and ij.
function _conjugate_basis_matrix(P::AlgAssAbsOrdIdl)
  M = basis_matrix(P)
  for r in 1:4, c in 2:4
    M[r, c] = -M[r, c]
  end
  return _hnf_integral(M, :lowerleft)
end

# The conjugate of an ideal Q of a quaternion algebra over a number field, an
# ideal with the left and right orders of Q swapped.
function _conjugate(Q::AlgAssRelOrdIdl)
  M = basis_pmatrix(Q)
  m = matrix(M)
  for r in 1:4, c in 2:4
    m[r, c] = -m[r, c]
  end
  return ideal(algebra(Q), pseudo_matrix(m, coefficient_ideals(M)))
end

################################################################################
#
#  Isomorphism invariants of orders over QQ
#
################################################################################

# A function returning a complete isomorphism invariant of the orders of a
# definite quaternion algebra over QQ that are locally isomorphic to O: the
# reduced Gram matrix of the Gross lattice for a maximal order of B_p, from
# which _classes_per_type reads the number of classes, and of the ternary
# quadratic form otherwise.
function _class_set_key(O::AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}})
  return is_prime(_reduced_disc(O)) ? _gross_gram_key : _ternary_key
end

# The Eisenstein reduced Gram matrix of the Gross lattice of a maximal order L
# of B_p: two of them are isomorphic if and only if their Gross lattices are
# isometric (Goren-Love, Canad. J. Math. 77 (2025), 1938-1965, Theorem 1.4).
function _gross_gram_key(L::AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}})
  G = gross_gram_matrix(gross_lattice_basis(L))
  return eisenstein_reduction(G; check = false)
end

# The number of right classes of a maximal order of B_p whose left order has
# the Gross key `key`: 1 if its supersingular elliptic curve is defined over
# F_p, and 2 otherwise (Gross, Heights and the special values of L-series,
# CMS Conf. Proc. 7 (1987), p. 125 and Proposition 2.4). The curve is defined
# over F_p if and only if the first two vectors of a basis attaining the
# successive minima span a lattice of determinant 4p, as the first two vectors
# of an Eisenstein reduced basis do (He-Korpal-Tran-Vincent,
# arXiv:2503.03478, Propositions 3.2.1 and 3.2.2, and Section 2.3); that
# determinant is the leading 2 x 2 minor of the reduced Gram matrix.
function _classes_per_type(key::ZZMatrix, p::ZZRingElem)
  return key[1, 1] * key[2, 2] - key[1, 2]^2 == 4 * p ? 1 : 2
end

# The Eisenstein reduced Gram matrix of the ternary quadratic form of the
# order O of a definite quaternion algebra over QQ: N nrd on the elements of
# trace zero in the dual of O with respect to the reduced trace, where
# N = discrd(O), scaled by 2 to be integral. Two orders of the algebra are
# isomorphic if and only if their forms are similar (Voight, Quaternion
# Algebras, Main Theorem 22.4.1 with 22.4.8 and Remark 22.4.3), and the
# positive definite forms of a similarity class are one GL_3(Z)-equivalence
# class, of which the reduced form is unique (Dickson, Studies in the Theory of
# Numbers, Theorem 104).
function _ternary_key(O::AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}})
  A = algebra(O)
  M = basis_matrix(O)
  # With T the Gram matrix of trd(x y) on the basis of O, the dual basis has
  # the coordinates inv(T) * M. The reduced trace of an element is twice its
  # first coordinate.
  T = change_base_ring(QQ, trred_matrix(O))
  dual = inv(T) * M
  K = kernel(matrix(ZZ, 1, 4, [ZZ(2 * dual[r, 1]) for r in 1:4]); side = :right)
  E = transpose(change_base_ring(QQ, K)) * dual
  N = abs(_reduced_disc(O))
  G = change_base_ring(ZZ, N * _trace_form_gram(A, E))
  return eisenstein_reduction(G; check = false)
end

# The Gram matrix of (x, y) -> trd(x conj(y)) on the elements of the
# quaternion algebra A whose coordinates are the rows of M.
function _trace_form_gram(A::QuaternionAlgebra, M::MatElem)
  return M * _trace_diagonal(A) * transpose(M)
end

# The Gram matrix of (x, y) -> trd(x conj(y)) on the basis 1, i, j, ij of A,
# with i^2 = a and j^2 = b: nrd(x0 + x1 i + x2 j + x3 ij) is
# x0^2 - a x1^2 - b x2^2 + ab x3^2.
function _trace_diagonal(A::QuaternionAlgebra)
  a, b = standard_form(A)
  K = base_ring(A)
  return diagonal_matrix(K, [K(2), -2 * a, -2 * b, 2 * a * b])
end

################################################################################
#
#  Right class sets of indefinite orders
#
################################################################################

# The right class set of an order O of a quaternion algebra satisfying the
# Eichler condition: 1 * O, then one integral right ideal of prime reduced
# norm for each further class of Cl_{G(O)} R, onto which the reduced norm is a
# bijection (Voight, Quaternion Algebras, Theorem 28.5.5).
function _right_class_set_indefinite(O)
  G, cls = _indefinite_class_group(O)
  N = _reduced_disc(O)
  ideals = [1 * O]
  classes = [zero(G)]
  if O isa AlgAssAbsOrd
    candidates = b -> [ZZ(p) for p in PrimesSet(2, b)]
    good = p -> !is_divisible_by(N, p)
  else
    R = base_ring(O)
    candidates = b -> sort!(prime_ideals_up_to(R, b); by = norm)
    good = P -> valuation(N, P) == 0
  end
  # Every class of a ray class group contains infinitely many primes
  # (Neukirch, Algebraic Number Theory, Theorem VII.13.2).
  bound = 10
  while length(ideals) < order(G)
    for P in candidates(bound)
      good(P) || continue
      g = cls(P)
      g in classes && continue
      push!(ideals, first(maximal_integral_ideals(O, P; side = :right)))
      push!(classes, g)
    end
    bound *= 2
  end
  return ideals
end

# The group Cl_{G(O)} R in bijection with the right classes of the order O of
# an indefinite quaternion algebra, and the map sending a prime of R not
# dividing discrd(O) to the class of the ideals of that reduced norm: the ray
# class group modulo m and the real places where the algebra ramifies, divided
# by the local reduced norms of units, where m is the product of p^(v_p(4) + 1)
# over the primes p where O is not Eichler (Voight, Quaternion Algebras,
# Theorem 28.5.5; Smertnig-Voight, Trans. London Math. Soc. 6 (2019), 53-86,
# Remark 6.12, for a definite algebra, there with every real place).
function _indefinite_class_group(
    O::AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}})
  S = _non_eichler_primes(O)
  if isempty(S)
    G = abelian_group(Int[])
    return G, (_::IntegerUnion) -> zero(G)
  end
  ls = [valuation(ZZ(4), p) + 1 for p in S]
  m = prod(p^l for (p, l) in zip(S, ls))
  Zm, = residue_ring(ZZ, m)
  U, mU = unit_group(Zm)
  cls(a::IntegerUnion) = preimage(mU, Zm(a))
  # No real place ramifies, so -1 is among the global elements divided out.
  H = [cls(-1)]
  for (p, l) in zip(S, ls)
    q = p^l
    Zq, = residue_ring(ZZ, q)
    Uq, mUq = unit_group(Zq)
    res = _local_norm_residues(O, p, l)
    local_gens = res === :all ? gens(Uq) : [preimage(mUq, Zq(r)) for r in res]
    # The squares are the norms of scalars.
    for u in vcat(local_gens, [2 * g for g in gens(Uq)])
      push!(H, cls(crt(lift(mUq(u)), q, ZZ(1), divexact(m, q))))
    end
  end
  G, mG = quo(U, H)
  return G, (ell::IntegerUnion) -> mG(cls(ell))
end

function _indefinite_class_group(
    O::AlgAssRelOrd{AbsSimpleNumFieldElem, <:Any, <:QuaternionAlgebra})
  A = algebra(O)
  R = base_ring(O)
  K = base_ring(A)
  omega = [v for v in real_places(K) if !is_split(A, v)]
  S = _non_eichler_primes(O)
  ls = [valuation(R(4), P) + 1 for P in S]
  m = prod((P^l for (P, l) in zip(S, ls)); init = 1 * R)
  C, mC = ray_class_group(m, omega; GRH = false)
  n = minimum(m)
  H = elem_type(C)[]
  for (k, P) in enumerate(S)
    Pl = P^ls[k]
    rest = prod((S[j]^ls[j] for j in eachindex(S) if j != k); init = 1 * R)
    Q, mQ = quo(R, Pl)
    U, mU = unit_group(Q)
    res = _local_norm_residues(O, P, ls[k])
    local_gens = res === :all ? gens(U) : [preimage(mU, mQ(r)) for r in res]
    for u in vcat(local_gens, [2 * g for g in gens(U)])
      # b + t n is b modulo m, and totally positive for t large.
      b = make_positive(crt(lift(mU(u)), Pl, one(R), rest), n)
      push!(H, mC \ (b * R))
    end
  end
  G, mG = quo(C, H)
  return G, (P::AbsNumFieldOrderIdeal) -> mG(mC \ P)
end

# Residues modulo p^l which, together with the squares, generate
# nrd(O_p^x) modulo 1 + p^l R_p; or :all if that is every unit. Here
# l = v_p(4) + 1, so that 1 + p^l R_p consists of squares (Smertnig-Voight,
# Trans. London Math. Soc. 6 (2019), 53-86, Remark 6.12).
function _local_norm_residues(O::AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}},
                              p::ZZRingElem, l::Int)
  B = elem_in_algebra.(basis(O))
  # An element of O_p is a unit if and only if its reduced norm is (Voight,
  # Quaternion Algebras, Exercise 10.15).
  # At an odd prime, nrd modulo p is a quadratic form over F_p, which takes
  # every nonzero value a if its rank is at least 2: with Q its
  # nondegenerate part, Q - a t^2 is isotropic (ibid., Lemma 12.3.5), so
  # either Q takes the value a or Q is isotropic and then contains a
  # hyperbolic plane (ibid., Lemma 5.4.2), which is universal. If its rank is
  # 1, it takes only squares, nrd(1) being 1.
  if is_odd(p)
    F = GF(p)
    G = _trace_form_gram(algebra(O), basis_matrix(O))
    return rank(map_entries(x -> F(ZZ(x)), G)) >= 2 ? :all : ZZRingElem[]
  end
  # Above 2: the norms of lifts of the units of O/pO, the elements of odd
  # norm, and of 1 + p^i b for a basis b of O; since
  # nrd(1 + p^i x) = 1 + p^i trd(x) modulo p^(i + 1), the latter generate
  # nrd(1 + pO_p) modulo 1 + p^l Z_p.
  q = p^l
  res = Set{ZZRingElem}()
  for c in Iterators.product(ntuple(_ -> 0:1, 4)...)
    n = ZZ(normred(sum(c[i] * B[i] for i in 1:4)))
    is_odd(n) && push!(res, mod(n, q))
  end
  for i in 1:(l - 1), b in B
    push!(res, mod(ZZ(normred(1 + p^i * b)), q))
  end
  return collect(res)
end

function _local_norm_residues(
    O::AlgAssRelOrd{AbsSimpleNumFieldElem, <:Any, <:QuaternionAlgebra},
    P::AbsNumFieldOrderIdeal, l::Int)
  A = algebra(O)
  R = base_ring(O)
  # The rows of B are elements of O whose classes form a basis of O/PO over
  # R/P.
  B = _local_basis_submodule_matrix(basis_pmatrix(O), P)
  _, mF = residue_field(R, P)
  # As over QQ, with pi^i r for r in a basis of R in place of p^i above 2.
  if is_odd(minimum(P))
    G = _trace_form_gram(A, B)
    return rank(map_entries(x -> mF(R(x)), G)) >= 2 ? :all : elem_type(R)[]
  end
  e = [elem_from_mat_row(A, B, i) for i in 1:4]
  Pl = P^l
  Q, OtoQ = StructureConstantAlgebra(O, P * O, P, mF)
  # The residues generate the same group for any uniformizer.
  pi = uniformizer(P)
  res = Set{elem_type(R)}()
  # Lift unit generators of O/PO and take their reduced norms.
  for u in K1(Q; do_units = true)
    push!(res, mod(normred(OtoQ \ u), Pl))
  end
  for i in 1:(l - 1), r in absolute_basis(R), x in e
    push!(res, mod(R(normred(one(A) + elem_in_nf(pi^i * r) * x)), Pl))
  end
  return collect(res)
end

################################################################################
#
#  Types
#
################################################################################

@doc raw"""
    type_set(O::Union{AlgAssAbsOrd, AlgAssRelOrd}) -> Vector

Return representatives of the types of the order $O$ of a quaternion algebra
$A$ over $\mathbf{Q}$ or a number field: one order for each isomorphism class
of orders locally isomorphic to $O$.

If $A$ is not totally definite, $O$ must be an Eichler order.

# Examples

```jldoctest
julia> O = maximal_order(quaternion_algebra_ramified_at(QQ, 97));

julia> length(type_set(O)), length(right_class_set(O))
(5, 8)
```
"""
@attr Vector{typeof(O)} function type_set(O::Union{AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}}, AlgAssRelOrd})
  return _type_set(O)
end

@doc raw"""
    type_number(O::Union{AlgAssAbsOrd, AlgAssRelOrd}) -> Int

Return the number of types of the order $O$, that is, the length of
[`type_set`](@ref).
"""
function type_number(O::Union{AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}}, AlgAssRelOrd})
  return length(type_set(O))
end

# The left orders of the right ideal classes of O run over every type (Voight,
# Quaternion Algebras, Lemma 17.4.13); over QQ one is kept per value of the
# complete isomorphism invariant _class_set_key.
function _type_set(O::AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}})
  _is_totally_definite_quaternion(algebra(O)) || return _type_set_indefinite(O)
  key_of = _class_set_key(O)
  seen = Set{ZZMatrix}()
  types = typeof(O)[]
  for I in right_class_set(O)
    L = left_order(I)
    key = key_of(L)
    key in seen && continue
    push!(seen, key)
    push!(types, L)
  end
  return types
end

function _type_set(
    O::AlgAssRelOrd{AbsSimpleNumFieldElem, <:Any, <:QuaternionAlgebra})
  _is_totally_definite_quaternion(algebra(O)) || return _type_set_indefinite(O)
  return _type_set_definite(O)
end

function _type_set(O::AlgAssRelOrd)
  @req !is_eichler(algebra(O)) "Algebra must be totally definite"
  return _type_set_definite(O)
end

# The same over a number field, comparing left orders by _is_isomorphic.
function _type_set_definite(O::AlgAssRelOrd)
  types = typeof(O)[]
  for I in right_class_set(O)
    L = left_order(I)
    any(S -> _is_isomorphic(L, S), types) || push!(types, L)
  end
  return types
end

# For an indefinite algebra the reduced norm induces a bijection from the
# types of O onto Cl_{G_N(O)} R, the quotient of Cl_{G(O)} R by the reduced
# norms of the normalizers of the completions of O (Voight, Quaternion
# Algebras, Corollary 28.5.10). For an Eichler order these are the squares,
# every element at a ramified prime (Lemma 13.4.9), and pi^e at a prime
# p^e exactly dividing the level, the norm of an Atkin-Lehner element
# (Proposition 23.4.14); compare 28.5.11. The normalizers of other orders are
# not determined here.
function _type_set_indefinite(O::AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}})
  @req _eichler_level_factors(O) !== nothing "Order must be an Eichler order"
  # Cl_{G(O)} Z is trivial: no real place ramifies and O is Eichler.
  return typeof(O)[O]
end

function _type_set_indefinite(
    O::AlgAssRelOrd{AbsSimpleNumFieldElem, <:Any, <:QuaternionAlgebra})
  level = _eichler_level_factors(O)
  @req level !== nothing "Order must be an Eichler order"
  A = algebra(O)
  G, cls = _indefinite_class_group(O)
  normalizer = vcat([2 * g for g in gens(G)],
                    [cls(P) for (P, _) in factor(_reduced_disc(O))
                     if !is_split(A, P)],
                    [cls(P) for (P, e) in level if is_odd(e)])
  Q, mQ = quo(G, normalizer)
  seen = Set{elem_type(Q)}()
  types = typeof(O)[]
  for I in right_class_set(O)
    q = mQ(cls(numerator(normred(I))))
    q in seen && continue
    push!(seen, q)
    push!(types, left_order(I))
  end
  return types
end

function _is_isomorphic(R::T, S::T) where {T <: Union{AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}}, AlgAssRelOrd}}
  # In a totally definite quaternion algebra, R and S are isomorphic if and
  # only if the lattices R and S are isometric with respect to the form
  # (x, y) -> trd(x * conj(y)): Kirschmer, Konstruktive Idealtheorie in
  # Quaternionenalgebren, Diplomarbeit, Universitaet Ulm, 2005, Korollar 4.1.6
  # (for conjugate orders) and Bemerkung 2.6.2 (conjugate means isomorphic, by
  # Skolem-Noether).

  A = algebra(R)
  @assert !is_eichler(A)
  B = basis(A)
  K = base_ring(A)
  M = zero_matrix(K, 4, 4)
  for i in 1:4
    for j in 1:4
      M[i, j] = trred(B[i] * conjugate(B[j]))
    end
  end
  V = quadratic_space(K, M)
  if K isa QQField
    LR = lattice(V, basis_matrix(R))
    LS = lattice(V, basis_matrix(S))
  else
    LR = lattice(V, basis_pmatrix(R))
    LS = lattice(V, basis_pmatrix(S))
  end
  return is_isometric(LR, LS)
end

#    noniso := [];
#
#    for OO in orders do
#        already_seen := false;
#        for Ox in noniso do
#            if IsIsomorphic(OO,Ox) then
#                already_seen := true;
#                break;
#            end if;
#        end for;
#
#        if not already_seen then
#            Append(~noniso, OO);
#        end if;
#    end for;
#    return #noniso;
#end intrinsic;
#

function locally_free_class_group(O::AlgAssRelOrd)
  AA, AAtoA  = restrict_scalars(algebra(O), QQ);
  OO = Hecke.order(AA, preimage.(AAtoA, elem_in_algebra.(absolute_basis(O))))
  return locally_free_class_group(OO)
end

function _stably_free_mass(O)
  return mass(O)//order(locally_free_class_group(O))
end

function _has_stably_free_cancellation(O)
  u = unit_group_modulo_scalars(O)
  return _stably_free_mass(O) == 1//length(u)
end

function _has_locally_free_cancellation(O)
  return order(locally_free_class_group(O)) == length(right_class_set(O))
end

function _zeta_denominator_bound_at_minus_one(K)
  S = lcm(cyclotomic_quadratic_extensions(K))
  # Sort out all possible m such that [F(zeta_m):F] = 2.
  Sdiv = [m for m in divisors(S) if m != 1 && valuation(m, 2) != 1]
  Sdiv = [m for m in Sdiv if all(degree(f) == 2 for (f, _) in factor(K, cyclotomic_polynomial(m)))]
  lden = lcm(ZZ.(Sdiv))
  return lden
end

function _mass_infinity(K::AbsSimpleNumField)
  if false degree(K) == 1
    return QQ(1//12)
  end
  hK = order(class_group(maximal_order(K))[1])
  z = dedekind_zeta_exact(K, -1)
  #@info "" _zeta_denominator_bound_at_minus_one(K)
  #@info "" _denominator_bound(K, -1)
  return QQ(2)^(1-degree(K)) * abs(z) * hK
end
#    L := LSeries(NumberField(F) : Precision := 6 + extra);
#    z := Real(Evaluate(L, -1));
#    tz10 := Log(Lden*Abs(z))/Log(10);
#    if tz10 ge 4 then
#      LSetPrecision(L, Ceiling(tz10) + 3 + extra );
#      z := Real(Evaluate(L, -1));
#    end if;
#    return 2^(1-Degree(F)) * Abs(Round(Lden*z)/Lden) * ClassNumber(F);
#  end if;
#end function;

function _mass_infinity(::QQField)
  return QQ(1//12)
end

#  {Sequence containing all prime powers m = p^e such that [F(zeta_m):F] <= 2}
function cyclotomic_quadratic_extensions(::QQField)
  return ZZRingElem[4, 3]
end

function cyclotomic_quadratic_extensions(F::AbsSimpleNumField)
  d = degree(F)
  OF = maximal_order(F)
  # phi(p^e) divide 2d (draw a diagram)
  P = [ p for p in PrimesSet(2, 2*d + 1) if is_divisible_by(2*d, p - 1)]
  S = [p^(valuation(2*d, p) + 1) for p in P]
  _is_cyclic_ext_quad = function(n)
    # Test the first few primes to rule out impossible ones
    for q in PrimesSet(1, 100)
      if !(gcd(q, n) == 1 && valuation(norm(discriminant(OF)), q) == 0)
        continue
      end
      facq = prime_decomposition(OF, q)
      for (Q,_) in facq
        absN = absolute_norm(Q) % n
        absN in [-1 % n, 1 % n]
        if !(absN in [1, n - 1])
          return false
        end
      end
    end
    return all(degree(f) == 2 for (f,_) in factor(F, cyclotomic_polynomial(n)))
  end
  #    for q in [q : q in [1..100] | IsPrime(q) and Gcd(q,m) eq 1 and
  #                                  Valuation(Norm(Discriminant(Z_F)),q) eq 0] do
  #      qfacts := Decomposition(Z_F,q);
  #      for qq in qfacts do
  #        if Integers(m) ! AbsoluteNorm(qq[1]) notin [Integers(m) | -1,1] then
  #          return false;
  #        end if;
  #      end for;
  #    end for;
  #    return forall{f : f in Factorization(CyclotomicPolynomial(m), F) | Degree(f[1]) eq 2};
  #  end function;
  for i in 1:length(S)
    m = S[i]
    while m > 1 && !_is_cyclic_ext_quad(m)
      m = divexact(m, P[i])
    end
    S[i] = m
  end
  return [m for m in S if m != 1]
end

_reduced_disc(O::AlgAssAbsOrd{<:QuaternionAlgebra}) = sqrt(abs(discriminant(O)))

_reduced_disc(O::AlgAssRelOrd{<:Any, <:Any, <:QuaternionAlgebra}) = is_power(discriminant(O), 2)[2]

@attr QQFieldElem mass(O::AlgAssAbsOrd{<:QuaternionAlgebra}) = _mass(O)

@attr QQFieldElem mass(O::AlgAssRelOrd{<:Any, <:Any, <:QuaternionAlgebra}) = _mass(O)

function _mass(O)
  A = algebra(O)
  F = base_ring(A)
  mass = _mass_infinity(F)
  for (p, e) in factor(_reduced_disc(O))
    #q:= T eq FldFunRat select (#BaseRing(F))^Degree(f[1]) else Norm(f[1]);
    q = norm(p)
    #@info p, e
    #@info q^e
    #@info eichler_invariant(O, p)
    #@info q^e * (1-1//q^2)/(1 - eichler_invariant(O, p)*(1//q))
    #@info p, q^e * (1-1//q^2)/(1 - eichler_invariant(O, p)*(1//q))
    mass *= q^e * (1-1//q^2)/(1 - eichler_invariant(O, p)*(1//q))
  end
  return mass
end

function eichler_invariant(O::AlgAssRelOrd, p::AbsSimpleNumFieldOrderIdeal)
  return _eichler_invariant(O, p)
end

function eichler_invariant(O::AlgAssAbsOrd, p::IntegerUnion)
  return _eichler_invariant(O, p)
end

function _eichler_invariant(O, p)
  A, = quo(O, p*O, p)
  J = radical(A)
  @req dim(J) != 0 "The prime must divide the discriminant"
  if dim(J) == 3
    return 0
  end
  B, = quo(A, J)
  # could be done quicker by testing the basis
  if is_simple(B)
    return -1
  else
    return 1
  end
end

@doc raw"""
    is_eichler(O::Union{AlgAssAbsOrd, AlgAssRelOrd}) -> Bool

Return whether the order $O$ of a quaternion algebra is an Eichler order, that
is, the intersection of two maximal orders.
"""
function is_eichler(O::Union{AlgAssAbsOrd, AlgAssRelOrd})
  A = algebra(O)
  @req A isa QuaternionAlgebra "Order must be an order of a quaternion algebra"
  return _eichler_level_factors(O) !== nothing
end

@doc raw"""
    eichler_level(O::AlgAssAbsOrd{<:QuaternionAlgebra}) -> ZZRingElem
    eichler_level(O::AlgAssRelOrd{<:Any, <:Any, <:QuaternionAlgebra})
      -> AbsNumFieldOrderIdeal

Return the level of the Eichler order $O$ of a quaternion algebra $A$ over
$K$: the ideal $M$ of the ring of integers of $K$, coprime to the discriminant
$D$ of $A$, with $\operatorname{discrd}(O) = DM$ [Voi21](@cite), 23.4.19. Over
$\mathbf{Q}$ it is returned as a positive integer.

An `ArgumentError` is thrown if $O$ is not an Eichler order, see
[`is_eichler`](@ref).

# Examples

The order of the matrices $\begin{pmatrix} a & b \\ 6c & d \end{pmatrix}$, with
$a, b, c, d \in \mathbf{Z}$, in $M_2(\mathbf{Q}) \cong (1, 1)_{\mathbf{Q}}$,
spanned by the matrix units $(1 \pm i)/2$, $(j + k)/2$ and $6$ times
$(j - k)/2$:

```jldoctest
julia> A = quaternion_algebra(QQ, 1, 1);

julia> e, i, j, k = basis(A);

julia> h = QQ(1, 2);

julia> O = order(A, [h * (e + i), h * (e - i), h * (j + k), 3 * (j - k)]);

julia> eichler_level(O)
6

julia> eichler_level(maximal_order(A))
1
```
"""
function eichler_level(O::AlgAssAbsOrd{<:QuaternionAlgebra})
  f = _eichler_level_factors(O)
  @req f !== nothing "Order must be an Eichler order"
  return prod((p^e for (p, e) in f); init = one(ZZ))
end

function eichler_level(O::AlgAssRelOrd{<:Any, <:Any, <:QuaternionAlgebra})
  f = _eichler_level_factors(O)
  @req f !== nothing "Order must be an Eichler order"
  return prod((p^e for (p, e) in f); init = 1 * base_ring(O))
end

# The pairs (p, e) with p^e exactly dividing the level of the order O of a
# quaternion algebra A, or nothing if O is not an Eichler order. O is Eichler
# at p if and only if it is maximal at p, which where A ramifies means that p
# divides discrd(O) once, or it is residually split there (Voight, Quaternion
# Algebras, Lemma 24.3.6); then A splits at p, and p^e, exactly dividing
# discrd(O), exactly divides the level (23.4.19).
function _eichler_level_factors(O::Union{AlgAssAbsOrd, AlgAssRelOrd})
  f = _non_maximal_factors(O)
  all(((p, _),) -> eichler_invariant(O, p) == 1, f) || return nothing
  return f
end

# The primes at which the order O of a quaternion algebra is not Eichler; see
# _eichler_level_factors.
function _non_eichler_primes(O::Union{AlgAssAbsOrd, AlgAssRelOrd})
  return [p for (p, _) in _non_maximal_factors(O)
          if eichler_invariant(O, p) != 1]
end

# The pairs (p, e) with p^e exactly dividing discrd(O) at which O is not
# maximal: those where the quaternion algebra splits, and those where it
# ramifies with e > 1.
function _non_maximal_factors(O::Union{AlgAssAbsOrd, AlgAssRelOrd})
  A = algebra(O)
  return [(p, e) for (p, e) in factor(_reduced_disc(O))
          if e > 1 || is_split(A, p)]
end

################################################################################
#
#  Classification
#
################################################################################

function _norms_of_ramified_primes(A::QuaternionAlgebra)
  O = maximal_order(A)
  return sort!([p isa ZZRingElem ? abs(p) : absolute_norm(p) for (p, _) in factor(discriminant(O))])
end

function _finger_print(O::Union{AlgAssAbsOrd, AlgAssRelOrd})
  A = algebra(O)
  K = base_ring(A)
  return degree(K), discriminant(maximal_order(K)), collect(coefficients(defining_polynomial(K))), _norms_of_ramified_primes(A), absolute_norm(_reduced_disc(O)), mass(O)
end

const degree_ranges = [1:40, 41:249, 250:309, 310:368, 369:373, 374:375]

# fp created with
# open("fp", "w") do io; for i in 1:length(fp); for x in fp[i]; print(io, ",", Hecke._stringify(x)); end; println(io); end; end;

function _read_fingerprint(;range = 1:375)
  res = Vector{Tuple{Int, ZZRingElem, Vector{Int}, Vector{Int}, Int, QQFieldElem}}(undef, length(range))
  j = 1
  for (i, l) in enumerate(readlines(joinpath(@__DIR__, "SVfingerprint.dat")))
    if !(i in range)
      continue
    end
    io = IOBuffer(l)
    _, deg = _parse(Int, io)
    _, discOK = _parse(ZZRingElem, io)
    _, coeffs = _parse(Vector{Int}, io)
    _, normsram = _parse(Vector{Int}, io)
    _, normdisc = _parse(Int, io)
    b, mas = _parse(QQFieldElem, io)
    res[j] = deg, discOK, coeffs, normsram, normdisc, mas
    j += 1
  end
  return res
end

# true => order not in the database
# false => order maybe in the database
function _order_not_in_db(O::AlgAssRelOrd)
  A = algebra(O)
  K = base_ring(O)
  if degree(K) > 6
    return true
  end
  fps = _read_fingerprint(; range = degree_ranges[degree(K)])
  length(fps) == 0 && return true
  filter!(x -> x[2] == discriminant(maximal_order(K)), fps)
  length(fps) == 0 && return true
  filter!(x -> x[4] == _norms_of_ramified_primes(A), fps)
  length(fps) == 0 && return true
  filter!(x -> x[5] == absolute_norm(_reduced_disc(O)), fps)
  length(fps) == 0 && return true
  filter!(x -> x[6] == mass(O), fps)
  return length(fps) == 0
end

function _order_not_in_db(O::AlgAssAbsOrd)
  A = algebra(O)
  fps = _read_fingerprint(; range = degree_ranges[1])
  filter!(x -> x[4] == _norms_of_ramified_primes(A), fps)
  length(fps) == 0 && return true
  filter!(x -> x[5] == abs(_reduced_disc(O)), fps)
  length(fps) == 0 && return true
  filter!(x -> x[6] == mass(O), fps)
  return length(fps) == 0
end

function has_stably_free_cancellation(O::Union{AlgAssAbsOrd{<:QuaternionAlgebra}, AlgAssRelOrd{<:Any, <:Any, <:QuaternionAlgebra}})
  if _order_not_in_db(O)
    return false
  end
  return _has_stably_free_cancellation(O)
end

function has_locally_free_cancellation(O::Union{AlgAssAbsOrd{<:QuaternionAlgebra}, AlgAssRelOrd{<:Any, <:Any, <:QuaternionAlgebra}})
  if _order_not_in_db(O)
    return false
  end
  return _has_locally_free_cancellation(O)
end
