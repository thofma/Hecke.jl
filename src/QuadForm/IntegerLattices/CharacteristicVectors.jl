# return all characteristic vectors up to sign
# unfortunately still to many for a fast graph hash
# at least in higher rank
# the idea follows https://arxiv.org/pdf/2004.14022
"""
    _characteristic_vectors(L::ZZLat) -> Vector{ZZMatrix}

Return a set of characteristic vectors of ``L`` up to sign.

We follow ideas of Sikirić, Haensch, Voight and van Woerden [SHVW20](@cite).

!!! note
    We do not give any guarantees that the characteristic vector set stays the same
    between different versions of Hecke.
"""
function _characteristic_vectors(L::ZZLat)
  L = lattice(rational_span(L))
  S1, P1, v1 = _shortest_vectors_sublattice(L; check=false)
  cvL = v1
  A = abelian_group(change_base_ring(ZZ, coordinates(basis_matrix(S1), P1)))
  done = Set{FinGenAbGroupElem}()
  for a in A
    -a in done && continue
    iszero(a) && continue
    push!(done, a)
    v = coordinates(a.coeff*basis_matrix(P1), S1)[1,:]
    tmp = [matrix(ZZ, 1, degree(S1), (v - j)*basis_matrix(S1)) for j in _closest_vectors(S1, v, Int; check=false)[2]]
    # if `a` is 2-torsion, then its coset is preserved by negation and the
    # vectors of minimal norm in it come in pairs `w`, `-w`
    iszero(a + a) && unique!(map!(_canonicalize!, tmp, tmp))
    append!(cvL, tmp)
  end
  if rank(S1) == rank(L)
    @hassert :Lattice 1 isone(hnf(reduce(vcat, cvL))[1:rank(L),:])
    return cvL
  end
  proj2 = orthogonal_projection(ambient_space(L), basis_matrix(P1); check=false)
  # a reduced basis speeds up the closest vector problems in the recursion
  L2 = lll(proj2(L))
  # `L2` spans the orthogonal complement of `P1`, so the projection onto the
  # orthogonal complement of `L2` is the projection complementary to `proj2`
  pr1 = one(proj2.matrix) - proj2.matrix
  P_Z = change_base_ring(ZZ, solve(basis_matrix(L2), proj2.matrix; side=:left))
  ctx = solve_init(P_Z)
  # the differences `w - j` only depend on `w` modulo `P1`, so we solve each
  # closest vector problem only once
  closest = Dict{Vector{QQFieldElem},Vector{Vector{QQFieldElem}}}()
  # recurse
  for a in _characteristic_vectors(L2)
    aL = a*basis_matrix(L2)
    # `L` has the identity as basis matrix, so `aL` lies in `L` precisely if
    # its entries are integral
    if isone(denominator(aL))
      push!(cvL, change_base_ring(ZZ, aL))
      continue
    end
    # a vector in L projecting to a
    vL = solve(ctx, a; side=:left)
    w_amb = vL * pr1
    # `w` is not integral: otherwise `w_amb` would lie in `P1` and hence `aL`
    # in `L`, which was excluded above
    w = coordinates(w_amb[1,:], P1)
    cv = get!(() -> [w - j for j in _closest_vectors(P1, w, Int; check=false)[2]], closest, [x - floor(x) for x in w])
    tmp = [change_base_ring(ZZ, aL + matrix(QQ, 1, length(w), j)*basis_matrix(P1)) for j in cv]
    append!(cvL, tmp)
  end
  @assert all(rank(L) == ncols(i) for i in cvL)
  @hassert :Lattice 1 isone(hnf(reduce(vcat, cvL))[1:rank(L),:])
  return cvL
end


# for testing purposes
_reduce_characteristic_vectors(cv_set::Vector{ZZMatrix}, L::ZZLat) = _reduce_characteristic_vectors(_convert_cv_set_to_int(cv_set, _integral_split_gram(L)[1]), L)

function _reduce_characteristic_vectors(cv_set::Vector{Matrix{Int}}, L::ZZLat)
  gram, d = _integral_split_gram(L)
  @assert isone(d)
  # the fundamental roots of `L`, already in the coordinates of `L`
  _, components = _root_lattice_recognition_fundamental(L)
  A_lat = reduce(vcat, components; init=zero_matrix(ZZ, 0, rank(L)))
  v_i = Matrix{Int}(undef, 1, number_of_columns(gram))
  t_i = Matrix{Int}(undef, number_of_rows(gram), 1)
  w_i = Matrix{Int}(undef, 1, 1)
  tmp = ZZ(0)
  gram_int = _int_matrix_with_overflow(gram, tmp)
  A_lat_int = _int_matrix_with_overflow(A_lat, tmp)
  fundamental_roots = [reshape(A_lat_int[i, :], :, 1) for i in 1:number_of_rows(A_lat_int)]
  res::Vector{Matrix{Int}} = []
  for v in cv_set
    AbstractAlgebra.LinearAlgebra.mul!(v_i, v, gram_int)
    AbstractAlgebra.LinearAlgebra.mul!(w_i, v_i, AbstractAlgebra.LinearAlgebra.transpose!(t_i, v))
    if w_i[1] == 1 || w_i[1] == 2
      continue
    end
    in_chamber = true
    for f_root in fundamental_roots
      AbstractAlgebra.LinearAlgebra.mul!(w_i, v_i, f_root)
      if w_i[1] < 0
        in_chamber = false
        break
      end
    end
    if in_chamber
      push!(res, v)
    end
  end
  for f_root in fundamental_roots
    push!(res, f_root')
  end
  return res
end

function _convert_cv_set_to_int(cv_set::Vector{ZZMatrix}, gram::ZZMatrix)
  tmp = ZZ(0)
  n = ZZ(0)
  tmp1 = zero_matrix(ZZ, 1, number_of_columns(gram))
  tmp2 = zero_matrix(ZZ, number_of_rows(gram), 1)
  tmp3 = zero_matrix(ZZ, 1, 1)
  for v in cv_set
    tmp1 = mul!(tmp1, v, gram)
    tmp3 = mul!(tmp3, tmp1, transpose!(tmp2, v))
    n = max(n, tmp3[1])
  end
  # we use Cauchy-Schwarz to check if char vector inner products are small enough to be converted to Int.
  # As we need at least w_max+1 and w_max+2 weights further, we need to lower bound by -2.
  if n-2 < ZZ(typemax(Int))
    cv_set_int = [_int_matrix_with_overflow(v, tmp) for v in cv_set]
  else
    throw(OverflowError("The characteristic vectors have to large inner products to be converted to Int."))
  end
  return cv_set_int
end

################################################################################
#
#  Minuscule vectors of root lattices
#
################################################################################

# Let `R` be a root lattice with a fixed fundamental system of roots
# `a_1,...,a_n` and let `c` be a class of the discriminant group `R^vee/R`.
# The vectors of minimal norm of `c` lying in the closed fundamental Weyl
# chamber are called the minuscule vectors of `c`. Since the Weyl group `W(R)`
# acts trivially on `R^vee/R` and the closed fundamental chamber is a
# fundamental domain for its action, they represent the vectors of minimal
# norm of `c` up to the action of `W(R)`. Solving a closest vector problem in
# `R` for a vector of `R^vee` therefore amounts to a table lookup, as long as
# we are only interested in the solutions up to the Weyl group.
#
# We describe a vector `v` of `R^vee` by its weight coordinates
# `g = (v.a_1,...,v.a_n)` in `ZZ^n`, that is, if a_1',...,a_n' is the dual basis then g = sum_i (v.a_i) a_i'
# Two such vectors lie in the same class of
# `R^vee/R` if and only if they have the same `g*adj mod d`, where `d` is the
# order of `R^vee/R` and `adj = d*C^-1` for `C` the Cartan matrix, that is to
# say the gram matrix of `a_1,...,a_n`.
struct _MinusculeTable
  d::Int                                                    # order of `R^vee/R`
  adj::Matrix{Int}                                          # `d*C^-1`
  data::Dict{Vector{Int},Tuple{Vector{Int},Rational{Int}}}  # class -> minuscule vector and its norm
end

_minuscule_class(g::AbstractVector{Int}, adj::Matrix{Int}, d::Int) = Int[mod(sum(g[k]*adj[k, j] for k in 1:length(g)), d) for j in 1:length(g)]

# The minuscule table of the irreducible root lattice of type `(t, k)`. In the
# weight coordinates above the fundamental weight `omega_i` is the `i`-th
# standard basis vector, and every non-trivial class of `R^vee/R` is
# represented by exactly one `omega_i` with `i` a minuscule node, that is to
# say a node whose coefficient in the highest root is one. So the minuscule
# vectors are the standard basis vectors of the minuscule nodes together with
# the zero vector for the trivial class, and all we have to record here is `d`
# and `adj`. The numbering of the nodes is the one of `root_lattice`, in which
# the diagram of `:D` is `1 - 3 - 4 - ... - k` with `2` attached to `3`, and
# the one of `:E` is `1 - 2 - ... - (k-1)` with `k` attached to `3`.
function _minuscule_table(t::Symbol, k::Int)
  if t === :A
    d = k + 1
    adj = Int[min(i, j)*(k + 1 - max(i, j)) for i in 1:k, j in 1:k]
  elseif t === :D && k >= 4
    # `1` and `2` are the spin nodes, attached to the tail `3 - 4 - ... - k`
    d = 4
    adj = zeros(Int, k, k)
    for i in 3:k, j in 3:k
      adj[i, j] = 4*(k + 1 - max(i, j))
    end
    for i in 1:2, j in 3:k
      adj[i, j] = adj[j, i] = 2*(k + 1 - j)
    end
    adj[1, 1] = adj[2, 2] = k
    adj[1, 2] = adj[2, 1] = k - 2
  elseif t === :E && k == 6
    d = 3
    adj = Int[4  5  6  4  2  3;
              5 10 12  8  4  6;
              6 12 18 12  6  9;
              4  8 12 10  5  6;
              2  4  6  5  4  3;
              3  6  9  6  3  6]
  elseif t === :E && k == 7
    d = 2
    adj = Int[4  6  8  6  4  2  4;
              6 12 16 12  8  4  8;
              8 16 24 18 12  6 12;
              6 12 18 15 10  5  9;
              4  8 12 10  8  4  6;
              2  4  6  5  4  3  3;
              4  8 12  9  6  3  7]
  elseif t === :E && k == 8
    d = 1
    adj = Int[ 4  7 10  8  6  4  2  5;
               7 14 20 16 12  8  4 10;
              10 20 30 24 18 12  6 15;
               8 16 24 20 15 10  5 12;
               6 12 18 15 12  8  4  9;
               4  8 12 10  8  6  3  6;
               2  4  6  5  4  3  2  3;
               5 10 15 12  9  6  3  8]
  else
    error("($t, $k) is not an irreducible root lattice of type ADE")
  end
  marks = highest_root(t, k)
  data = Dict{Vector{Int},Tuple{Vector{Int},Rational{Int}}}(zeros(Int, k) => (zeros(Int, k), 0//1))
  for i in 1:k
    isone(marks[1, i]) || continue
    w = zeros(Int, k)
    w[i] = 1
    data[_minuscule_class(w, adj, d)] = (w, adj[i, i]//d)
  end
  @assert length(data) == d
  return _MinusculeTable(d, adj, data)
end

# The tables of the irreducible components of a root lattice, the components
# being given by their ADE `types` and `ranges`. The table of a component
# depends only on its ADE type, since its fundamental roots come out of
# `_root_lattice_recognition_fundamental` in the standard numbering, so that
# the Cartan matrix of a component of type `(t, k)` is the one of
# `root_lattice(t, k)`.
function _minuscule_tables_of(types::Vector{Tuple{Symbol,Int}}, ranges::Vector{UnitRange{Int}})
  return Tuple{UnitRange{Int},_MinusculeTable}[(r, _minuscule_table(t...)) for (t, r) in zip(types, ranges)]
end

# The weight coordinates of the minuscule vector of the class of the vector
# with weight coordinates `g`, together with its norm. Both the closed
# fundamental chamber and the discriminant group are direct products over the
# irreducible components, so that we may work component by component.
function _minuscule_vector(D::Vector{Tuple{UnitRange{Int},_MinusculeTable}}, g::ZZMatrix)
  gd = zeros(Int, ncols(g))
  nrm = zero(Rational{Int})
  for (r, t) in D
    w, s = t.data[_minuscule_class(Int[Int(mod(g[1, j], t.d)) for j in r], t.adj, t.d)]
    gd[r] = w
    nrm += s
  end
  return gd, nrm
end

# The vector of minimal norm of the coset `v + R` lying in the closed
# fundamental chamber, where `g` are the weight coordinates of the vector `v`
# and `gd` those of the minuscule vector of its class. The difference lies in
# `R` and has coordinates `(gd - g)*C^-1` with respect to the fundamental
# roots, so in the coordinates of `L` it is `(gd - g)*dweights//dd` for
# `dweights` as in `_dual_weights`.
function _minuscule_translate(v::ZZMatrix, g::ZZMatrix, gd::Vector{Int}, dweights::ZZMatrix, dd::Int)
  return v + divexact((matrix(ZZ, 1, length(gd), gd) - g)*dweights, dd)
end

# `dd*C^-1*roots` for `dd` the least common multiple of the `d` of the
# components, that is to say `dd` times the fundamental weights of `R` in the
# coordinates of `L`. We assemble it from the `adj` of the components rather
# than inverting the Cartan matrix.
function _dual_weights(D::Vector{Tuple{UnitRange{Int},_MinusculeTable}}, roots::ZZMatrix)
  dd = reduce(lcm, t.d for (_, t) in D)
  A = block_diagonal_matrix(ZZMatrix[matrix(ZZ, div(dd, t.d)*t.adj) for (_, t) in D])
  return A*roots, dd
end

################################################################################
#
#  Reduced characteristic vectors
#
################################################################################

# Return the reduced characteristic vector set of `L`, that is to say the
# fundamental roots of `L` together with the characteristic vectors of norm
# different from 1 and 2 lying in the closed fundamental Weyl chamber.
# The roots of length 2 span the root sublattice `R` of `L`,
# and all closest vector problems occurring in `_characteristic_vectors` are
# closest vector problems in `R` for vectors of `R^vee`. Their solutions are
# the minuscule vectors of `R` up to the action of the Weyl group of `R`, and
# these are all we need here: the Weyl group is contained in the orthogonal
# group of `L`, so keeping only the solutions in the closed fundamental
# chamber loses no information. Note that all the vectors we produce have norm
# bigger than 2: they are non-zero and none of them is a root, since a root
# lies in `R` and has trivial class in `R^vee/R`.
# `L` must be positive definite and not represent 1
function _reduced_characteristic_vectors_without_1(L::ZZLat)
  n = rank(L)
  gram, d = _integral_split_gram(L)
  @assert isone(d)
  # the fundamental roots of `L`, in the coordinates of `L` and grouped into
  # the irreducible components of the root sublattice
  types, components = _root_lattice_recognition_fundamental(L)
  if is_empty(components)
    # `L` has no vector of norm 1 or 2, so there is nothing to reduce: the
    # closed fundamental chamber is all of the ambient space.
    # `_characteristic_vectors` returns the characteristic vectors only up to
    # sign; we need all of them for the result to be canonical
    cv = _characteristic_vectors(L)
    return _convert_cv_set_to_int(append!(cv, ZZMatrix[-v for v in cv]), gram)
  end
  roots = reduce(vcat, components; init=zero_matrix(ZZ, 0, n))
  nr = nrows(roots)
  ranges = UnitRange{Int}[]
  k = 0
  for c in components
    push!(ranges, (k+1):(k+nrows(c)))
    k += nrows(c)
  end
  cartan = roots*gram*transpose(roots)
  D = _minuscule_tables_of(types, ranges)
  dweights, dd = _dual_weights(D, roots)
  # `v*gram_roots` are the weight coordinates of the vector `v` of `L`
  gram_roots = gram*transpose(roots)
  res = ZZMatrix[roots[i:i, :] for i in 1:nr]

  # the vectors of minimal norm of the non-trivial cosets of `P/R`, where `P`
  # is the primitive closure of `R` in `L`, are characteristic vectors
  BP = saturate(roots)
  cosets = ZZMatrix[zero_matrix(ZZ, 1, n)]
  # the square of the index of `R` in `P`
  if !isone(divexact(det(cartan), det(BP*gram*transpose(BP))))
    for a in abelian_group(solve(BP, roots; side=:left))
      is_zero(a) && continue
      push!(cosets, a.coeff*BP)
    end
  end
  for v in cosets[2:end]
    g = v*gram_roots
    push!(res, _minuscule_translate(v, g, _minuscule_vector(D, g)[1], dweights, dd))
  end
  nr == n && return _convert_cv_set_to_int(res, gram)

  # the remaining characteristic vectors are the lifts of minimal norm of the
  # characteristic vectors of the projection `L2` of `L` to the orthogonal
  # complement of `R`
  # The projection onto the orthogonal complement of `R`, which is the one of
  # `P` since the two span the same space. It is `1 - G*roots^t*cartan^-1*roots`,
  # and `cartan^-1` is `dweights` divided by `dd`, so there is nothing to
  # invert. `L0` has the identity as basis matrix, so `pr` is at the same time
  # the matrix of a generating system of `L2`.
  L0 = lattice(rational_span(L))
  pr = identity_matrix(QQ, n) - change_base_ring(QQ, gram_roots*dweights)*QQ(1, dd)
  L2 = lattice(ambient_space(L0), pr; isbasis=false, check=false)
  PZ = change_base_ring(ZZ, solve(basis_matrix(L2), pr; side=:left))
  cv2 = _characteristic_vectors(L2)
  # `_characteristic_vectors` returns the characteristic vectors only up to
  # sign; we need all of them for the result to be canonical
  cv2 = append!(cv2, ZZMatrix[-a for a in cv2])
  ctx = solve_init(PZ)
  gs = Vector{ZZMatrix}(undef, length(cosets))
  gds = Vector{Vector{Int}}(undef, length(cosets))
  ns = Vector{Rational{Int}}(undef, length(cosets))  #squared norms
  for a in cv2
    # the lifts of `a` are the vectors of `vL + P`; their norm is the norm of
    # `a` plus the norm of the part in `P`, so it is minimal exactly for the
    # cosets of `P/R` with the shortest minuscule vectors
    # brute force this here
    vL = solve(ctx, a; side=:left)
    for (i, c) in enumerate(cosets)
      gs[i] = (vL + c)*gram_roots
      gds[i], ns[i] = _minuscule_vector(D, gs[i])
    end
    best = minimum(ns)
    for (i, c) in enumerate(cosets)
      ns[i] == best || continue
      push!(res, _minuscule_translate(vL + c, gs[i], gds[i], dweights, dd))
    end
  end
  return _convert_cv_set_to_int(res, gram)
end

# Return the fundamental roots of `L` together with the characteristic vectors
# of norm different from 1 and 2 lying in the closed fundamental Weyl chamber.
function _reduced_characteristic_vectors(L::ZZLat)
  if !iseven(L)     # splitt off ones if there are any
    ones = ZZMatrix[matrix(ZZ, 1, rank(L), v) for (v, _) in short_vectors(L, 1, 1, Int; check=false)]
    if !is_empty(ones)
      # the vectors of norm one are pairwise orthogonal and split off `L`, so the
      # remaining characteristic vectors are those of the orthogonal complement
      # `M` of the lattice they span; of the vectors of norm one themselves we
      # keep one of each pair
      N = lattice_in_same_ambient_space(L, change_base_ring(QQ, reduce(vcat, ones))*basis_matrix(L))
      M = orthogonal_submodule(L, N)
      if !is_zero(rank(M))
        B = change_base_ring(ZZ, solve(basis_matrix(L), basis_matrix(M); side=:left))
        append!(ones, ZZMatrix[matrix(ZZ, v)*B for v in _reduced_characteristic_vectors(M)])
      end
      return _convert_cv_set_to_int(ones, _integral_split_gram(L)[1])
    end
  end
  return _reduced_characteristic_vectors_without_1(L)
end
