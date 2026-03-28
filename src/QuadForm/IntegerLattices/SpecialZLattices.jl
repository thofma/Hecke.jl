################################################################################
#
#  Hyperbolic plane
#
################################################################################

@doc raw"""
    integer_lattice(S::Symbol, n::RationalUnion = 1) -> ZZlat

Given `S = :H` or `S = :U`, return a $\mathbb Z$-lattice admitting $n*J_2$ as
Gram matrix in some basis, where $J_2$ is the 2-by-2 matrix with 0's on the
main diagonal and 1's elsewhere.
"""
function integer_lattice(S::Symbol, n::RationalUnion = 1)
  @req S === :H || S === :U "Only available for the hyperbolic plane"
  gram = scalar_matrix(2, n)
  reverse_cols!(gram)
  return integer_lattice(; gram)
end

@doc raw"""
    hyperbolic_plane_lattice(n::RationalUnion = 1) -> ZZLat

Return the hyperbolic plane with intersection form of scale `n`, that is,
the unique (up to isometry) even unimodular hyperbolic $\mathbb Z$-lattice
of rank 2, rescaled by `n`.

# Examples

```jldoctest
julia> L = hyperbolic_plane_lattice(6);

julia> gram_matrix(L)
[0   6]
[6   0]

julia> L = hyperbolic_plane_lattice(ZZ(-13));

julia> gram_matrix(L)
[  0   -13]
[-13     0]
```
"""
hyperbolic_plane_lattice(n::RationalUnion = 1) = integer_lattice(:H, n)

################################################################################
#
# The 23 holy constructions of the Leech lattice
#
################################################################################


@doc raw"""
    leech_lattice() -> ZZLat

Return the Leech lattice.
"""
function leech_lattice()
  R = integer_lattice(gram=2*identity_matrix(ZZ,24))
  N = maximal_even_lattice(R) # niemeier lattice
  return leech_lattice(N)[1]
end

@doc raw"""
    leech_lattice(niemeier_lattice::ZZLat) -> ZZLat, QQMatrix, Int

Return a triple `L, v, h` where `L` is the Leech lattice.

L is an `h`-neighbor of the Niemeier lattice `N` with respect to `v`.
This means that `L / L ∩ N  ≅ ℤ / h ℤ`.
Here `h` is the Coxeter number of the Niemeier lattice.

This implements the 23 holy constructions of the Leech lattice in [CS99](@cite).

# Examples
```jldoctest leech
julia> R = integer_lattice(gram=2 * identity_matrix(ZZ, 24));

julia> N = maximal_even_lattice(R); # Some Niemeier lattice

julia> minimum(N)
2

julia> det(N)
1

julia> L, v, h = leech_lattice(N);

julia> minimum(L)
4

julia> det(L)
1

julia> h == index(L, intersect(L, N))
true

```

We illustrate how the Leech lattice is constructed from `N`, `h` and `v`.

```jldoctest leech
julia> Zmodh, _ = residue_ring(ZZ, h);

julia> V = ambient_space(N);

julia> vG = map_entries(x->Zmodh(ZZ(x)), inner_product(V, v, basis_matrix(N)));

julia> LN = transpose(lift(Hecke.kernel(vG; side = :right)))*basis_matrix(N); # vectors whose inner product with `v` is divisible by `h`.

julia> M = lattice(V, LN) + h*N;

julia> M == intersect(L, N)
true

julia> M + lattice(V, 1//h * v) == L
true

```
"""
function leech_lattice(niemeier_lattice::ZZLat)
  # construct the leech lattice from one of the 23 holy constructions in SPLAG
  # we follow a mix of Ebeling and SPLAG
  # there seem to be some signs wrong in Ebeling?
  N = niemeier_lattice
  @req rank(N)==24 && norm(N)==2 && scale(N)==1 && det(N)==1 && is_definite(N) "not a Niemeier lattice"
  # figure out which Niemeier lattice it is
  V = ambient_space(N)
  ADE, ade, RR = root_lattice_recognition_fundamental(N)
  rank(ADE)==24 || error("not a niemeier lattice")
  F = basis_matrix(ADE)
  for i in 1:length(ade)
    F = vcat(F, -highest_root(ade[i]...) * basis_matrix(RR[i]))
  end
  rho = sum(_weyl_vector(r) for r in RR)
  h = coxeter_number(ade[1]...)
  # sanity checks
  @hassert :Lattice 1 inner_product(V, rho, rho) == 2 * h * (h+1)
  @hassert :Lattice 1 all(h == coxeter_number(i...) for i in ade)
  rhoB = solve(basis_matrix(N), rho; side = :left)
  v = QQ(1, h) * transpose(rhoB)
  A = integer_lattice(gram=gram_matrix(N))
  c = QQ(2 + 2//h)
  vv = vec(collect(v))
  sv = [matrix(QQ, 1, 24, vv - i)*basis_matrix(N) for (i, _) in Hecke.close_vectors(A, vv, c, c, check=false)]
  @hassert :Lattice 1 all(inner_product(V, i, i)==(2 + 2//h) for i in sv)
  @hassert :Lattice 1 length(sv)^2 == abs(det(ADE))
  G = reduce(vcat, sv)
  FG = vcat(F, G)
  K = transpose(kernel(matrix(ZZ, ones(Int, 1, nrows(FG))), side = :right))
  B = change_base_ring(QQ, K) * FG
  B = _hnf!_integral(FakeFmpqMat(B))
  B = QQ(1, B.den) * change_base_ring(QQ, B.num[end-23:end, :])
  leech_lattice = lattice(V, B)
  leech_lattice = lll(leech_lattice) # make it a bit prettier
  # confirm computation
  @hassert :Lattice 1 rank(B)==24
  @hassert :Lattice 1 scale(leech_lattice)==1 && norm(leech_lattice)==2
  @hassert :Lattice 1 det(leech_lattice)==1
  @hassert :Lattice 1 minimum(leech_lattice)==4

  # figure out the glue vector
  T = torsion_quadratic_module(leech_lattice, intersect(leech_lattice, N))
  @assert length(gens(T))==1 "something is wrong"
  w = transpose(matrix(lift(gens(T)[1])))

  return leech_lattice, h*w, h
end

###############################################################################
#
#  Hyperkaehler lattices
#
###############################################################################

@doc raw"""
    k3_lattice()

Return the integer lattice corresponding to the Beauville-Bogomolov-Fujiki
form associated to a K3 surface.

# Examples
```jldoctest
julia> L = k3_lattice();

julia> is_unimodular(L)
true

julia> signature_tuple(L)
(3, 0, 19)
```
"""
function k3_lattice()
  U = QQ[0 1; 1 0]
  E8 = -_root_lattice_E(8)
  return integer_lattice(; gram = diagonal_matrix(U, U, U, E8, E8))
end

@doc raw"""
    mukai_lattice(S::Symbol = :K3; extended::Bool = false)

Return the (extended) Mukai lattice.

If `S == :K3`, it returns the (extended) Mukai lattice associated to
hyperkaehler manifolds which are deformation equivalent to a moduli space
of stable sheaves on a K3 surface.

If `S == :Ab`, it returns the (extended) Mukai lattice associated to
hyperkaehler manifolds which are deformation equivalent to a moduli space
of stable sheaves on an abelian surface.

# Examples
```jldoctest
julia> L = mukai_lattice();

julia> genus(L)
Genus symbol for integer lattices
Signatures: (4, 0, 20)
Local symbol:
  Local genus symbol at 2: 1^24

julia> L = mukai_lattice(; extended = true);

julia> genus(L)
Genus symbol for integer lattices
Signatures: (5, 0, 21)
Local symbol:
  Local genus symbol at 2: 1^26

julia> L = mukai_lattice(:Ab);

julia> genus(L)
Genus symbol for integer lattices
Signatures: (4, 0, 4)
Local symbol:
  Local genus symbol at 2: 1^8

julia> L = mukai_lattice(:Ab; extended = true);

julia> genus(L)
Genus symbol for integer lattices
Signatures: (5, 0, 5)
Local symbol:
  Local genus symbol at 2: 1^10
```
"""
function mukai_lattice(S::Symbol = :K3; extended::Bool = false)
  @req S in [:K3, :Ab] "Wrong symbol"
  U = QQ[0 1; 1 0]
  if S == :Ab
    extended && return integer_lattice(; gram = diagonal_matrix(U, U, U, U, U))
    return integer_lattice(; gram = diagonal_matrix(U, U, U, U))
  end

  E8 = -_root_lattice_E(8)
  !extended && return integer_lattice(; gram = diagonal_matrix(U, U, U, U, E8, E8))
  return integer_lattice(; gram = diagonal_matrix(U, U, U, U, U, E8, E8))
end

@doc raw"""
    hyperkaehler_lattice(S::Symbol; n::Int = 2)

Return the integer lattice corresponding to the Beauville-Bogomolov-Fujiki
form on a hyperkaehler manifold whose deformation type is determined by `S`
and `n`.

- If `S == :K3` or `S == :Kum`, then `n` must be an integer bigger than 2;
- If `S == :OG6` or `S == :OG10`, the value of `n` has no effect.

# Examples
```jldoctest
julia> L = hyperkaehler_lattice(:Kum; n = 3)
Integer lattice of rank 7 and degree 7
with gram matrix
[0   1   0   0   0   0    0]
[1   0   0   0   0   0    0]
[0   0   0   1   0   0    0]
[0   0   1   0   0   0    0]
[0   0   0   0   0   1    0]
[0   0   0   0   1   0    0]
[0   0   0   0   0   0   -8]

julia> L = hyperkaehler_lattice(:OG6)
Integer lattice of rank 8 and degree 8
with gram matrix
[0   1   0   0   0   0    0    0]
[1   0   0   0   0   0    0    0]
[0   0   0   1   0   0    0    0]
[0   0   1   0   0   0    0    0]
[0   0   0   0   0   1    0    0]
[0   0   0   0   1   0    0    0]
[0   0   0   0   0   0   -2    0]
[0   0   0   0   0   0    0   -2]

julia> L = hyperkaehler_lattice(:OG10);

julia> genus(L)
Genus symbol for integer lattices
Signatures: (3, 0, 21)
Local symbols:
  Local genus symbol at 2: 1^-24
  Local genus symbol at 3: 1^-23 3^1

julia> L = hyperkaehler_lattice(:K3; n = 3);

julia> genus(L)
Genus symbol for integer lattices
Signatures: (3, 0, 20)
Local symbol:
  Local genus symbol at 2: 1^22 4^1_7
```
"""
function hyperkaehler_lattice(S::Symbol; n::Int = 2)
  @req S in [:K3, :Kum, :OG10, :OG6] "Wrong symbol for deformation type"

  U = QQ[0 1; 1 0]
  if S == :OG6
    k = QQ[-2 0; 0 -2]
    return integer_lattice(; gram = diagonal_matrix(U, U, U, k))
  elseif S == :Kum
    @req n >= 2 "n must be a positive integer bigger than 1"
    k = QQ[-2-2*n; ]
    return integer_lattice(; gram = diagonal_matrix(U, U, U, k))
  end

  E8 = -_root_lattice_E(8)
  if S == :OG10
    k = -_root_lattice_A(2)
    return integer_lattice(; gram = diagonal_matrix(U, U, U, E8, E8, k))
  else
    @assert S == :K3
    @req n >= 2 "n must be a positive integer bigger than 1"
    k = QQ[2-2*n; ]
    return integer_lattice(; gram = diagonal_matrix(U, U, U, E8, E8, k))
  end
end
