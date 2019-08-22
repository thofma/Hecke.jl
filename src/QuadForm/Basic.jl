export ambient_space, rank, gram_matrix, inner_product, involution, islocal_square, isequivalent, isrationally_equivalent

################################################################################
#
#
#
################################################################################

abstract type AbsSpace end

abstract type AbsLat end

mutable struct QuadSpace{S, T} <: AbsSpace
  K::S
  gram::T
end

mutable struct HermSpace{S, T, U, W} <: AbsSpace
  E::S
  K::T
  gram::U
  involution::W
end


mutable struct QuadLat{S, T, U} <: AbsLat
  space::QuadSpace{S, T}
  pmat::U
  gram::T

  function QuadLat(K::S, G::T, P::U) where {S, T, U}
    space = QuadSpace(K, G)
    z = new{S, T, U}(space, P)
    return z
  end

  function QuadLat(K::S, G::T) where {S, T}
    n = nrows(G)
    M = pseudo_matrix(identity_matrix(K, n))
    return QuadLat(K, G, M)
  end
end

mutable struct HermLat{S, T, U, V, W} <: AbsLat
  space::HermSpace{S, T, U, W}
  pmat::V
  gram::T

  function HermLat(E::S, G::U, P::V) where {S, U, V}
    @assert degree(E) == 2
    A = automorphisms(E)
    a = gen(E)
    if A[1](a) == a
      involution = A[2]
    else
      involution = A[1]
    end

    K = base_field(E)

    space = HermSpace(E, K, G, involution)
      
    z = new{S, typeof(K), U, V, typeof(involution)}(space, P)
    return z
  end

  function HermLat(E::S, G::U) where {S, U}
    n = nrows(G)
    M = pseudo_matrix(identity_matrix(E, n))
    return HermLat(E, G, M)
  end
end

pseudo_matrix(L::AbsLat) = L.pmat

coefficient_ideals(L::AbsLat) = coefficient_ideals(pseudo_matrix(L))

basis_matrix(L::AbsLat) = matrix(pseudo_matrix(L))

rank(L::AbsSpace) = nrows(L.gram)

ambient_space(L::AbsLat) = L.space

rank(L::AbsLat) = nrows(L.pmat)

gram_matrix(L::AbsSpace) = L.gram

function isregular(L::AbsSpace)
  G = gram_matrix(L)
  return rank(G) == nrows(G)
end

base_algebra(L::QuadSpace) = L.K

base_algebra(L::HermSpace) = L.E

base_algebra(L::QuadLat) = L.space.K

base_algebra(L::HermLat) = L.space.E

involution(L::QuadLat) = identity

involution(L::HermLat) = involution(ambient_space(L))

involution(L::QuadSpace) = identity

involution(L::HermSpace) = L.involution

function inner_product(G, v, w)
  mv = matrix(base_ring(G), 1, rank(G), v)
  mw = matrix(base_ring(G), rank(G), 1, w)
  return (mv * gram_matrix(G) * mw)[1, 1]
end

function inner_product(G, v, w, involution)
  return inner_product(G, v, [involution(x) for x in w])
end

inner_product(V::QuadSpace, v, w) = inner_product(gram_matrix(V), v, w)

inner_product(V::HermSpace, v, w) = inner_product(gram_matrix(V), v, w, involution(V))

function gram_matrix(V::AbsSpace, M)
  return M * gram_matrix(V) * transpose(_map(M, involution(V)))
end

function gram_matrix_of_basis(L::AbsLat)
  return gram_matrix(ambient_space(L), L.pmat.matrix)
end

function degree(L::AbsLat)
  return dimension(ambient_space(L))
end

function dimension(L::AbsSpace)
  return nrows(gram_matrix(L))
end

# Check if one really needs minimal
# Steinitz form is not pretty
function generators(L::AbsLat; minimal::Bool = true)
  St = _steinitz_form(pseudo_matrix(L), Val{false})
  d = nrows(St)
  n = degree(L)
  T = elem_type(base_algebra(L))
  v = Vector{T}[]
  for i in 1:(d - 1)
    @assert isprincipal(coefficient_ideals(St)[i])[1]
    push!(v, T[basis_matrix(L)[i, j] for j in 1:d])
  end

  I = numerator(coefficient_ideals(St)[d])
  den = denominator(coefficient_ideals(St)[d])
  if minimal && base_algebra(L) isa AnticNumberField
    b, a = isprincipal(I)
    if b
      push!(v, T[base_algebra(L)(a)//den * basis_matrix(L)[n, j] for j in 1:d])
    end
    return v
  end

  _assure_weakly_normal_presentation(I)
  push!(v, T[base_algebra(L)(I.gen_one)//den * basis_mat(L)[n, j] for j in 1:d])
  push!(v, T[base_algebra(L)(I.gen_two)//den * basis_mat(L)[n, j] for j in 1:d])

  return v
end

function discriminant(L::AbsLat)
  d = det(gram_matrix_of_basis(L))
  v = involution(L)
  C = coefficient_ideals(L)
  I = prod(J for J in C)
  return d * I * v(I)
end

function gram_matrix(V::AbsSpace, v::Vector)
  m = length(v)
  G = zero_matrix(base_algebra(V), m, m)
  for i in 1:m
    for j in 1:m
      G[i, j] = inner_product(V, v[i], v[j])
    end
  end
  return G
end

function det(V::QuadSpace)
  return det(gram_matrix(V))
end

function det(V::HermSpace)
  d = det(gram_matrix(V))
  @assert all(iszero(coeff(d, i)) for i in 1:degree(base_algebra(V)) - 1)
  return coeff(d, 0)
end

function discriminant(V::AbsSpace)
  d = det(V)
  n = mod(rank(V), 4)
  if n == 0 || n == 1
    return d
  else
    return -d
  end
end

function _map(a::MatElem, f)
  z = similar(a)
  for i in 1:nrows(a)
    for j in 1:ncols(a)
      z[i, j] = f(a[i, j])
    end
  end
  return z
end

# Clean this up
function _gram_schmidt(M::MatElem, a)
  F = deepcopy(M)
  K = base_ring(F)
  n = nrows(F)
  S = identity_matrix(K, n)
  ok = isdiagonal(F)
  if !ok
    for i in 1:n 
      if iszero(F[i,i])
        T = identity_matrix(K, n)
        let F = F, i = i
          ok = findfirst(j -> !iszero(F[j, j]), (i + 1):n)
        end
        if ok !== nothing
          T[i,i] = 0
          T[j,j] = 0
          T[i,j] = 1
          T[j,i] = 1
        else
          let F = F, i = i,
            ok = findfirst(j -> !iszero(F[i, j]), (i + 1):n)
          end
          if ok === nothing
            error("Matrix is not of full rank")
          end
          T[i, j] = 1 
        end 
        S = T * S
        F = T * F * transpose(_map(T, a))
      end
      T = identity_matrix(K, n)
      for j in (i + 1):n
        T[j, i] = divexact(-F[j, i], F[i, i])
      end
      F = T * F * transpose(_map(T, a))
      S = T * S
    end
    @assert isdiagonal(F)
  end
  return F, S
end

function diagonal(L::AbsSpace)
  D, _ = _gram_schmidt(gram_matrix(L), involution(L))
  return diagonal(D)
end

function diagonal(L::AbsLat)
  D, _ = _gram_schmidt(gram_matrix_of_basis(L), involution(L))
  return diagonal(D)
end

################################################################################
#
#  Hasse invariant
#
################################################################################

function _hasse_invariant(D, p)
  h = 1
  n = length(D)
  for i in 1:(n - 1)
    for j in (i + 1):n
      n = n * hilbert_symbol(D[i], D[j], p)
    end
  end
  return h
end

function hasse_invariant(V::QuadSpace, p)
  return _hasse_invariant(diagonal(V), p)
end

function hasse_invariant(L::QuadLat, p)
  return _hasse_invariant(diagonal(L), p)
end

function hasse_invariant(L::HermSpace, p)
  throw(error("The space must be quadratic"))
end

function hasse_invariant(L::HermLat, p)
  throw(error("The lattice must be quadratic"))
end

# This can be refactored to operate on the diagonal of a gram schmidt basis and
# the gram matrix.
# (Probably only on the diagonal of a gram schmidt basis)
function witt_invariant(L::QuadSpace, p::NfOrdIdl)
  h = hasse_invariant(L, p)
  F = gram_matrix(L)
  dett = det(F)
  K = base_algebra(L)
  ncolsFmod8 = mod(ncols(F), 8)
  if ncolsFmod8 == 3 || ncolsFmod8 == 4
    c = -dett
  elseif ncolsFmod8 == 5 || ncolsFmod8 == 6
    c = K(-1)
  elseif ncolsFmod8 == 7 || ncolsFmod8 == 0
    c = dett
  else
    c = K(1)
  end
  return h * hilbert_symbol(K(-1), c, p)
end

function witt_invariant(L::QuadSpace, p::InfPlc)
  if iscomplex(p)
    error("Dont' know what to do. Markus returns false")
  end

  h = hasse_invariant(L, p)
  F = gram_matrix(L)
  dett = det(F)
  K = base_algebra(L)
  ncolsFmod8 = mod(ncols(F), 8)
  if ncolsFmod8 == 3 || ncolsFmod8 == 4
    c = -dett
  elseif ncolsFmod8 == 5 || ncolsFmod8 == 6
    c = K(-1)
  elseif ncolsFmod8 == 7 || ncolsFmod8 == 0
    c = dett
  else
    c = K(1)
  end
  @assert !iszero(c)
  if isnegative(c, p)
    return -h
  else
    return h
  end
end

function witt_invariant(L::QuadLat, p::NfOrdIdl)
  h = hasse_invariant(L, p)
  F = gram_matrix_of_basis(L)
  dett = det(F)
  K = base_algebra(L)
  ncolsFmod8 = mod(ncols(F), 8)
  if ncolsFmod8 == 3 || ncolsFmod8 == 4
    c = -dett
  elseif ncolsFmod8 == 5 || ncolsFmod8 == 6
    c = K(-1)
  elseif ncolsFmod8 == 7 || ncolsFmod8 == 0
    c = dett
  else
    c = K(1)
  end
  return h * hilbert_symbol(K(-1), c, p)
end

function witt_invariant(L::QuadLat, p::InfPlc)
  if iscomplex(p)
    error("Dont' know what to do. Markus returns false")
  end

  h = hasse_invariant(L, p)
  F = gram_matrix_of_basis(L)
  dett = det(F)
  K = base_algebra(L)
  ncolsFmod8 = mod(ncols(F), 8)
  if ncolsFmod8 == 3 || ncolsFmod8 == 4
    c = -dett
  elseif ncolsFmod8 == 5 || ncolsFmod8 == 6
    c = K(-1)
  elseif ncolsFmod8 == 7 || ncolsFmod8 == 0
    c = dett
  else
    c = K(1)
  end
  @assert !iszero(c)
  if isnegative(c, p)
    return -h
  else
    return h
  end
end

function isequivalent(L::QuadSpace, M::QuadSpace, p::NfOrdIdl)
  GL = gram_matrix(L)
  GM = gram_matrix(M)
  if GL == GM
    return true
  end

  return rank(GL) == rank(GM) && islocal_square(det(GL) * det(GM), p) && hasse_invariant(L, p) == hasse_invariant(M, p)
end

function isrationally_equivalent(L::QuadLat, M::QuadLat, p::NfOrdIdl)
  GL = gram_matrix_of_basis(L)
  GM = gram_matrix_of_basis(M)
  if GL == GM
    return true
  end

  return rank(GL) == rank(GM) && islocal_square(det(GL) * det(GM), p) && hasse_invariant(L, p) == hasse_invariant(M, p)
end

function isequivalent(L::QuadSpace, M::QuadSpace, p::InfPlc)
  if rank(L) != rank(M)
    return false
  end

  if iscomplex(p)
    return true
  end

  DL = diagonal(L)
  DM = diagonal(M)
  return count(x -> isnegative(x, p), DL) == count(x -> isnegative(x, p), DM)
end

function isequivalent(L::QuadLat, M::QuadLat, p::InfPlc)
  if rank(L) != rank(M)
    return false
  end

  if iscomplex(p)
    return true
  end

  DL = diagonal(L)
  DM = diagonal(M)
  return count(x -> isnegative(x, p), DL) == count(x -> isnegative(x, p), DM)
end

function _quadratic_form_invariants(M; minimal = true)
  G, _ = _gram_schmidt(M, identity);
  D = diagonal(G)
  K = base_ring(M)
  O = maximal_order(K)
  sup = Dict{ideal_type(O), Bool}()
  for i in 1:length(D)
    f = factor(D[i] * O)
    for (P, e) in f
      if isodd(e)
        sup[P] = true
      end
    end
  end
  F = Tuple{ideal_type(O), Int}[]
  for P in keys(sup)
    e = _hasse_invariant(D, P)
    if e == -1 || !minimal
      push!(F, (P, e))
    end
  end
  I = [ (P, count(x -> isnegative(x, P), D)) for P in real_places(K) ];
  return prod(D), F, I
end

#intrinsic QuadraticFormInvariants(M::AlgMatElt[FldAlg]: Minimize:= true) -> FldAlgElt, SetEnum[RngOrdIdl], SeqEnum[RngIntElt]
#{The invariants describing the quadratic form M}
#  require IsSymmetric(M) and Rank(M) eq Ncols(M): "The form must be symmetric and regular";
#  D:= Diagonal(OrthogonalizeGram(M));
#  K:= BaseRing(M);
#  R:= Integers(K);
#  P:= Support(2*R);
#  U:= Universe(P);
#  for d in D do
#    P join:= { f[1] : f in Factorization(d*R) | IsOdd(f[2]) };
#  end for;
#  F:= Minimize select {U | p : p in P | Hasse(D, p) eq -1 } else { <p, Hasse(D, p) > : p in P };
#  I:= [ #[ d: d in D | Evaluate(d, f) le 0 ] : f in RealPlaces(K) ];
#  return &* D, F, I;
#end intrinsic;

#intrinsic IsRationallyEquivalent(L1::LatMod, L2::LatMod : AmbientSpace:= false) -> BoolElt
#{Tests if L1 and L2 are equivalent over their base field}
#  require IsOrthogonal(L1) and IsOrthogonal(L2) : "The lattices must both be hermitian or orthogonal.";
#  require BaseRing(L1) cmpeq BaseRing(L2): "Incompatible lattices";
#
#  if AmbientSpace or (IsFull(L1) and IsFull(L2)) then
#    F1:= InnerProductMatrix(L1);
#    F2:= InnerProductMatrix(L2);
#  else
#    F1:= GramMatrixOfBasis(L1);
#    F2:= GramMatrixOfBasis(L2);
#  end if;
#  if F1 cmpeq F2 then return true;
#  elif Ncols(F1) ne Ncols(F2) then return false; end if;
#
#  Det1, Finite1, I1:= QuadraticFormInvariants(F1);
#  Det2, Finite2, I2:= QuadraticFormInvariants(F2);
#  return I1 eq I2 and Finite1 eq Finite2 and IsSquare(Det1*Det2);
#end intrinsic;

################################################################################
#
#  Helper functions (sort them later)
#
################################################################################

function image(f::NfRelToNfRelMor{T, T}, I::NfRelOrdFracIdl{T, S}) where {T, S}
  #S has to be an automorphism!!!!
  O = order(I)
  @assert ismaximal(O) # Otherwise the order might change
  K = nf(O)

  b = pseudo_basis(I)

  z = NfRelOrdFracIdl{T, S}(O, [(f(a), b) for (a, b) in b])
  return z
end

# An element is locally a square if and only if the quadratic defect is 0, that is
# the valuation is inf.
# (see O'Meara, Introduction to quadratic forms, 3rd edition, p. 160)
function islocal_square(a, p)
  return quadratic_defect(a, p) isa PosInf
end
