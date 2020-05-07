export genus, representative, rank, det, uniformizer, det_representative,
       gram_matrix, representative, genus, genera_hermitian,
       local_genera_hermitian, rank

################################################################################
#
#  Local genus symbol
#
################################################################################

add_verbose_scope(:Lattice)
add_assert_scope(:Lattice)

# Need to make this type stable once we have settled on a design
mutable struct LocalGenusHerm{S, T}
  E::S                                # Field
  p::T                                # prime of base_field(E)
  data::Vector{Tuple{Int, Int, Int}}  # data
  norm_val::Vector{Int}               # additional norm valuation
                                      # (for the dyadic case)
  isdyadic::Bool                      # 2 in p
  isramified::Bool                    # p ramified in E
  non_norm_rep                        # u in K*\N(E*)
  ni::Vector{Int}                     # ni for the ramified, dyadic case

  function LocalGenusHerm{S, T}() where {S, T}
    z = new{S, T}()
    return z
  end
end

################################################################################
#
#  I/O
#
################################################################################

function Base.show(io::IO, ::MIME"text/plain", G::LocalGenusHerm)
  compact = get(io, :compact, false)
  if !compact
    if isdyadic(G) && isramified(G)
      print(io, "Local genus symbol (rank, scale, det, norm) at ")
    else
      print(io, "Local genus symbol (rank, scale, det) at ")
    end
    print(IOContext(io, :compact => true), prime(G), ":")
    print(io, "\n")
  end
  if isdyadic(G) && isramified(G)
    for i in 1:length(G)
      print(io, "(", scale(G, i), ", ", rank(G, i), ", ",
            det(G, i) == 1 ? "+" : "-", ", ", norm(G, i), ")")
    end
  else
    for i in 1:length(G)
      print(io, "(", scale(G, i), ", ", rank(G, i), ", ",
            det(G, i) == 1 ? "+" : "-",  ")")
    end
  end
end

function Base.show(io::IO, G::LocalGenusHerm)
  if isdyadic(G) && isramified(G)
    for i in 1:length(G)
      print(io, "(", scale(G, i), ", ", rank(G, i), ", ",
            det(G, i) == 1 ? "+" : "-", ", ", norm(G, i), ")")
      if i < length(G)
        print(io, " ")
      end
    end
  else
    for i in 1:length(G)
      print(io, "(", scale(G, i), ", ", rank(G, i),
            ", ", det(G, i) == 1 ? "+" : "-",  ")")
      if i < length(G)
        print(io, " ")
      end
    end
  end
end

################################################################################
#
#  Basic properties
#
################################################################################

@doc Markdown.doc"""
    scale(G::LocalGenusHerm, i::Int) -> Int

Given a genus symbol for Hermitian lattices over $E/K$, return the $\mathfrak
P$-valuation of the scale of the $i$th Jordan block of $G$, where $\mathfrak
P$ is a prime ideal lying over $\mathfrak p$.
"""
scale(G::LocalGenusHerm, i::Int) = G.data[i][1]

@doc Markdown.doc"""
    scales(G::LocalGenusHerm, i::Int) -> Vector{Int}

Given a genus symbol for Hermitian lattices over $E/K$, return the $\mathfrak
P$-valuation of the scales of the Jordan blocks of $G$, where $\mathfrak
P$ is a prime ideal lying over $\mathfrak p$.
"""
scales(G::LocalGenusHerm) = map(i -> scale(G, i), 1:length(G))::Vector{Int}

@doc Markdown.doc"""
    rank(G::LocalGenusHerm, i::Int)

Given a genus symbol for Hermitian lattices over $E/K$, return the rank of the
$i$th Jordan block of $G$.
"""
rank(G::LocalGenusHerm, i::Int) = G.data[i][2]

@doc Markdown.doc"""
    rank(G::LocalGenusHerm) -> Int

Given a genus symbol $G$, return the rank of a lattice in $G$.
"""
function rank(G::LocalGenusHerm)
  return sum(rank(G, i) for i in 1:length(G))
end

@doc Markdown.doc"""
    ranks(G::LocalGenusHerm)

Given a genus symbol for Hermitian lattices over $E/K$, return the ranks of the
Jordan block of $G$.
"""
ranks(G::LocalGenusHerm) = map(i -> rank(G, i), 1:length(G))::Vector{Int}

@doc Markdown.doc"""
    det(G::LocalGenusHerm, i::Int) -> Int

Given a genus symbol for Hermitian lattices over $E/K$, return the determinant of the
$i$th Jordan block of $G$. This will be `1` or `-1` depending on whether the
determinant is local norm or not.
"""
det(G::LocalGenusHerm, i::Int) = G.data[i][3]

@doc Markdown.doc"""
    disc(G::LocalGenusHerm, i::Int) -> Int

Given a genus symbol for Hermitian lattices over $E/K$, return the discriminant
of the $i$th Jordan block of $G$. This will be `1` or `-1` depending on whether
the discriminant is local norm or not.
"""
function disc(G::LocalGenusHerm, i::Int)
  d = det(G)
  r = rank(G, i) % 4
  if r == 0 || r == 1
    return d
  end
  E = base_field(G)
  fl = islocal_norm(E, base_field(E)(-1), prime(G))
  if fl
    return d
  else
    return -d
  end
end

@doc Markdown.doc"""
    disc(G::LocalGenusHerm) -> Int

Given a genus symbol $G$, return the discriminant of a lattice in $G$. This will be
`1` or `-1` depending on whether the discriminant is a local norm or not.
"""
function disc(G::LocalGenusHerm)
  d = det(G)
  r = rank(G) % 4
  if r == 0 || r == 1
    return d
  end
  E = base_field(G)
  fl = islocal_norm(E, base_field(K)(-1), prime(G))
  if fl
    return d
  else
    return -d
  end
end

@doc Markdown.doc"""
    det(G::LocalGenusHerm) -> Int

Given a genus symbol $G$, return the determinant of a lattice in $G$. This will be
`1` or `-1` depending on whether the determinant is a local norm or not.
"""
function det(G::LocalGenusHerm)
  return prod(det(G, i) for i in 1:length(G))
end

@doc Markdown.doc"""
    dets(G::LocalGenusHerm) -> Vector{Int}

Given a genus symbol for Hermitian lattices over $E/K$, return the determinants
of the Jordan blocks of $G$. These will be `1` or `-1` depending on whether the
determinant is local norm or not.
"""
dets(G::LocalGenusHerm) = map(i -> det(G, i), 1:length(G))::Vector{Int}

@doc Markdown.doc"""
    norm(G::LocalGenusHerm, i::Int) -> Int

Given a dyadic genus symbol for Hermitian lattices over $E/K$ at a prime
$\mathfrak p$, return the $\mathfrak p$-valuation of the norm of the $i$ Jordan
block of $G$.
"""
norm(G::LocalGenusHerm, i::Int) = begin @assert isdyadic(G); G.norm_val[i] end # this only works if it is dyadic

@doc Markdown.doc"""
    norms(G::LocalGenusHerm) -> Vector{Int}

Given a dyadic genus symbol for Hermitian lattices over $E/K$ at a prime
$\mathfrak p$, return the $\mathfrak p$-valuations of the norms of the Jordan
blocks of $G$.
"""

@doc Markdown.doc"""
    isramified(G::LocalGenus) -> Bool

Given a genus symbol for Hermitian lattices at a prime $\mathfrak p$, return
whether $\mathfrak p$ is ramified.
"""
isramified(G::LocalGenusHerm) = G.isramified

@doc Markdown.doc"""
    isdyadic(G::LocalGenus) -> Bool

Given a genus symbol for Hermitian lattices at a prime $\mathfrak p$, return
whether $\mathfrak p$ is dyadic.
"""
isdyadic(G::LocalGenusHerm) = G.isdyadic

#data(G::LocalGenusHerm) = G.data

@doc Markdown.doc"""
    length(G::LocalGenusHerm) -> Int

Return the number of Jordan blocks in a Jordan decomposition of $G$.
"""
length(G::LocalGenusHerm) = length(G.data)

@doc Markdown.doc"""
    base_field(G::LocalGenusHerm) -> NumField

Given a local genus symbol of Hermitian lattices over $E/K$, return $E$.
"""
base_field(G::LocalGenusHerm) = G.E

@doc Markdown.doc"""
    prime(G::LocalGenus) -> NfOrdIdl

Given a local genus symbol of Hermitian lattices at a prime $\mathfrak p$,
return $\mathfrak p$.
"""
prime(G::LocalGenusHerm) = G.p

################################################################################
#
#  A local non-norm
#
################################################################################

function _non_norm_rep(G::LocalGenusHerm)
  if isdefined(G, :non_norm_rep)
    return G.non_norm_rep::elem_type(base_field(base_field(G)))
  end

  z = _non_norm_rep(base_field(G), base_field(base_field(G)), prime(G))
  G.non_norm_rep = z
  return z::elem_type(base_field(base_field(G)))
end

################################################################################
#
#  A local unifomizer
#
################################################################################

@doc Markdown.doc"""
    uniformizer(G::LocalGenusHerm) -> NumFieldElem

Given a local genus symbol of Hermitian lattices over $E/K$ at a prime $\mathfrak p$,
return a generator for the largest invariant ideal of $E$.
"""
function uniformizer(G::LocalGenusHerm)
  E = base_field(G)
  K = base_field(E)
  if isramified(G)
    lP = prime_decomposition(maximal_order(E), prime(G))
    @assert length(lP) == 1 && lP[1][2] == 2
    Q = lP[1][1]
    pi = p_uniformizer(Q)
    A = automorphisms(E)
    uni = A[1](elem_in_nf(pi)) * A[2](elem_in_nf(pi))
    @assert iszero(coeff(uni, 1))
    @assert islocal_norm(E, coeff(uni , 0), prime(G))
    return coeff(uni, 0)
  else
    return uniformizer(prime(G))
  end
end

################################################################################
#
#  Additional dyadic information
#
################################################################################

# Get the "ni" for the ramified dyadic case
function _get_ni_from_genus(G::LocalGenusHerm)
  @assert isramified(G)
  @assert isdyadic(G)
  t = length(G)
  z = Vector{Int}(undef, t)
  for i in 1:t
    ni = minimum(2 * max(0, scale(G, i) - scale(G, j)) + 2 * norm(G, j) for j in 1:t)
    z[i] = ni
  end
  return z
end

################################################################################
#
#  Determinant representative
#
################################################################################

# TODO: I don't understand what this is doing. I know that d tells me if it is
#       a norm or not. Why do I have to multiply with a uniformizer
@doc Markdown.doc"""
    det_representative(G::LocalGenusHerm) -> NumFieldElem

Return a representative for the norm class of the determinant of $G$.
"""
function det_representative(G::LocalGenusHerm)
  z = G.data
  d = det(G)
  v = sum(scale(G, i) * rank(G, i) for i in 1:length(G))
  if isramified(G)
    v = div(v, 2)
  end
  if d == 1
    u = one(base_field(base_field(G)))
  else
    @assert isramified(G)
    u = _non_norm_rep(G)
  end
  return u * uniformizer(G)^v
end

################################################################################
#
#  Gram matrix
#
################################################################################

@doc Markdown.doc"""
    gram_matrix(G::LocalGenusHerm)

Return a matrix $M$, such that a lattice with Gram matrix $M$ is an element of
the given genus.
"""
function gram_matrix(G::LocalGenusHerm)
  return diagonal_matrix(dense_matrix_type(base_field(G))[gram_matrix(G, i) for i in 1:length(G)])
end

function gram_matrix(G::LocalGenusHerm, l::Int)
  i = scale(G, l)
  m = rank(G, l)
  d = det(G, l)
  E = base_field(G)
  K = base_field(E)
  p = elem_in_nf(p_uniformizer(prime(G)))
  A = automorphisms(E)
  _a = gen(E)
  conj = A[1](_a) == _a ? A[2] : A[1] 

  if !isramified(G)
    return diagonal_matrix([E(p)^i for j in 1:m])
  end

  # ramified
  
  lQ = prime_decomposition(maximal_order(E), prime(G))
  @assert length(lQ) == 1 && lQ[1][2] == 2
  Q = lQ[1][1]
  pi = elem_in_nf(p_uniformizer(Q))
  H = matrix(E, 2, 2, [0, pi^i, conj(pi)^i, 0])

  if !isdyadic(G)
    # non-dyadic
    if iseven(i)
      # According to Kir16, there the last exponent should be i/2 * (1 - m)
      if d == 1
        u = one(E)
      else
        u = _non_norm_rep(G)
      end
      if m == 1
        fl = islocal_norm(E, p^div(i, 2), prime(G))
        if d == -1
          return diagonal_matrix([(fl ? _non_norm_rep(G) : one(E)) * E(p)^div(i, 2)])
        else
          return diagonal_matrix([(!fl ? _non_norm_rep(G) : one(E)) * E(p)^div(i, 2)]) 
        end
      end
      return diagonal_matrix(push!([E(p)^div(i, 2) for j in 1:(m - 1)], u * E(p)^(div(i, 2) * (m - 1))))
    else
      return diagonal_matrix([H for j in 1:div(m, 2)])
    end
  end

  # dyadic
  
  k = norm(G, l)

  # I should cache this e
  e = valuation(different(maximal_order(E)), Q)

  if isodd(m)
    # odd rank
    @assert 2*k == i
    r = div(m - 1, 2)
    nn = mod(m, 4)
    if d == 1
      discG = K(1)
    else
      discG = elem_in_nf(_non_norm_rep(G))
    end
    if nn == 0 || nn == 1
      discG = discG
    else
      discG = -discG
    end
    @assert iseven(i)
    if islocal_norm(E, discG*p^(-m * div(i, 2)), prime(G))
      u = K(1)
    else
      u = _non_norm_rep(G)
    end

    U = matrix(E, 1, 1, [u * p^(div(i, 2))])
    return diagonal_matrix(append!(typeof(U)[U], [H for j in 1:r]))
  else
    # even rank
    r = div(m, 2) - 1
    if islocal_norm(E, K((-1)^div(m, 2)), prime(G)) == (d == 1)
      # hyperbolic
      @assert i + e >= 2 * k
      @assert 2 * k >= i
      U = matrix(E, 2, 2, [p^k, pi^i, conj(pi)^i, 0])
      return diagonal_matrix(append!(typeof(U)[U], [H for j in 1:r]))
    else # not hyperbolic
      @assert i + e > 2 * k
      @assert 2 * k >= i
      u = _non_norm_rep(G)
      u0 = u - 1
      U = matrix(E, 2, 2, [p^k, pi^i, conj(pi)^i, -p^(i -k) * u0])
      return diagonal_matrix(append!(typeof(U)[U], [H for j in 1:r]))
    end
  end
end

################################################################################
#
#  Representative
#
################################################################################

@doc Markdown.doc"""
    representative(G::LocalGenusHerm) -> HermLat

Given a local genus, return a Hermitian lattice contained in this genus.
"""
function representative(G::LocalGenusHerm)
  E = G.E
  return lattice(hermitian_space(E, gram_matrix(G)))
end

################################################################################
#
#  Constructor
#
################################################################################

@doc Markdown.doc"""
    genus(HermLat, E::NumField, p::Idl, data::Vector{Tuple{Int, Int, Int}};
                                        type = :det)
                                                              -> LocalGenusHerm

Construct the local genus symbol of hermitian lattices over $E$ at the prime ideal
$\mathfrak p$ with the invariants specified by `data`.

If the prime ideal is good, the vector `data` contain for each block of the
Jordan decomposition a pair `(s, r, d)`, where `s` is the scale, `r` the
rank. The value `d` must be in `[-1, 1]` and indicates whether the determinant
of the block is a local norm or not.

If the optional `type` keyword is set to `:disc`, then `d` is interpreted as the
norm class of the discriminant of the corresponding Jordan block.
"""
genus(::Type{HermLat}, E, p, data; type)

function genus(::Type{HermLat}, E::S, p::T, data::Vector{Tuple{Int, Int, Int}}; type = :det) where {S <: NumField, T}
  z = LocalGenusHerm{S, T}()
  z.E = E
  z.p = p
  z.isdyadic = isdyadic(p)
  z.isramified = isramified(maximal_order(E), p)
  @assert !(isramified(z) && isdyadic(z))
  if !z.isramified || type === :det
    z.data = copy(data)
  else
    type !== :disc && throw(error("type :$type must be :disc or :det"))
    fl = islocal_norm(E, base_field(E)(-1), p)
    if fl
      z.data = copy(data)
    end
    # Now -1 is not a local norm, so we adjust whenever the rank is 2, 3 mod 4.
    z.data = Vector{Tuple{Int, Int, Int}}(undef, length(data))
    for i in 1:length(data)
      r = data[i][2] % 4
      if r == 0 || r == 1
        z.data[i] = data[i]
      else
        z.data[i] = (data[i][1], data[i][2], (-1) * data[i][3])
      end
    end
  end
  return z
end

function genus(::Type{HermLat}, E::S, p::T, data::Vector{Tuple{Int, Int, Int, Int}}; type = :det) where {S <: NumField, T}
  z = LocalGenusHerm{S, T}()
  z.E = E
  z.p = p
  z.isdyadic = isdyadic(p)
  z.isramified = isramified(maximal_order(E), p)
  if isramified(z) && isdyadic(z)
    z.data = Tuple{Int, Int, Int}[Base.front(v) for v in data]
    z.norm_val = Int[v[end] for v in data]
    z.ni = _get_ni_from_genus(z)
    
    for i in 1:length(z.data)
      # If the rank is odd, then n(L) * O_E = s(L), so n = 2 * s,
      # since n is the valuation in K and the extension is ramified.
      v = z.data[i]
      if isodd(v[2])
        if 2 * z.norm_val[i] != v[1]
          throw(error("""Not a valid local genus in block $(i):
                      Scale ($(v[1])) must be twice the norm ($(z.norm_val[i]))"""))
        end
      end
    end
  else
    z.data = Tuple{Int, Int, Int}[Base.front(v) for v in data]
  end

  if type !== :det && type !== :disc
    throw(error("type :$type must be :disc or :det"))
  end

  if type === :disc
    fl = islocal_norm(E, base_field(E)(-1), p)
    if !fl
      for i in 1:length(z.data)
        r = z.data[i][2] % 4
        if r == 0 || r == 1
          continue
        else
          z.data[i] = (z.data[i][1], z.data[i][2], (-1) * z.data[i][3])
        end
      end
    end
  end

  return z::LocalGenusHerm{S, T}
end

################################################################################
#
#  Genus symbol of a lattice
#
################################################################################

# TODO: caching
# TODO: better documentation

@doc Markdown.doc"""
    genus(L::HermLat, p::NfOrdIdl) -> LocalGenusHerm

Returns the genus of $L$ at the prime ideal $\mathfrak p$.

See [Kir16, Definition 8.3.1].
"""
function genus(L::HermLat, q)
  if order(q) !== base_ring(base_ring(L))
    return _genus(L, minimum(q))
  else
    return _genus(L, q)
  end
end

function _genus(L::HermLat, p)
  sym = _genus_symbol(L, p)
  G = genus(HermLat, nf(base_ring(L)), p, sym)
  # Just for debugging 
  @hassert :Lattice 1 begin
    if isdyadic(G) && isramified(G)
      GG = _genus_symbol_kirschmer(L, p)
      all(i -> GG[i][4] == G.ni[i], 1:length(G))
    else
      true
    end
  end
  return G
end

################################################################################
#
#  Test if lattice is contained in local genus
#
################################################################################

@doc Markdown.doc"""
    in(L::HermLat, G::LocalGenusHerm) -> Bool

Test if the lattice $L$ is contained in the local genus $G$.
"""
Base.in(L::HermLat, G::LocalGenusHerm) = genus(L, prime(G)) == G

################################################################################
#
#  Equality
#
################################################################################

@doc Markdown.doc"""
    ==(G1::LocalGenusHerm, G2::LocalGenusHerm)

Test if two local genera are equal.
"""
function ==(G1::LocalGenusHerm, G2::LocalGenusHerm)
  if base_field(G1) != base_field(G2)
    return false
  end

  if prime(G1) != prime(G2)
    return false
  end

  if length(G1) != length(G2)
    return false
  end

  t = length(G1)

  p = prime(G1)

  # We now check the Jordan type

  if any(i -> scale(G1, i) != scale(G2, i), 1:t)
    return false
  end

  if any(i -> (rank(G1, i) != rank(G2, i)), 1:t)
    return false
  end

  if det(G1) != det(G2) # rational spans must be isometric
    return false
  end

  if any(i -> (rank(G1, i) != rank(G2, i)), 1:t)
    return false
  end

  if !isramified(G1) # split or unramified
    return true
    # Everything is normal and the Jordan decomposition types agree
    #return all(det(G1, i) == det(G2, i) for i in 1:t)
  end

  if isramified(G1) && !isdyadic(G1) # ramified, but not dyadic
    # If s(L_i) is odd, then L_i = H(s(L_i))^(rk(L_i)/2) = H(s(L_i'))^(rk(L_i')/2) = L_i'
    # So all L_i, L_i' are locally isometric, in particular L_i is normal if and only if L_i' is normal
    # If s(L_i) = s(L_i') is even, then both L_i and L_i' have orthgonal bases, so they are
    # in particular normal.

    # Thus we only have to check Theorem 3.3.6 4.
    return all(i -> det(G1, i) == det(G2, i), 1:t)
    # TODO: If think I only have to do something if the scale is even. Check this!
  end

  # Dyadic ramified case

  # First check if L_i is normal if and only if L_i' is normal, i.e.,
  # that the Jordan decompositions agree
  for i in 1:t
    if (scale(G1, i) == 2 * norm(G1, i)) != (scale(G2, i) == 2 * norm(G2, i))
      return false
    end
  end

  if any(i -> G1.ni[i] != G2.ni[i], 1:t)
    return false
  end

  E = base_field(G1)
  lQ = prime_decomposition(maximal_order(E), p)
  @assert length(lQ) == 1 && lQ[1][2] == 2
  Q = lQ[1][1]

  e = valuation(different(maximal_order(E)), Q)

  for i in 1:(t - 1)
    dL1prod = prod(det(G1, j) for j in 1:i)
    dL2prod = prod(det(G2, j) for j in 1:i)

    d = dL1prod * dL2prod

    if d != 1
      if 2 * (e - 1) < G1.ni[i] + G1.ni[i + 1] - 2 * scale(G1, i)
        return false
      end
    end
  end

  return true
end

function _genus_symbol(L::HermLat, q)
  if order(q) != base_ring(base_ring(L))
    return __genus_symbol(L, minimum(q))
  else
    return __genus_symbol(L, q)
  end
end

function __genus_symbol(L::HermLat, p)
  @assert order(p) == base_ring(base_ring(L))
  B, G, S = jordan_decomposition(L, p)
  R = base_ring(L)
  E = nf(R)
  K = base_field(E)
  local sym::Vector{Tuple{Int, Int, Int, Int}}
  if !isdyadic(p) || !isramified(R, p)
    # The last entry is a dummy to make the compiler happier
    sym = Tuple{Int, Int, Int, Int}[ (S[i], nrows(B[i]), islocal_norm(E, coeff(det(G[i]), 0), p) ? 1 : -1, 0) for i in 1:length(B)]
  else
    P = prime_decomposition(R, p)[1][1]
    pi = E(K(uniformizer(p)))
    sym = Tuple{Int, Int, Int, Int}[]
    for i in 1:length(B)
      normal = _get_norm_valuation_from_gram_matrix(G[i], P) == S[i]
      GG = diagonal_matrix(dense_matrix_type(E)[pi^(max(0, S[i] - S[j])) * G[j] for j in 1:length(B)])
      v = _get_norm_valuation_from_gram_matrix(GG, P)
      #@assert v == valuation(R * norm(lattice(hermitian_space(E, GG), identity_matrix(E, nrows(GG)))), P)
      r = nrows(B[i]) # rank
      s = S[i] # P-valuation of scale(L_i)
      det_class = islocal_norm(E, coeff(det(G[i]), 0), p) ? 1 : -1  # Norm class of determinant
      normi = _get_norm_valuation_from_gram_matrix(G[i], P) # P-valuation of norm(L_i)
      @assert mod(normi, 2) == 0 # I only want p-valuation
      push!(sym, (s, r, det_class, div(normi, 2)))
    end
  end
  return sym
end

################################################################################
#
#  Global genus
#
################################################################################

mutable struct GenusHerm
  E
  primes::Vector
  LGS::Vector
  rank::Int
  signatures

  function GenusHerm(E, r, LGS::Vector, signatures)
    primes = Vector(undef, length(LGS))

    for i in 1:length(LGS)
      primes[i] = prime(LGS[i])
      @assert r == rank(LGS[i])
    end
    z = new(E, primes, LGS, r, signatures)
    return z
  end
end

@doc Markdown.doc"""
    ==(G1::GenusHerm, G2::GenusHerm)

Test if two genera are equal.
"""
function ==(G1::GenusHerm, G2::GenusHerm)
  if G1.E != G2.E
    return false
  end

  if length(G1.primes) != length(G2.primes)
    return false
  end

  if G1.signatures != G2.signatures
    return false
  end

  for p in G1.primes
    if !(p in G2.primes)
      return false
    end
    if G1[p] != G2[p]
      return false
    end
  end

  return true
end

function Base.show(io::IO, G::GenusHerm)
  print(io, "Genus symbol over")
  print(io, G.E)
  print(io, "\n", "and local genera",)
  for g in G.LGS
    print(io, "\n")
    print(IOContext(io, :compact => true), prime(g), " => ", g)
  end
  print(io, "\n and signature")
  for (pl, v) in G.signatures
    print(io, "\n")
    _print_short(io, pl.r)
    print(io, " => ")
    print(io, v)
  end
end

function _print_short(io::IO, a::arb)
  r = BigFloat(a)
  s = string(r)
  if length(s) >= 10
    ss = s[1:9] * "…"
  else
    ss = s
  end
  print(io, ss)
end

function _print_short(io::IO, a::acb)
  _print_short(io, real(a))
  if !iszero(imag(a))
    print(io, " + ")
    _print_short(io, imag(a))
    print(io, " * i")
  end
end

################################################################################
#
#  Test if lattice is contained in genus
#
################################################################################

@doc Markdown.doc"""
    in(L::HermLat, G::LocalGenusHerm) -> Bool

Test if the lattice $L$ is contained in the local genus $G$.
"""
Base.in(L::HermLat, G::GenusHerm) = genus(L) == G

# This could be made more efficient

################################################################################
#
#  I/O
#
################################################################################

function Base.show(io::IO, ::MIME"text/plain", G::GenusHerm)
  print(io, "Global genus symbol\n")
  for i in 1:length(G.primes)
    print(IOContext(io, :compact => true), G.primes[i], " => ", G.LGS[i],)
    if i < length(G.primes)
      print(io, "\n")
    end
  end
  for (pl, v) in G.signatures
    print(io, "\n")
    _print_short(io, pl.r)
    print(io, " => ")
    print(io, v)
  end
end

################################################################################
#
#  Constructor
#
################################################################################

@doc Markdown.doc"""
    genus(L::Vector{LocalGenusHerm},
          signatures::Vector{Tuple{InfPlc, Int}}) -> GenusHerm

Given a set of local genera and signatures, return the corresponding global
genus.
"""
function genus(L::Vector, signatures::Dict{InfPlc, Int})
  @assert !isempty(L)
  @assert all(N >= 0 for (_, N) in signatures)
  if !_check_global_genus(L, signatures)
    throw(error("Invariants violate the product formula."))
  end
  r = rank(first(L))
  E = base_field(first(L))
  return GenusHerm(E, r, L, signatures)
end

function genus(L::Vector, signatures::Vector{Tuple{InfPlc, Int}})
  return genus(L, Dict(signatures))
end

@doc Markdown.doc"""
    genus(L::HermLat) -> GenusHerm

Given a Hermitian lattice, return the genus it belongs to.
"""
function genus(L::HermLat)
  bad = bad_primes(L)
  for p in support(discriminant(base_ring(L)))
    if !(p in bad)
      push!(bad, p)
    end
  end

  for p in support(2 * base_ring(base_ring(L)))
    if !(p in bad)
      push!(bad, p)
    end
  end

  S = real_places(base_field(base_field(L)))
  D = diagonal(rational_span(L))
  signatures = Dict{InfPlc, Int}(s => count(d -> isnegative(d, s), D) for s in S)
  return genus([genus(L, p) for p in bad], signatures)
end

################################################################################
#
#  Basic access
#
################################################################################

@doc Markdown.doc"""
    primes(G::GenusHerm) -> Vector{NfOrdIdl}

Return the primes of a global genus symbol.
"""
primes(G::GenusHerm) = G.primes

@doc Markdown.doc"""
    signatures(G::GenusHerm) -> Dict{InfPlc, Int}

Return the signatures at the infinite places, which for each real place is
given by the negative index of inertia.
"""
signatures(G::GenusHerm) = G.signatures

################################################################################
#
#  Consistency check
#
################################################################################

function _check_global_genus(LGS, signatures)
  _non_norm = _non_norm_primes(LGS)
  P = length(_non_norm)
  I = length([(s, N) for (s, N) in signatures if mod(N, 2) == 1])
  if mod(P + I, 2) == 1
    return false
  end
  return true
end

################################################################################
#
#  Primes at which the determinant is not a local norm
#
################################################################################

function _non_norm_primes(LGS::Vector)
  z = []
  for g in LGS
    p = prime(g)
    d = det(g)
    if d != 1
      push!(z, p)
    end
  end
  return z
end

################################################################################
#
#  Convenient functions
#
################################################################################

function Base.getindex(G::GenusHerm, P)
  i = findfirst(isequal(P), G.primes)
  if i === nothing
    throw(error("No local genus symbol at $P"))
  end
  return G.LGS[i]
end

################################################################################
#
#  Compute representatives of genera
#
################################################################################

function _hermitian_form_with_invariants(E, dim, P, N)
  #@show dim, P, N
  #@show E, dim, N, [minimum(p) for p in P]
  K = base_field(E)
  R = maximal_order(K)
#  require forall{n: n in N | n in {0..dim}}: "Number of negative entries is impossible";
  infinite_pl = [ p for p in real_places(K) if _decomposition_number(E, p) == 1 ]
  length(N) != length(infinite_pl) && error("Wrong number of real places")
  S = maximal_order(E)
  prim = [ p for p in P if length(prime_decomposition(S, p)) == 1 ] # only take non-split primes
  #@show prim
  I = [ p for p in keys(N) if isodd(N[p]) ]
  !iseven(length(I) + length(P)) && error("Invariants do not satisfy the product formula")
  e = gen(E)
  x = 2 * e - trace(e)
  b = coeff(x^2, 0) # b = K(x^2)
  #@show b, prim, I
  a = _find_quaternion_algebra(b, prim, I)
  #@show a
  D = elem_type(E)[]
  for i in 1:(dim - 1)
    if length(I) == 0
      push!(D, one(E))
    else
      push!(D, E(_weak_approximation(infinite_pl, [N[p] >= i ? -1 : 1 for p in infinite_pl])))
    end
  end
  push!(D, a * prod(D))
  Dmat = diagonal_matrix(D)
  #@show Dmat
  dim0, P0, N0 = _hermitian_form_invariants(Dmat)
  #@show P0
  #@show prim
  @assert dim == dim0
  @assert Set(prim) == Set(P0)
  @assert N == N0
  return Dmat
end

function _hermitian_form_invariants(M)
  E = base_ring(M)
  K = base_field(E)
  @assert degree(E) == 2
  A = automorphisms(E)
  a = gen(E)
  v = A[1](a) == a ? A[2] : A[1]

  @assert M == transpose(_map(M, v))
  d = coeff(det(M), 0) # K(det(M))
  P = Dict()
  for p in keys(factor(d * maximal_order(K)))
    if islocal_norm(E, d, p)
      continue
    end
    P[p] = true
  end
  for p in keys(factor(discriminant(maximal_order(E))))
    if islocal_norm(E, d, p)
      continue
    end
    P[p] = true
  end
  D = diagonal(_gram_schmidt(M, v)[1])
  I = Dict([ p=>length([coeff(d, 0) for d in D if isnegative(coeff(d, 0), p)]) for p in real_places(K) if _decomposition_number(E, p) == 1])
  return ncols(M), collect(keys(P)), I
end

base_field(G::GenusHerm) = G.E

rank(G::GenusHerm) = G.rank

function representative(G::GenusHerm)
  P = _non_norm_primes(G.LGS)
  E = base_field(G)
  V = hermitian_space(E, _hermitian_form_with_invariants(base_field(G), rank(G), P, G.signatures))
  @vprint :Lattice 1 "Finding maximal integral lattice\n"
  M = maximal_integral_lattice(V)
  lp = G.primes
  for g in G.LGS
    p = prime(g)
    @vprint :Lattice 1 "Finding representative for $g at $(prime(g))...\n"
    L = representative(g)
    @hassert :Lattice 1 genus(L, p) == g
    #@show coefficient_ideals(pseudo_matrix(L))
    #@show matrix(pseudo_matrix(L))
    @vprint :Lattice 1 "Finding sublattice\n"
    M = find_lattice(M, L, p)
  end
  return M
end

################################################################################
#
#  Enumeration of local genera
#
################################################################################

@doc Markdown.doc"""
    local_genera_hermitian(E::NumField, p::NfOrdIdl, rank::Int,
                 det_val::Int, max_scale::Int) -> Vector{LocalGenusHerm}

Return all local genera of Hermitian lattices over $E$ at $\mathfrak p$ with
rank `rank`, scale valuation bounded by `max_scale` and determinant valuation
bounded by `det_val`.
"""
function local_genera_hermitian(E, p, rank::Int, det_val::Int, max_scale::Int, is_ramified = isramified(maximal_order(E), p))
  #@show E, p, rank, det_val, max_scale, is_ramified
  is_inert = !is_ramified && length(prime_decomposition(maximal_order(E), p)) == 1
  if is_ramified
    # the valuation is with respect to p
    # but the scale is with respect to P
    # in the ramified case p = P**2 and thus
    # the determinant of a block is
    # P^(scale*rank) = p^(scale*rank/2)
    det_val *= 2
  end

  K = number_field(order(p))

  scales_rks = Vector{Tuple{Int, Int}}[] # possible scales and ranks

  for rkseq in _integer_lists(rank, max_scale + 1)
    d = 0
    pgensymbol = Tuple{Int, Int}[]
    for i in 0:(max_scale + 1) - 1
      d += i * rkseq[i + 1]
      if rkseq[i + 1] != 0
        push!(pgensymbol, (i, rkseq[i + 1]))
      end
    end
    if d == det_val
        push!(scales_rks, pgensymbol)
    end
  end
  
  if !is_ramified
    # I add the 0 to make the compiler happy
    symbols = Vector{LocalGenusHerm{typeof(E), typeof(p)}}(undef, length(scales_rks))
    for i in 1:length(scales_rks)
      g = scales_rks[i]
      z = Tuple{Int, Int, Int, Int}[]
      for b in g
        # We have to be careful.
        # If p is inert, then the norm is not surjective. 
        if !is_inert || iseven(b[1] * b[2])
          push!(z, (b[1], b[2], 1, 0))
        else
          push!(z, (b[1], b[2], -1, 0))
        end
      end
      symbols[i] = genus(HermLat, E, p, z)
    end
    return symbols
  end

  scales_rks = Vector{Tuple{Int, Int}}[g for g in scales_rks if all((mod(b[1]*b[2], 2) == 0) for b in g)]

  symbols = LocalGenusHerm{typeof(E), typeof(p)}[]
  #hyperbolic_det = hilbert_symbol(K(-1), gen(K)^2//4 - 1, p)
  hyperbolic_det = islocal_norm(E, K(-1), p) ? 1 : -1
  if !isdyadic(p) # non-dyadic
    for g in scales_rks
      n = length(g)
      dets = Vector{Int}[]
      for b in g
        if mod(b[1], 2) == 0
          push!(dets, [1, -1])
        end
        if mod(b[1], 2) == 1
          push!(dets, [hyperbolic_det^(div(b[2], 2))])
        end
      end

      for d in Iterators.product(dets...)
        g2 = Vector{Tuple{Int, Int, Int, Int}}(undef, length(g))
        for k in 1:n
          # Again the 0 for dummy purposes
          g2[k] = (g[k]..., d[k], 0)
        end
        push!(symbols, genus(HermLat, E, p, g2))
      end
    end
    return symbols
  end

  # Ramified case
  lp = prime_decomposition(maximal_order(E), p)
  @assert length(lp) == 1 && lp[1][2] == 2
  P = lp[1][1]
  
  e = valuation(different(maximal_order(E)), P)
  # only for debugging
  scales_rks = reverse(scales_rks)

  for g in scales_rks
    n = length(g)
    det_norms = Vector{Vector{Int}}[]
    for b in g
      if mod(b[2], 2) == 1
        @assert iseven(b[1])
        push!(det_norms, [[1, div(b[1], 2)], [-1, div(b[1], 2)]])
      end
      if mod(b[2], 2) == 0
        dn = Vector{Int}[]
        i = b[1]
        # (i + e) // 2 => k >= i/2
        k = ceil(Int, i//2) 
        while 2 * k < i + e
          push!(dn, Int[1, k])
          push!(dn, Int[-1, k])
          k += 1
        end

        if mod(i + e, 2) == 0
          push!(dn, Int[hyperbolic_det^(div(b[2], 2)), k])
        end
        push!(det_norms, dn)
        #for k in (ceil(Int, Int(i)//2)):(div(Int(i + e), 2) - 1)
        #  push!(dn, Int[1, k])
        #  push!(dn, Int[-1, k])
        #end
        #push!(dn, Int[hyperbolic_det^(div(b[2], 2)), div(i + e, 2)])
        #if mod(i + e, 2) == 1
        #  push!(dn, Int[-hyperbolic_det^(div(b[2], 2)), div(i + e, 2)])
        #end
        #push!(det_norms, dn)
      end
    end
    for dn in Iterators.product(det_norms...)
      g2 = Vector{Tuple{Int, Int, Int, Int}}(undef, length(g))
      for k in 1:n
        g2[k] = (g[k]..., dn[k]...)
      end
      h = genus(HermLat, E, p, g2)
      if !(h in symbols)
        push!(symbols, h)
      end
    end
  end
  return symbols
end

@doc Markdown.doc"""
    genera_hermitian(E::NumField, p::NfOrdIdl, rank::Int,
                    det_val::Int, max_scale::Int) -> Vector{LocalGenusHerm}

Return all local genera of Hermitian lattices over $E$ at $\mathfrak p$ with
rank `rank`, scale valuation bounded by `max_scale` and determinant valuation
bounded by `det_val`.
"""
function genera_hermitian(E, rank, signatures, determinant; max_scale = nothing)
  K = base_field(E)
  OE = maximal_order(E)
  if max_scale === nothing
    _max_scale = determinant
  else
    _max_scale = max_scale
  end

  primes = support(discriminant(OE))
  for p in support(norm(determinant))
    if !(p in primes)
      push!(primes, p)
    end
  end

  local_symbols = Vector{LocalGenusHerm{typeof(E), typeof(primes[1])}}[]

  ms = norm(_max_scale)
  ds = norm(determinant)
  for p in primes
    det_val = valuation(ds, p)
    mscale_val = valuation(ms, p)
    det_val = div(det_val, 2)
    if !isramified(OE, p)
      mscale_val = div(mscale_val, 2)
    end
    push!(local_symbols, local_genera_hermitian(E, p, rank, det_val, mscale_val))
  end

  res = []
  it = Iterators.product(local_symbols...)
  for gs in it
    c = collect(gs)
    b = _check_global_genus(c, signatures)
    if b
      push!(res, GenusHerm(E, rank, c, signatures))
    end
  end

  return res
end

################################################################################
#
#  Genus representatives
#
################################################################################

# Return b, p, bad
# b = isdefinite(L)
# p = prime ideal of base_ring(L) which can be used for the neighbor method
# bad = bad primes of L, where L,p is not modular or p is dyadic and dividing disc(S)
function smallest_neighbour_prime(L)
  S = base_ring(L)
  R = base_ring(S)
  lp = bad_primes(L)
  bad = ideal_type(R)[p for p in lp if !ismodular(L, p)[1] ]
  for (p,_) in factor(discriminant(S))
    if isdyadic(p) && !(p in bad)
      push!(bad, p)
    end
  end

  if !isdefinite(L)
    return false, 1*S, bad
  end

  # TODO: This does not find the prime ideal with smallest norm,
  # but with smallest minimum ...

  m = rank(L)
  p = 1
  P = ideal_type(R)[]
  while length(P) == 0
    p = next_prime(p)
    lp = ideal_type(R)[ p[1] for p in prime_decomposition(R, p)]
    P = setdiff(lp, bad)
    if m == 2
      P = filter(p -> isisotropic(L, p), P)
    end
  end
  Q = prime_decomposition(S, P[1])[1][1]

  if isempty(bad)
    I = 1 * S
  else
    I = prod(bad) * S
  end
  n = absolute_norm(Q)
  if n >= 1000
    PP = prime_ideals_up_to(S, 1000)
    for QQ in PP
      if !iscoprime(QQ, I)
        continue
      end

      if isisotropic(L, QQ)
        return true, QQ, bad
      end
    end
  end
  PP = prime_ideals_up_to(S, n)
  for QQ in PP
    if !iscoprime(QQ, I)
      continue
    end
    if isisotropic(L, QQ)
      return true, QQ, bad
    end
  end
  throw(error("Impossible"))
end

function genus_generators(L::HermLat)
  R = base_ring(L)
  E = nf(R)
  D = different(R)
  b, P0, bad = smallest_neighbour_prime(L)

  local bad_prod::ideal_type(base_ring(R))

  if isempty(bad)
    bad_prod = 1 * base_ring(R)
  else
    bad_prod = prod(bad)
  end

  # First the ideals coming from the C/C0 quotient
  Eabs, EabstoE, _ = absolute_field(E)
  Rabs = maximal_order(Eabs)
  C, h = class_group(Rabs)
  RR = base_ring(R)
  C0 = support(D)
  CC, hh = class_group(RR)
  for p in find_gens(pseudo_inv(h), PrimesSet(2, -1))[1]
    if !(p in C0)
      push!(C0, sum(R * R(EabstoE(elem_in_nf(b))) for b in basis(p)))
    end
  end
  Q0, q0 = quo(C, [ h\ideal(Rabs, [Rabs(EabstoE\b) for b in absolute_basis(i)]) for i in C0])
  q00 = pseudo_inv(q0) * h
  PP = ideal_type(R)[]

  local F::GaloisField

  local W::Generic.QuotientModule{gfp_elem}

  if iseven(rank(L))
    for (P, e) in factor(D)
      G = genus(L, P)
      if any(i -> isodd(rank(G, i)), 1:length(G))
        continue
      elseif !isdyadic(P)
        if any(i -> iseven(scale(G, i)), 1:length(G))
          continue
        end
      else
        if any(i -> isodd(e  + scale(G, i)) || (e + scale(G, i) != G.ni[i]), 1:length(G))
          continue
        end
      end
      push!(PP, P)
    end

    if !isempty(PP)
      U, f = unit_group_fac_elem(Rabs)
      UU, ff = unit_group_fac_elem(RR)
      nnorm = hom(U, UU, GrpAbFinGenElem[ff\FacElem(nf(RR)(norm(f(U[i])))) for i in 1:ngens(U)])
      l = length(PP)
      VD = Int[ valuation(D, P) for P in PP ]
      K, k = kernel(nnorm)
      F = GF(2, cached = false)
      V = VectorSpace(F, length(PP))
      S = elem_type(V)[]
      for u in gens(K)
        z = elem_type(F)[]
        for i in 1:length(PP)
          zz = R(EabstoE(evaluate(f(k(u))))) - 1
          if iszero(zz) || (valuation(zz, PP[i]) >= VD[i])
            push!(z, F(0))
          else
            push!(z, F(1))
          end
        end
        push!(S, V(z))
      end
      #S = [ V(elem_type(F)[valuation(R(EabstoE(evaluate(f(k(u)))) - 1), PP[i]) >= VD[i] ? F(0) : F(1) for i in 1:length(PP)]) for u in gens(K)]
      _T, _ = sub(V, S)
      W, w = quo(V, _T)
      if dim(W) == 0
        PP = ideal_type(R)[]
      end
    end
  end

  Gens = Tuple{ideal_type(R), fmpz}[]

  if isempty(PP)
    S = GrpAbFinGenElem[]
    Q, q = quo(Q0, S)::Tuple{GrpAbFinGen, GrpAbFinGenMap}
    Work = isdefinite(L) ? typeof(P0)[ P0 ] : typeof(P0)[]
    p = 2
    while order(Q) > 1
      while isempty(Work)
        p = next_prime(p)
        Work = ideal_type(R)[ QQ for QQ in support(p * R) if issplit(QQ) && valuation(bad, QQ) == 0 ]
      end
      P = popfirst!(Work)
      c = (q00\P)::GrpAbFinGenElem
      o = order(q(c))::fmpz
      if !isone(o)
        push!(S, c)
        Q, q = quo(Q0, S)::Tuple{GrpAbFinGen, GrpAbFinGenMap}
        push!(Gens, (P, o))
      end
    end
  else
    ll = Int(order(Q0))
    cocycle = Matrix{elem_type(W)}(undef, ll, ll)
    for i in 1:ll
      for j in 1:ll
        cocycle = zero(W)
      end
    end
    C = collect(Q0)
    ideals = ideal_type(Rabs)[ q00(C[i]) for i in 1:length(C) ]
    for i in 1:ll
      for j in 1:ll
        ij = findfirst(isequal(C[i] * C[j]), C)
        I = ideals[i] * ideals[j] * inv(ideals[ij])
        J = I * inv(a(I))
        ok, x = isprincipal(J)
        u = f(nnorm(-(ff\FacElem(nf(RR)(norm(x))))))
        x = x * u
        @assert norm(x) == 1
        y = w(V(Int[ valuation(x - 1, PP[i]) >= VD[i] ? F(0) : F(1) for i in 1:length(PP)]))
        cocycle[i, j] = y
        cocycle[j, i] = y
      end
    end

    S = Tuple{elem_type(Q0), Generic.QuotientModuleElem{elem_type(F)}}[(id(Q0), zero(W))]
    Work = isdefinite(L) ? typeof(P0)[ P0 ] : typeof(P0)[]
    p = 2
    while length(S) != order(Q0) * length(W)
      while isempty(Work)
        p = next_prime(p)
        Work = ideal_type(R)[ QQ for QQ in support(p * R) if issplit(QQ) && valuation(bad, QQ) == 0 ]
      end
      P = popfirst!(Work)
      c = q00\P
      i = findfirst(isequal(c), C)
      I = P * inv(ideals[i])
      J = I * inv(a(I))
      ok, x = isprincipal(J)
      u = f(nnorm(-(ff\FacElem(nf(RR)(norm(x))))))
      x = x * u
      @assert norm(x) == 1
      y = V(Int[ valuation(x - 1, PP[i]) >= VD[i] ? F(0) : F(1) for i in 1:length(PP)])
      idx = findfirst(isequal(P), PP)
      if idx !== nothing
        y = V(elem_type(F)[i == idx ? y[i] : y[i] + 1] for i in 1:dim(V)) #w(V([y[idx] = y[idx] + 1
      end
      elt = (c, w(y))
      elt1 = elt
      o = 1
      siz = length(S)
      while !(elt1 in S)
        j = findfirst(isequal(elt1[1]), C)
        @assert !isnothing(j)
        for l in 1:siz
          elt2 = S[l]
          k = findfirst(isequal(elt2[1]), C)
          @assert !isnothing(k)
          prod = (elt1[1] * elt2[1], elt1[2] + elt2[2] + cycycle[j, k])
          if !(prod in S)
            push!(S, prod)
          end
        end
        elt1 = (elt[1] * elt1[1], elt[2] + elt[1] + cocycle[i, j])
        o = o + 1
      end
      @assert length(S) == siz * o
      if o != 1
        push!(Gens, (P, o))
      end
    end
  end

  if isdefinite(L)
    return Gens, true, P0
  else
    return Gens, false, P0
  end
end

function representatives(G::GenusHerm)
  return genus_representatives(representative(G))
end

################################################################################
#
#  First attempt, which mirrors Markus' Magma code
#
#  This is only used for debugging purposes
#
################################################################################

mutable struct LocalGenusSymbol{S}
  P
  data
  x
  iseven::Bool
  E
  isramified
  non_norm
end

prime(G::LocalGenusSymbol) = G.P

uniformizer(G::LocalGenusSymbol{QuadLat}) = G.x

data(G::LocalGenusSymbol) = G.data

base_field(G::LocalGenusSymbol) = G.E

function Base.show(io::IO, G::LocalGenusSymbol)
  print(io, "Local genus symbol (scale, rank, det) at\n")
  print(IOContext(io, :compact => true), G.P)
  compact = get(io, :compact, false)
  if !compact
    print(io, "\nwith base field\n")
    print(io, base_field(G))
  end
  println(io, "\nWith data ", data(G))
  !G.iseven ? println(io, "and unifomizer\n", G.x) : nothing
end

# TODO: I have to redo this

function _genus_symbol_kirschmer(L::QuadLat, p::NfOrdIdl; uniformizer = zero(order(p)))
  O = order(p)
  nf(O) != base_field(L) && throw(error("Prime ideal must be an ideal of the base field of the lattice"))
  # If you pull from cache, you might have to adjust the symbol according
  # to the uniformizer flag

  J, G, E = jordan_decomposition(L, p)
  if !iszero(uniformizer)
    unif = uniformizer
    if valuation(unif, p) != 1
      throw(error("Wrong uniformizer"))
    end
  else
    unif = elem_in_nf(Hecke.uniformizer(p))
  end

  if minimum(p) != 2
    _, _h = ResidueField(O, p)
    h = extend(_h, nf(O))
    Gs = [ h(prod(diagonal(G[i]))//unif^(E[i] * nrows(J[i]))) for i in 1:length(J)]
    @assert !(0 in Gs)
    x  = [ (nrows(J[i]), E[i], issquare(Gs[i])[1] ? 1 : -1) for i in 1:length(J)]
    return LocalGenusSymbol{QuadLat}(p, x, unif, false, base_field(L), nothing, nothing)
  else
    t = length(G)
    sL = [ minimum(iszero(g[i, j]) ? inf : valuation(g[i, j], p) for j in 1:ncols(g) for i in 1:j) for g in G]
    @assert sL == E
    e = ramification_index(p)
    aL = []
    uL = []
    wL = []
    for i in 1:t
      GG = diagonal_matrix([ j < i ? unif^(2*(sL[i] - sL[j])) * G[j] : G[j] for j in 1:t])
      D = diagonal(GG)
      m, pos = findmin([valuation(d, p) for d in D])
      if e + sL[i] <= m
        push!(aL, unif^(e + sL[i]))
      else
        push!(aL, D[pos])
      end
      push!(uL, valuation(aL[i], p))
      push!(wL, min(e + sL[i], minimum(uL[i] + quadratic_defect(d//aL[i], p) for d in D)))
    end
    fL = []
    for k in 1:(t - 1)
      exp = uL[k] + uL[k + 1]
      push!(fL, (isodd(exp) ? exp : min(quadratic_defect(aL[k] * aL[k + 1], p), uL[k] + wL[k + 1], uL[k + 1], wL[k], e + div(exp, 2) + sL[k])) - 2*sL[k])
    end
    return LocalGenusSymbol{QuadLat}(p, ([nrows(G[k]) for k in 1:t], sL, wL, aL, fL, G), unif, true, base_field(L), nothing, nothing)
  end
end

# This is the "Magma" Genus symbol
function _genus_symbol_kirschmer(L::HermLat, p; uniformizer = zero(order(p)))
  @assert order(p) == base_ring(base_ring(L))

  B, G, S = jordan_decomposition(L, p)
  R = base_ring(L)
  E = nf(R)
  K = base_field(E)
  if !isdyadic(p) || !isramified(R, p)
    sym = Tuple{Int, Int, Bool}[ (nrows(B[i]), S[i], islocal_norm(E, coeff(det(G[i]), 0), p)) for i in 1:length(B)]
  else
    P = prime_decomposition(R, p)[1][1]
    pi = E(K(Hecke.uniformizer(p)))
    sym = Tuple{Int, Int, Bool, Int, elem_type(K)}[]
    for i in 1:length(B)
      normal = (_get_norm_valuation_from_gram_matrix(G[i], P)::Int == S[i])::Bool
      GG = diagonal_matrix(dense_matrix_type(E)[pi^(max(0, S[i] - S[j])) * G[j] for j in 1:length(B)])::dense_matrix_type(E)
      v = _get_norm_valuation_from_gram_matrix(GG, P)::Int
      #_n = norm(lattice(hermitian_space(E, GG), identity_matrix(E, nrows(GG))))
      #vv = valuation(R * norm(lattice(hermitian_space(E, GG), identity_matrix(E, nrows(GG)))), P)::Int
      s = (nrows(B[i]), S[i], normal, v, coeff(det(diagonal_matrix([G[j] for j in 1:i])), 0))
      push!(sym, s)
    end
  end
  return sym
end

function _all_row_span(M)
  F = base_ring(M)
  rows = Vector{Vector{elem_type(F)}}(undef, nrows(M))
  for i in 1:nrows(M)
    rows[i] = elem_type(F)[M[i, j] for j in 1:ncols(M)]
  end
  n = nrows(M)
  it = Iterators.product([F for i in 1:n]...)
  res = Vector{Vector{elem_type(F)}}()
  for c in it
    z = Ref(c[1]) .* rows[1]
    for i in 2:n
      z = z .+ (Ref(c[i]) .* rows[i])
    end
    push!(res, z)
  end
  return res
end
