export genus, representative, rank, det, uniformizer, det_representative,
       gram_matrix, representative, genus, genera_hermitian,
       local_genera_hermitian, rank, orthogonal_sum, isinert, scales, ranks,
       dets, issplit

################################################################################
#
#  Local genus symbol
#
################################################################################

# Need to make this type stable once we have settled on a design
mutable struct LocalGenusHerm{S, T}
  E::S                                # Field
  p::T                                # prime of base_field(E)
  data::Vector{Tuple{Int, Int, Int}}  # data
  norm_val::Vector{Int}               # additional norm valuation
                                      # (for the dyadic case)
  isdyadic::Bool                      # 2 in p
  isramified::Bool                    # p ramified in E
  issplit::Bool                       # p split in E
  non_norm_rep                        # u in K*\N(E*)
  ni::Vector{Int}                     # ni for the ramified, dyadic case

  function LocalGenusHerm{S, T}() where {S, T}
    z = new{S, T}()
    return z
  end
end

local_genus_herm_type(E) = LocalGenusHerm{typeof(E), ideal_type(order_type(base_field(E)))}

################################################################################
#
#  I/O
#
################################################################################

function Base.show(io::IO, ::MIME"text/plain", G::LocalGenusHerm)
  compact = get(io, :compact, false)
  if !compact
    if isdyadic(G) && isramified(G)
       print(io, "Local genus symbol (scale, rank, det, norm) at ")
    else
      print(io, "Local genus symbol (scale, rank, det) at ")
    end
    if length(G) > 0
      print(IOContext(io, :compact => true), prime(G), ":")
      print(io, "\n")
    else
      print(IOContext(io, :compact => true), prime(G), " of rank zero")
    end
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
  return reduce(+, (rank(G, i) for i in 1:length(G)), init = Int(0))
end

@doc Markdown.doc"""
    ranks(G::LocalGenusHerm)

Given a genus symbol for Hermitian lattices over $E/K$, return the ranks of the
Jordan blocks of $G$.
"""
ranks(G::LocalGenusHerm) = map(i -> rank(G, i), 1:length(G))::Vector{Int}

@doc Markdown.doc"""
    det(G::LocalGenusHerm, i::Int) -> Int

Given a genus symbol for Hermitian lattices over $E/K$, return the determinant of the
$i$th Jordan block of $G$. This will be `1` or `-1` depending on whether the
determinant is a local norm or not.
"""
det(G::LocalGenusHerm, i::Int) = G.data[i][3]

@doc Markdown.doc"""
    det(G::LocalGenusHerm) -> Int

Given a genus symbol $G$, return the determinant of a lattice in $G$. This will be
`1` or `-1` depending on whether the determinant is a local norm or not.
"""
function det(G::LocalGenusHerm)
  return reduce(*, (det(G, i) for i in 1:length(G)), init = Int(1))
end

@doc Markdown.doc"""
    dets(G::LocalGenusHerm) -> Vector{Int}

Given a genus symbol for Hermitian lattices over $E/K$, return the determinants
of the Jordan blocks of $G$. These will be `1` or `-1` depending on whether the
determinant is a local norm or not.
"""
dets(G::LocalGenusHerm) = map(i -> det(G, i), 1:length(G))::Vector{Int}

@doc Markdown.doc"""
    discriminant(G::LocalGenusHerm, i::Int) -> Int

Given a genus symbol for Hermitian lattices over $E/K$, return the discriminant
of the $i$th Jordan block of $G$. This will be `1` or `-1` depending on whether
the discriminant is a local norm or not.
"""
function discriminant(G::LocalGenusHerm, i::Int)
  d = det(G, i)
  r = rank(G, i) % 4
  if !isramified(G) || r == 0 || r == 1 
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
    discriminant(G::LocalGenusHerm) -> Int

Given a genus symbol $G$, return the discriminant of a lattice in $G$. This will be
`1` or `-1` depending on whether the discriminant is a local norm or not.
"""
function discriminant(G::LocalGenusHerm)
  d = det(G)
  r = rank(G) % 4
  if !isramified(G) || r == 0 || r == 1
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
    norm(G::LocalGenusHerm, i::Int) -> Int

Given a dyadic genus symbol for Hermitian lattices over $E/K$ at a prime
$\mathfrak p$, return the $\mathfrak p$-valuation of the norm of the $i$th Jordan
block of $G$.
"""
norm(G::LocalGenusHerm, i::Int) = begin @assert isdyadic(G); G.norm_val[i] end # this only works if it is dyadic

#@doc Markdown.doc"""
#    norms(G::LocalGenusHerm) -> Vector{Int}
#
#Given a dyadic genus symbol for Hermitian lattices over $E/K$ at a prime
#$\mathfrak p$, return the $\mathfrak p$-valuations of the norms of the Jordan
#blocks of $G$.
#"""

@doc Markdown.doc"""
    isramified(g::localgenusherm) -> bool

Given a genus symbol for hermitian lattices at a prime $\mathfrak p$, return
whether $\mathfrak p$ is ramified.
"""
isramified(g::LocalGenusHerm) = g.isramified

@doc Markdown.doc"""
    issplit(g::localgenusherm) -> bool

Given a genus symbol for hermitian lattices at a prime $\mathfrak p$, return
whether $\mathfrak p$ is split.
"""
issplit(g::LocalGenusHerm) = g.issplit

@doc Markdown.doc"""
    isinert(g::localgenusherm) -> bool

Given a genus symbol for hermitian lattices at a prime $\mathfrak p$, return
whether $\mathfrak p$ is inert.
"""
isinert(g::LocalGenusHerm) = !g.isramified && !g.issplit

@doc Markdown.doc"""
    isdyadic(G::LocalGenusHerm) -> Bool

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
    prime(G::LocalGenusHerm) -> NfOrdIdl

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
return a generator for the largest invariant ideal of $E$ containing $\mathfrak p$.
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
    return K(uniformizer(prime(G)))
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
  d = det(G)
  v = sum(scale(G, i) * rank(G, i) for i in 1:length(G); init = 0)
  if !isramified(G)
    return uniformizer(G)^v
  end

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

@doc Markdown.doc"""
    det_representative(G::LocalGenusHerm) -> NumFieldElem

Return a representative for the norm class of the determinant of $G$.
"""
function det_representative(G::LocalGenusHerm, i::Int)
  d = det(G, i)
  v = scale(G, i) * rank(G, i)
  if !isramified(G)
    return uniformizer(G)^v
  end

  v = div(v, 2)

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
  if rank(G) == 0
    return zero_matrix(base_field(G), 0, 0)
  end
  return diagonal_matrix(dense_matrix_type(base_field(G))[gram_matrix(G, i) for i in 1:length(G)])
end

function gram_matrix(G::LocalGenusHerm, l::Int)
  i = scale(G, l)
  m = rank(G, l)
  d = det(G, l)
  E = base_field(G)
  K = base_field(E)
  p = elem_in_nf(p_uniformizer(prime(G)))
  conj = involution(E)

  if !isramified(G)
    return diagonal_matrix([E(p)^i for j in 1:m])
  end

  # ramified

  lQ = prime_decomposition(maximal_order(E), prime(G))
  @assert length(lQ) == 1 && lQ[1][2] == 2
  Q = lQ[1][1]
  pi = elem_in_nf(p_uniformizer(Q))
  H = matrix(E, 2, 2, elem_type(E)[zero(E), pi^i, conj(pi)^i, zero(E)])

  if !isdyadic(G)
    # non-dyadic
    if iseven(i)
      # According to Kir16, there the last exponent should be i/2 * (1 - m)
      lastexp = div(i, 2) * (1 - m)
      drep = det_representative(G, l)
      return diagonal_matrix(push!(elem_type(E)[E(p)^div(i, 2) for j in 1:(m - 1)], drep * E(p)^(lastexp)))
      if d == 1
        u = one(K)
      else
        u = _non_norm_rep(G)
      end
      if m == 1
        fl = islocal_norm(E, p^div(i, 2), prime(G))
        if d == -1
          return diagonal_matrix([(fl ? _non_norm_rep(G) : one(K)) * E(p)^div(i, 2)])
        else
          return diagonal_matrix([(!fl ? _non_norm_rep(G) : one(K)) * E(p)^div(i, 2)])
        end
      end
      return diagonal_matrix(push!(elem_type(E)[E(p)^div(i, 2) for j in 1:(m - 1)], u * E(p)^(div(i, 2) * (m - 1))))
    else
      return diagonal_matrix(dense_matrix_type(E)[H for j in 1:div(m, 2)])
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
  L = lattice(hermitian_space(E, gram_matrix(G)))
  S = ideal_type(base_ring(base_ring(L)))
  GType = local_genus_herm_type(E)
  symbols = get_attribute!(L, :local_genus) do
    Dict{S, GType}()
  end::Dict{S, GType}

  get!(symbols, prime(G), G)

  return L
end

################################################################################
#
#  Constructor
#
################################################################################

@doc Markdown.doc"""
    genus(HermLat, E::NumField, p::Idl, data::Vector; type = :det, check = false)
                                                              -> LocalGenusHerm

Construct the local genus symbol of hermitian lattices over $E$ at the prime ideal
$\mathfrak p$ with the invariants specified by `data`.

- If the prime ideal is good (not ramified and dyadic), the elements of `data` must 
  be `(s, r, d)::Tuple{Int, Int, Int}` where `s` is the scale, `r` the rank and
  `d` the determinant/discriminant class.

  In the unramified case, `d` is determined by `s` and `r` and can be omitted.
  Hence also `(s, r)::Tuple{Int, Int}` is allowed.

- If the prime ideal is bad (ramified and dyadic), the elements of `data` must 
  be `(s, r, d, n)::Tuple{Int, Int, Int, Int}`, where in addition `n`
  is the norm valuation.

Additional comments:
- `d` must be in `[1, -1`].
- If `type == :disc`, the parameter `d` is interpreted as the discriminant.
- Sanity checks can be disabled by setting `check = false`.
"""
genus(::Type{HermLat}, E, p, data; type, check)

# rank zero genus
function genus(::Type{HermLat}, E::S, p::T) where {S, T}
  if isramified(maximal_order(E), p) && isdyadic(p)
    return genus(HermLat, E, p, Vector{Tuple{Int, Int, Int, Int}}())
  else
    return genus(HermLat, E, p, Vector{Tuple{Int, Int, Int}}())
  end
end

# Some comments
#
# We distinguish between bad and good case
# First the good case

# This is the internal function which requires the decomposition behavior of
# the prime to be already determined and does not do any internal checks.
function _genus(::Type{HermLat}, E::S, p::T, data::Vector{Tuple{Int, Int, Int}}, is_dyadic, is_ramified, is_split) where {S, T}
  z = LocalGenusHerm{S, T}()
  z.E = E
  z.p = p
  @hassert :Lattice 1 !(is_dyadic && is_ramified)
  z.isdyadic = is_dyadic
  z.isramified = is_ramified
  z.issplit = is_split
  z.data = data
  return z
end

# This is one of the two user facing functions for the good case, namely the
# unramified case. Here the determinant/discriminant class need not be supplied.
function genus(::Type{HermLat}, E, p, data::Vector{Tuple{Int, Int}}; check::Bool = true)
  @req !isramified(maximal_order(E), p) "For dyadic primes the norm valuation has to be specified"
  if check
    @req all(data[i][2] >= 0 for i in 1:length(data)) "Ranks must be positive"
    @req all(data[i][1] < data[i + 1][1] for i in 1:length(data)-1) "Scales must be strictly increasing"
  end

  is_dyadic = isdyadic(p)

  lp = prime_decomposition(maximal_order(E), p)
  if length(lp) == 2
    is_split = true
    is_ramified = false
  else
    is_split = false
    if lp[1][2] == 1
      is_ramified = false
    else
      is_ramified = true
    end
  end

  cdata = Vector{Tuple{Int, Int, Int}}(undef, length(data))

  l = length(data)

  if !is_split
    # inert case
    for i in 1:l
      # The determinant class is the class of E(p)^(r * s) and E(p)
      # has class -1.
      if isodd(data[i][1]) && isodd(data[i][2])
        cdata[i] = (data[i][1], data[i][2], -1)
      else
        cdata[i] = (data[i][1], data[i][2], 1)
      end
    end
  else
    for i in 1:l
      # split case
      cdata[i] = (data[i][1], data[i][2], 1)
    end
  end
  return _genus(HermLat, E, p, cdata, is_dyadic, is_ramified, is_split)
end

# This is the second user facing functions for the general good case. Here the 
# determinant/discriminant class must be supplied. We also do some sanity
# checks in the unramified case concerning the det/disc.
function genus(::Type{HermLat}, E::S, p::T, data::Vector{Tuple{Int, Int, Int}}; type = :det, check::Bool = true) where {S <: NumField, T}
  @req type === :det || type === :disc "type :$type must be :disc or :det"

  if check
    @req all(data[i][2] >= 0 for i in 1:length(data)) "Ranks must be positive"
    @req all(data[i][1] < data[i + 1][1] for i in 1:length(data)-1) "Scales must be strictly increasing"
    @req all(abs(data[i][3]) == 1 for i in 1:length(data)) "Norm classes must be +/-1"
  end

  # Determine the prime decomposition
  lp = prime_decomposition(maximal_order(E), p)
  if length(lp) == 2
    is_split = true
    is_ramified = false
  else
    is_split = false
    if lp[1][2] == 1
      is_ramified = false
    else
      is_ramified = true
    end
  end

  is_dyadic = isdyadic(p)

  @req !(is_dyadic && is_ramified) "For dyadic primes the norm valuation has to be specified"

  l = length(data)

  cdata = copy(data)

  if type === :disc
    # We need to swap the sign depending on whether some rank is 2, 3 mod 4
    # and -1 is not a local norm. The latter can only happen in the ramified case
    if any(data[i][2] % 4 in [2, 3] for i in 1:l) && is_ramified
      fl = islocal_norm(E, base_field(E)(-1), p)
      if !fl
        for i in 1:l
          r = data[i][2] % 4
          if r == 2 || r == 3
            cdata[i] = (cdata[i][1], cdata[i][2], -data[i][3])
          end
        end
      end
    end
  end

  # Now check that the determinant class fits with the scale and rank.
  # There is a restriction only in the unramified case
  if check
    if !is_ramified
      if !is_split
        # inert case
        for i in 1:l
          # The determinant class is the class of E(p)^(r * s) and E(p)
          # has class -1.
          if isodd(cdata[i][1]) && isodd(cdata[i][2])
            @req cdata[i][3] == -1 "$(type === :disc ? "Discriminant" : "Determinant") class does not fit scale and rank"
          else
            @req cdata[i][3] == 1 "$(type === :disc ? "Discriminant" : "Determinant") class does not fit scale and rank"
          end
        end
      else
        for i in 1:l
          # In the split case the class must always be 1.
          @req cdata[i][3] == 1 "$(type === :disc ? "Discriminant" : "Determinant") classes must be 1"
        end
      end
    else
      # Non-dyadic ramified
      # If the scale is odd, then the rank m must be even and
      # the lattice is H(i)^(m/2), hence has determinant class
      # [-1]^(m/2)
      #
      fl = islocal_norm(E, base_field(E)(-1), p)
      for i in 1:l
        if isodd(cdata[i][1])
          @req iseven(cdata[i][2]) "Rank must be even for blocks of odd scale"
          m2 = div(cdata[i][2], 2)
          if fl
            @req cdata[i][3] == 1 "Determinant must be 1 for blocks of odd scale"
          else
            @req cdata[i][3] == (iseven(m2) ? 1 : -1) "Determinant mismatch in block $i"
          end
        end
      end
    end
  end
  # Now call the internal function
  return _genus(HermLat, E, p, cdata, is_dyadic, is_ramified, is_split)
end

# Now comes the bad case.
#
# First the internal function, which has as additonal argument the vector of norm valuations.
function _genus(::Type{HermLat}, E::S, p::T, data::Vector{Tuple{Int, Int, Int}}, norms::Vector{Int}) where {S <: NumField, T}
  z = LocalGenusHerm{S, T}()
  z.E = E
  z.p = p
  z.isdyadic = isdyadic(p)
  z.isramified = isramified(maximal_order(E), p)
  z.issplit = false
  # We test the cheap thing
  @req z.isdyadic && z.isramified "Prime must be dyadic and ramified"
  z.norm_val = norms
  z.data = data
  z.ni = _get_ni_from_genus(z)
  return z
end

# The user facing function in the bad case.
function genus(::Type{HermLat}, E::S, p::T, data::Vector{Tuple{Int, Int, Int, Int}}; type = :det, check::Bool = true) where {S <: NumField, T}
  is_dyadic = isdyadic(p)
  is_ramified = isramified(maximal_order(E), p)
  @req is_dyadic && is_ramified "Prime must be dyadic and ramified"
  @req type === :det || type === :disc "type :$type must be :disc or :det"

  cdata = Tuple{Int, Int, Int}[Base.front(v) for v in data]
  norm_val = Int[v[end] for v in data]

  if check
    @req all(data[i][1] < data[i + 1][1] for i in 1:length(data)-1) "Scales must be strictly increasing"
    @req all(abs(data[i][3]) == 1 for i in 1:length(data)) "Norm classes must be +/-1"
  end

  l = length(cdata)

  if check
    for i in 1:l
      # If the rank is odd, then n(L) * O_E = s(L), so n = 2 * s,
      # since n is the valuation in K and the extension is ramified.
      v = cdata[i]
      if isodd(v[2])
        @req 2 * norm_val[i] == v[1] """Not a valid local genus in block $(i):
                                        Scale ($(v[1])) must be twice the norm ($(norm_val[i]))"""
      end
      # TODO: We should also check using e, the valuation of the different
    end
  end

  if type === :disc && any(data[i][2] % 4 in [2, 3] for i in 1:l)
    # We need to swap the sign depending on whether some rank is 2, 3 mod 4
    # and -1 is not a local norm.
    fl = islocal_norm(E, base_field(E)(-1), p)
    if !fl
      for i in 1:l
        r = cdata[i][2] % 4
        if r == 0 || r == 1
          continue
        else
          cdata[i] = (data[i][1], data[i][2], (-1) * data[i][3])
        end
      end
    end
  end
  # Now call the internal function, no checks
  return _genus(HermLat, E, p, cdata, norm_val)
end

################################################################################
#
#  Genus symbol of a lattice
#
################################################################################

# TODO: better documentation

@doc Markdown.doc"""
    genus(L::HermLat, p::NfOrdIdl) -> LocalGenusHerm

Returns the genus of $L$ at the prime ideal $\mathfrak p$.

See [Kir16, Definition 8.3.1].
"""
function genus(L::HermLat, q)
  if typeof(q) === ideal_type(base_ring(base_ring(L)))
    # yippii, correct ideal type
    return _genus_correct_ideal_type(L, q)
  else
    if q isa fmpq || q isa Int
      # we allow this in case base_ring(base_ring(L)) == ZZ
      @req base_ring(base_ring(L)) isa FlintIntegerRing "Smaller field must be QQ"
      qq = ideal(base_ring(base_ring(L)), q)::ideal_type(base_ring(base_ring(L)))
      return _genus_correct_ideal_type(L, qq)
    end
  end
end

function _genus_correct_ideal_type(L, q)
  @assert typeof(q) === ideal_type(base_ring(base_ring(L)))
  S = ideal_type(base_ring(base_ring(L)))
  GType = local_genus_herm_type(nf(base_ring(L)))
  symbols = get_attribute!(L, :local_genus) do
    return Dict{S, GType}()
  end::Dict{S, GType}

  return get!(symbols, q) do
    _genus(L, q)
  end::GType
end

function _genus(L::HermLat, p)
  bad, sym = _genus_symbol(L, p)
  if bad
    G = genus(HermLat, nf(base_ring(L)), p, sym)
  else
    G = genus(HermLat, nf(base_ring(L)), p, [Base.front(v) for v in sym])
  end
  # Just for debugging
  @hassert :Lattice 1 begin
    if isdyadic(G) && isramified(G)
      GG = _genus_symbol_kirschmer(L, p)
      all(let G = G; i -> GG[i][4] == G.ni[i]; end, 1:length(G))
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

function _genus_symbol(L::HermLat, p)
  @assert order(p) == base_ring(base_ring(L))
  B, G, S = jordan_decomposition(L, p)
  R = base_ring(L)
  E = nf(R)
  K = base_field(E)
  local sym::Vector{Tuple{Int, Int, Int, Int}}
  bad = true
  if !isdyadic(p) || !isramified(R, p)
    # The last entry is a dummy to make the compiler happier
    sym = Tuple{Int, Int, Int, Int}[ (S[i], nrows(B[i]), islocal_norm(E, coeff(det(G[i]), 0), p) ? 1 : -1, 0) for i in 1:length(B)]
    bad = false
  else
    P = prime_decomposition(R, p)[1][1]
    pi = E(K(uniformizer(p)))
    sym = Tuple{Int, Int, Int, Int}[]
    for i in 1:length(B)
      normal = _get_norm_valuation_from_gram_matrix(G[i], P) == S[i]
     GG = diagonal_matrix(dense_matrix_type(E)[pi^(max(0, S[i] - S[j])) * G[j] for j in 1:length(B)])
      #v = _get_norm_valuation_from_gram_matrix(GG, P)
      #@assert v == valuation(R * norm(lattice(hermitian_space(E, GG), identity_matrix(E, nrows(GG)))), P)
      r = nrows(B[i]) # rank
      s = S[i] # P-valuation of scale(L_i)
      det_class = islocal_norm(E, coeff(det(G[i]), 0), p) ? 1 : -1  # Norm class of determinant
      normi = _get_norm_valuation_from_gram_matrix(G[i], P) # P-valuation of norm(L_i)
      @assert mod(normi, 2) == 0 # I only want p-valuation
      push!(sym, (s, r, det_class, div(normi, 2)))
    end
    bad = true
  end
  return bad, sym
end

################################################################################
#
#  Global genus
#
################################################################################

mutable struct GenusHerm{S, T, U, V}
  E::S
  primes::Vector{T}
  LGS::Vector{U}
  rank::Int
  signatures::V

  function GenusHerm(E::S, r, LGS::Vector{U}, signatures::V) where {S, U, V}
    K = base_field(E)
    primes = Vector{ideal_type(order_type(K))}(undef, length(LGS))

    for i in 1:length(LGS)
      primes[i] = prime(LGS[i])
      @assert r == rank(LGS[i])
    end
    z = new{S, eltype(primes), U, V}(E, primes, LGS, r, signatures)
    return z
  end
end

genus_herm_type(E) = GenusHerm{typeof(E), ideal_type(order_type(base_field(E))), local_genus_herm_type(E), Dict{InfPlc, Int}}

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

function Base.show(io::IO, ::MIME"text/plain", G::GenusHerm)
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
#  Sum of genera
#
################################################################################

function orthogonal_sum(G1::GenusHerm, G2::GenusHerm)
  @req G1.E === G2.E "Genera must have same base field"
  E = G1.E
  LGS = local_genus_herm_type(G1.E)[]
  prim = eltype(primes(G1))[]
  P1 = Set(primes(G1))
  P2 = Set(primes(G2))
  for p in union(P1, P2)
    if p in P1
      i = findfirst(g -> prime(g) == p, G1.LGS)
      g1 = G1.LGS[i]
    else
      @assert !isramified(maximal_order(E), p)
      g1 = genus(HermLat, p, [(0, rank(G1), 1)])
    end

    if p in P2
      i = findfirst(g -> prime(g) == p, G2.LGS)
      g2 = G2.LGS[i]
    else
      @assert !isramified(maximal_order(E), p)
      g2 = genus(HermLat, p, [(0, rank(G2), 1)])
    end

    g3 = orthogonal_sum(g1, g2)
    push!(prim, p)
    push!(LGS, g3)
  end
  sig1 = G1.signatures
  sig2 = G2.signatures
  g3 = merge(+, sig1, sig2)
  return genus(LGS, g3)
end

Base.:(+)(G1::GenusHerm, G2::GenusHerm) = orthogonal_sum(G1, G2)

################################################################################
#
#  Test if lattice is contained in genus
#
################################################################################

@doc Markdown.doc"""
    in(L::HermLat, G::GenusHerm) -> Bool

Test if the lattice $L$ is contained in the genus $G$.
"""
Base.in(L::HermLat, G::GenusHerm) = genus(L) == G

# This could be made more efficient

################################################################################
#
#  I/O
#
################################################################################

function Base.show(io::IO, G::GenusHerm)
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
function genus(L::Vector{<:LocalGenusHerm}, signatures::Dict{InfPlc, Int})
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
  c = get_attribute(L, :genus)
  S = ideal_type(base_ring(base_ring(L)))
  if c === nothing
    G = _genus(L)
    set_attribute!(L, :genus => G)
    return G
  else
    return c::genus_herm_type(base_field(L))
  end
end

function _genus(L::HermLat)
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

  SE = infinite_places(base_field(L))
  # Only taking real places of K which split into complex plases
  S = unique([r.base_field_place for r in SE if isreal(r.base_field_place) && !isreal(r)])
  D = diagonal(rational_span(L))
  # Only count the places with stay 
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
  _non_norm = _non_norm_primes(LGS, ignore_split = true)
  P = length(_non_norm)
  I = length([(s, N) for (s, N) in signatures if isodd(mod(N, 2))])
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

function _non_norm_primes(LGS::Vector{LocalGenusHerm{S, T}}; ignore_split = false) where {S, T}
  z = T[]
  for g in LGS
    if ignore_split && issplit(g)
      continue
    end
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
  i === nothing && throw(error("No local genus symbol at $P"))
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
  infinite_pl = [ p for p in real_places(K) if length(infinite_places(E, p)) == 1 ]
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
      el = E(_weak_approximation(infinite_pl, [N[p] >= i ? -1 : 1 for p in infinite_pl]))
      push!(D, el)
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
  v = involution(E)

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
  I = Dict([ p=>length([coeff(d, 0) for d in D if isnegative(coeff(d, 0), p)]) for p in real_places(K) if length(infinite_places(E, p)) == 1])
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
    M = locally_isometric_sublattice(M, L, p)
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
equal to `det_val`.
"""
function local_genera_hermitian(E, p, rank::Int, det_val::Int, max_scale::Int; check::Bool = true)
  #@show E, p, rank, det_val, max_scale, is_ramified
  is_ramified = isramified(maximal_order(E), p)
  is_inert = !is_ramified && length(prime_decomposition(maximal_order(E), p)) == 1
  is_split = !is_ramified && !is_inert
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
      z = Tuple{Int, Int, Int}[]
      for b in g
        # We have to be careful.
        # If p is inert, then the norm is not surjective.
        if !is_inert || iseven(b[1] * b[2])
          push!(z, (b[1], b[2], 1))
        else
          push!(z, (b[1], b[2], -1))
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

      for d in cartesian_product_iterator(dets, inplace = true)# Iterators.product(dets...)
        g2 = Vector{Tuple{Int, Int, Int}}(undef, length(g))
        for k in 1:n
          # Again the 0 for dummy purposes
          g2[k] = (g[k]..., d[k])
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

    for dn in cartesian_product_iterator(det_norms, inplace = true)
      g2 = Vector{Tuple{Int, Int, Int, Int}}(undef, length(g))
      for k in 1:n
        g2[k] = (g[k][1], g[k][2], dn[k][1], dn[k][2])
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
    genera_hermitian(E::NumField, rank::Int,
                                  signatures::Dict{InfPlc, Int},
                                  determinant::nf_elem,
                                  max_scale = nothing) -> Vector{GenusHerm}

Return all genera of Hermitian lattices over $E$ with rank `rank`, signatures
given by `signatures`, scale bounded by `max_scale` and determinant class equal
to `determinant`.
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

  local_symbols = Vector{local_genus_herm_type(E)}[]

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

  res = genus_herm_type(E)[]
  it = cartesian_product_iterator(local_symbols, inplace = true)
  for gs in it
    c = copy(gs)
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

# Return def, p, bad
# def = isdefinite(L)
# p = prime ideal of base_ring(L) which can be used for the neighbor method
# bad = bad primes of L, where L,p is not modular or p is dyadic and dividing discriminant(S)
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
  a = involution(L)
  def, P0, bad = smallest_neighbour_prime(L)

  local bad_prod::ideal_type(base_ring(R))

  if isempty(bad)
    bad_prod = 1 * base_ring(R)
  else
    bad_prod = prod(bad)
  end

  # First the ideals coming from the C/C0 quotient
  Eabs, EabstoE = absolute_simple_field(ambient_space(L))
  Rabs = maximal_order(Eabs)
  C, h = class_group(Rabs)
  RR = base_ring(R)
  C0 = support(D)
  CC, hh = class_group(RR)
  for p in find_gens(pseudo_inv(hh), PrimesSet(2, -1))[1]
    if !(p in C0)
      push!(C0, sum(R * R(EabstoE(elem_in_nf(b))) for b in basis(p)))
    end
  end
  Q0, q0 = quo(C, elem_type(C)[ h\ideal(Rabs, [Rabs(EabstoE\b) for b in absolute_basis(i)]) for i in C0])
  q00 = pseudo_inv(q0) * h
  PP = ideal_type(R)[]

  local F::GaloisField

  local W::Generic.QuotientModule{gfp_elem}

  if iseven(rank(L))
    for (P, e) in factor(D)
      p = minimum(P)
      G = genus(L, p)
      if any(i -> isodd(rank(G, i)), 1:length(G))
        continue
      elseif !isdyadic(p)
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
        push!(S, V(z)::elem_type(V))
      end
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
    Work = def ? typeof(P0)[ P0 ] : typeof(P0)[]
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
        cocycle[i,j] = zero(W)
      end
    end
    C = collect(Q0)
    ideals = ideal_type(Rabs)[ q00(C[i]) for i in 1:length(C) ]
    for i in 1:ll
      for j in 1:i
        ij = findfirst(isequal(C[i] + C[j]), C)
        Iabs = ideals[i] * ideals[j] * inv(ideals[ij])
	I = EabstoE(Iabs)
        J = I * inv(a(I))
	Jabs = EabstoE\J
        ok, x = isprincipal(Jabs)
        u = f(nnorm\(-(ff\FacElem(nf(RR)(norm(x))))))
        x = x * u
        @assert norm(x) == 1
	if evaluate(x) == 1
	  y = w(V(zeros(F,length(PP))))
	else
          y = w(V([ valuation(evaluate(x) - 1, PP[i]) >= VD[i] ? F(0) : F(1) for i in 1:length(PP)]))
        end
	cocycle[i, j] = y
        cocycle[j, i] = y
      end
    end

    S = Tuple{elem_type(Q0), Generic.QuotientModuleElem{elem_type(F)}}[(id(Q0), zero(W))]
    Work = def ? typeof(P0)[ P0 ] : typeof(P0)[]
    p = 2
    while length(S) != order(Q0) * dim(W)
      while isempty(Work)
        p = next_prime(p)
        Work = ideal_type(R)[ QQ for QQ in support(p * R) if issplit(QQ) && valuation(bad, QQ) == 0 ]
      end
      P = popfirst!(Work)
      c = q00\P
      i = findfirst(isequal(c), C)
      Iabs = P * inv(ideals[i])
      I = EabstoE(Iabs)
      J = I * inv(a(I))
      Jabs = EabstoE\J
      ok, x = isprincipal(Jabs)
      u = f(nnorm\(-(ff\FacElem(nf(RR)(norm(x))))))
      x = x * u
      @assert norm(x) == 1
      if evaluate(x) == 1
        y = w(V(zeros(F,length(PP))))
      else
        y = w(V([ valuation(evaluate(x) - 1, PP[i]) >= VD[i] ? F(0) : F(1) for i in 1:length(PP)]))
      end
      idx = findfirst(isequal(P), PP)
      if idx !== nothing
        y = V(elem_type(F)[i == idx ? y[i] + 1 : y[i]  for i in 1:dim(V)])
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

  return Gens, def, P0
end

function representatives(G::GenusHerm)
  return genus_representatives(representative(G))
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
