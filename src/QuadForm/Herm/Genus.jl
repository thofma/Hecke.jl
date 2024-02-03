################################################################################
#
#  Local genus symbol
#
################################################################################

local_genus_herm_type(E) = HermLocalGenus{typeof(E), ideal_type(order_type(base_field(E)))}

################################################################################
#
#  I/O
#
################################################################################

function Base.show(io::IO, ::MIME"text/plain", G::HermLocalGenus)
  p = prime(G)
  println(io, "Local genus symbol for hermitian lattices")
  io = pretty(io)
  print(io, Indent(), "over ", Lowercase())
  Base.show(io, MIME"text/plain"(), maximal_order(G.E))
  println(io, Dedent())
  println(IOContext(io, :compact => true), "Prime ideal: ", p)
  if length(G) in [0, 1]
    print(io, "Jordan block ")
  else
    print(io, "Jordan blocks ")
  end
  if is_dyadic(G) && is_ramified(G)
    print(io, "(scale, rank, det, norm):")
  else
    print(io, "(scale, rank, det):")
  end
  print(io, Indent())
  if length(G) == 0
    nothing
  elseif is_dyadic(G) && is_ramified(G)
    println(io)
    for i in 1:length(G)-1
      println(io, "(", scale(G, i), ", ", rank(G, i), ", ",
              det(G, i) == 1 ? "+" : "-", ", ", norm(G, i), ")")
    end
    print(io, "(", scale(G, length(G)), ", ", rank(G, length(G)), ", ",
          det(G, length(G)) == 1 ? "+" : "-", ", ", norm(G, length(G)), ")")
  else
    println(io)
    for i in 1:length(G)-1
      println(io, "(", scale(G, i), ", ", rank(G, i), ", ",
              det(G, i) == 1 ? "+" : "-",  ")")
    end
    print(io, "(", scale(G, length(G)), ", ", rank(G, length(G)), ", ",
          det(G, length(G)) == 1 ? "+" : "-",  ")")
  end
  print(io, Dedent())
end

function Base.show(io::IO, G::HermLocalGenus)
  if get(io, :supercompact, false)
    if length(G) == 0
      print(io, "Empty local hermitian genus")
    elseif is_dyadic(G) && is_ramified(G)
      for i in 1:length(G)
        print(io, "(", scale(G, i), ", ", rank(G, i), ", ",
            det(G, i) == 1 ? "+" : "-", ", ", norm(G, i), ")")
      end
    else
      for i in 1:length(G)
        print(io, "(", scale(G, i), ", ", rank(G, i),
            ", ", det(G, i) == 1 ? "+" : "-",  ")")
      end
    end
  else
    print(io, "Local genus symbol for hermitian lattices over the ", absolute_minimum(prime(G)), "-adic integers")
  end
end

################################################################################
#
#  Basic properties
#
################################################################################

@doc raw"""
    scale(g::HermLocalGenus, i::Int) -> Int

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime $\mathfrak
p$ of $\mathcal O_K$, return the $\mathfrak P$-valuation of the scale of the `i`th
Jordan block of `g`, where $\mathfrak P$ is a prime ideal of $\mathcal O_E$ lying
over $\mathfrak p$.
"""
scale(G::HermLocalGenus, i::Int) = G.data[i][1]

@doc raw"""
    scale(g::HermLocalGenus) -> AbsSimpleNumFieldOrderFractionalIdeal

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime
$\mathfrak p$ of $\mathcal O_K$, return the scale of the Jordan block of minimum
$\mathfrak P$-valuation, where $\mathfrak{P}$ is a prime ideal of $\mathcal O_E$
lying over $\mathfrak p$.
"""
function scale(g::HermLocalGenus)
  E = base_field(g)
  OE = maximal_order(E)
  P = prime_decomposition(OE, prime(g))[1][1]
  return fractional_ideal(OE, P)^(scale(g, 1))
end

@doc raw"""
    scales(g::HermLocalGenus) -> Vector{Int}

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime $\mathfrak
p$ of $\mathcal O_K$, return the $\mathfrak P$-valuation of the scales of the Jordan
blocks of `g`, where $\mathfrak P$ is a prime ideal of $\mathcal O_E$ lying over $\mathfrak p$.
"""
scales(G::HermLocalGenus) = map(i -> scale(G, i), 1:length(G))::Vector{Int}

@doc raw"""
    rank(g::HermLocalGenus, i::Int) -> Int

Given a local genus symbol `g` for hermitian lattices, return the rank of the
`i`th Jordan block of `g`.
"""
rank(G::HermLocalGenus, i::Int) = G.data[i][2]

@doc raw"""
    rank(g::HermLocalGenus) -> Int

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, return the rank of any hermitian lattice whose
$\mathfrak p$-adic completion has local genus symbol `g`.
"""
function rank(G::HermLocalGenus)
  return reduce(+, rank(G, i) for i in 1:length(G); init = Int(0))
end

@doc raw"""
    ranks(g::HermLocalGenus) -> Vector{Int}

Given a local genus symbol `g` for hermitian lattices, return the ranks of the
Jordan blocks of `g`.
"""
ranks(G::HermLocalGenus) = map(i -> rank(G, i), 1:length(G))::Vector{Int}

@doc raw"""
    det(g::HermLocalGenus, i::Int) -> Int

Given a local genus symbol `g` for hermitian lattices over $E/K$, return the determinant
of the `i`th Jordan block of `g`.

The returned value is $1$ or $-1$ depending on whether the determinant is a local norm in `K`.
"""
det(G::HermLocalGenus, i::Int) = G.data[i][3]

@doc raw"""
    det(g::HermLocalGenus) -> Int

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, return the determinant of a hermitian lattice
whose $\mathfrak p$-adic completion has local genus symbol `g`.

The returned value is $1$ or $-1$ depending on whether the determinant is a local
norm in `K`.
"""
function det(G::HermLocalGenus)
  return reduce(*, det(G, i) for i in 1:length(G); init = Int(1))
end

@doc raw"""
    dets(g::HermLocalGenus) -> Vector{Int}

Given a local genus symbol `g` for hermitian lattices over $E/K$, return the determinants
of the Jordan blocks of `g`.

The returned values are $1$ or $-1$ depending on whether the respective determinants are
are local norms in `K`.
"""
dets(G::HermLocalGenus) = map(i -> det(G, i), 1:length(G))::Vector{Int}

@doc raw"""
    discriminant(g::HermLocalGenus, i::Int) -> Int

Given a local genus symbol `g` for hermitian lattices over $E/K$, return the discriminant
of the `i`th Jordan block of `g`.

The returned value is $1$ or $-1$ depending on whether the discriminant is a local norm in `K`.
"""
function discriminant(G::HermLocalGenus, i::Int)
  d = det(G, i)
  r = rank(G, i) % 4
  if !is_ramified(G) || r == 0 || r == 1
    return d
  end
  E = base_field(G)
  fl = is_local_norm(E, base_field(E)(-1), prime(G))
  if fl
    return d
  else
    return -d
  end
end

@doc raw"""
    discriminant(g::HermLocalGenus) -> Int

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, return the discriminant of a hermitian lattice
whose $\mathfrak p$-adic completion has local genus symbol `g`.

The returned value is $1$ or $-1$ depending on whether the discriminant is a local
norm in `K`.
"""
function discriminant(G::HermLocalGenus)
  d = det(G)
  r = rank(G) % 4
  if !is_ramified(G) || r == 0 || r == 1
    return d
  end
  E = base_field(G)
  fl = is_local_norm(E, base_field(E)(-1), prime(G))
  if fl
    return d
  else
    return -d
  end
end

@doc raw"""
    norm(g::HermLocalGenus, i::Int) -> Int

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, return the $\mathfrak p$-valuation of the norm of
the `i`th Jordan block of `g`.
"""
function norm(G::HermLocalGenus, i::Int)
  if !is_ramified(G)
    # In the unramified case, the Jordan block is
    # diagonal so the norm and the scale agree. Moreover,
    # the P-valuation of p is one, so we keep the same valuations
    # too.
    return scale(G, i)
  elseif !is_dyadic(G)
    # Two cases: either the scale valuation is odd and the Jordan
    # block is a direct sum of subnormal planes. In this case, if j
    # is the scale P-valuation, the norm p-valuation is (j+1)/2.
    # Or the scale valuation is even, the Jordan block is diagonal so the
    # scale and norm are the same: in that case though the P-valuation of
    # p is two so we must divide the P-valuation of the scale by 2.
    si = scale(G, i)
    ni = div(si+1, 2)
    return ni
  else
    # Already computed at the creation of the genus symbol.
    return G.norm_val[i]
  end
end

@doc raw"""
    norms(g::HermLocalGenus) -> Vector{Int}

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, return the $\mathfrak p$-valuations of the
norms of the Jordan blocks of `g`.
"""
norms(G::HermLocalGenus) = map(i -> norm(G, i), 1:length(G))::Vector{Int}

@doc raw"""
    norm(g::HermLocalGenus) -> AbsSimpleNumFieldOrderFractionalIdeal

Return the norm of `g`, i.e. the norm of any of its representatives.  

Given a local genus symbol `g` of hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, it norm is computed as the norm of the Jordan block of minimum
$\mathfrak p$-valuation.
"""
function norm(G::HermLocalGenus)
  p = prime(G)
  OK = order(p)
  return fractional_ideal(OK, p)^(minimum(norms(G)))
end

@doc raw"""
    is_ramified(g::HermLocalGenus) -> Bool

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, return whether $\mathfrak p$ is ramified in
$\mathcal O_E$.
"""
is_ramified(g::HermLocalGenus) = g.is_ramified

@doc raw"""
    is_split(g::HermLocalGenus) -> Bool

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, return whether $\mathfrak p$ is split in
$\mathcal O_E$.
"""
is_split(g::HermLocalGenus) = g.is_split

@doc raw"""
    is_inert(g::HermLocalGenus) -> Bool

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, return whether $\mathfrak p$ is inert in
$\mathcal O_E$.
"""
is_inert(g::HermLocalGenus) = !g.is_ramified && !g.is_split

@doc raw"""
    is_dyadic(g::HermLocalGenus) -> Bool

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, return whether $\mathfrak p$ is dyadic.
"""
is_dyadic(G::HermLocalGenus) = G.is_dyadic

@doc raw"""
    length(g::HermLocalGenus) -> Int

Given a local genus symbol `g` for hermitian lattices, return the number of Jordan blocks
of `g`.
"""
length(G::HermLocalGenus) = length(G.data)

@doc raw"""
    base_field(g::HermLocalGenus) -> NumField

Given a local genus symbol `g` for hermitian lattices over $E/K$, return `E`.
"""
base_field(G::HermLocalGenus) = G.E

@doc raw"""
    prime(g::HermLocalGenus) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, return $\mathfrak p$.
"""
prime(G::HermLocalGenus) = G.p

################################################################################
#
#  A local non-norm
#
################################################################################

# If G is defined over E/K at a prime p of O_K, this returns an unit in K which is
# not a local norm at p.
function _non_norm_rep(G::HermLocalGenus)
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

@doc raw"""
    uniformizer(g::HermLocalGenus) -> NumFieldElem

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, return a generator for the largest ideal of $\mathcal O_E$
containing $\mathfrak p$ and invariant under the action of the non-trivial involution
of `E`.
"""
function uniformizer(G::HermLocalGenus)
  E = base_field(G)
  K = base_field(E)
  if is_ramified(G)
    lP = prime_decomposition(maximal_order(E), prime(G))
    @assert length(lP) == 1 && lP[1][2] == 2
    Q = lP[1][1]
    pi = p_uniformizer(Q)
    A = automorphism_list(E)
    uni = A[1](elem_in_nf(pi)) * A[2](elem_in_nf(pi))
    @assert iszero(coeff(uni, 1))
    @assert is_local_norm(E, coeff(uni , 0), prime(G))
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
function _get_ni_from_genus(G::HermLocalGenus)
  @assert is_ramified(G)
  @assert is_dyadic(G)
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

# If p does not ramify in E, then the determinant of G is pi^v where pi is a
# uniformizer of p. Otherwise pi is a local norm and the class of the
# determinant of G is the same as u*pi^(v//2) where u is 1 if d == 1, otherwise
# it is a non local norm. Indeed the valuation is with respect to p = P^2
# but the scale is with respect to P and thus the determinant of a G is
# represented P^(scale*rank) = p^(scale*rank/2) times u.
@doc raw"""
    det_representative(g::HermLocalGenus) -> NumFieldElem

Given a local genus symbol `g` for hermitian lattices over $E/K$, return a
representative of the norm class of the determinant of `g` in $K^{\times}$.
"""
function det_representative(G::HermLocalGenus)
  d = det(G)
  v = sum(scale(G, i) * rank(G, i) for i in 1:length(G); init = 0)
  if !is_ramified(G)
    return uniformizer(G)^v
  end

  if is_ramified(G)
    v = div(v, 2)
  end
  if d == 1
    u = one(base_field(base_field(G)))
  else
    @assert is_ramified(G)
    u = _non_norm_rep(G)
  end
  return u * uniformizer(G)^v
end

@doc raw"""
    det_representative(g::HermLocalGenus, i::Int) -> NumFieldElem

Given a local genus symbol `g` for hermitian lattices over $E/K$, return a
representative of the norm class of the determinant of the `i`th Jordan block of
`g` in $K^{\times}$.
"""
function det_representative(G::HermLocalGenus, i::Int)
  d = det(G, i)
  v = scale(G, i) * rank(G, i)
  if !is_ramified(G)
    return uniformizer(G)^v
  end

  v = div(v, 2)

  if d == 1
    u = one(base_field(base_field(G)))
  else
    @assert is_ramified(G)
    u = _non_norm_rep(G)
  end
  return u * uniformizer(G)^v
end

################################################################################
#
#  Gram matrix
#
################################################################################

@doc raw"""
    gram_matrix(g::HermLocalGenus) -> MatElem

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, return a Gram matrix `M` of `g`, with coefficients
in `E`.`M` is such that any hermitian lattice over $E/K$ with Gram matrix `M` satisfies
that the local genus symbol of its completion at $\mathfrak p$ is `g`.
"""
function gram_matrix(G::HermLocalGenus)
  if rank(G) == 0
    return zero_matrix(base_field(G), 0, 0)
  end
  return diagonal_matrix(dense_matrix_type(base_field(G))[gram_matrix(G, i) for i in 1:length(G)])
end

@doc raw"""
    gram_matrix(g::HermLocalGenus, i::Int) -> MatElem

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, return a Gram matrix `M` of the `i`th Jordan block
of `g`, with coefficients in `E`. `M` is such that any hermitian lattice over $E/K$
with Gram matrix `M` satisfies that the local genus symbol of its completion at
$\mathfrak p$ is equal to the `i`th Jordan block of `g`.
"""
function gram_matrix(G::HermLocalGenus, l::Int)
  i = scale(G, l)
  m = rank(G, l)
  d = det(G, l)
  E = base_field(G)
  K = base_field(E)
  p = elem_in_nf(p_uniformizer(prime(G)))
  conj = involution(E)

  if !is_ramified(G)
    return diagonal_matrix([E(p)^i for j in 1:m])
  end

  # ramified

  lQ = prime_decomposition(maximal_order(E), prime(G))
  @assert length(lQ) == 1 && lQ[1][2] == 2
  Q = lQ[1][1]
  pi = elem_in_nf(p_uniformizer(Q))
  H = matrix(E, 2, 2, elem_type(E)[zero(E), pi^i, conj(pi)^i, zero(E)])

  if !is_dyadic(G)
    # non-dyadic
    if iseven(i)
      # According to Kir16, there the last exponent should be i/2 * (1 - m)
      lastexp = div(i, 2) * (1 - m)
      drep = det_representative(G, l)
      return diagonal_matrix(push!(elem_type(E)[E(p)^div(i, 2) for j in 1:(m - 1)], drep * E(p)^(lastexp)))
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
    if is_local_norm(E, discG*p^(-m * div(i, 2)), prime(G))
      u = K(1)
    else
      u = _non_norm_rep(G)
    end

    U = matrix(E, 1, 1, [u * p^(div(i, 2))])
    return diagonal_matrix(append!(typeof(U)[U], [H for j in 1:r]))
  else
    # even rank
    r = div(m, 2) - 1
    if is_local_norm(E, K((-1)^div(m, 2)), prime(G)) == (d == 1)
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

@doc raw"""
    representative(g::HermLocalGenus) -> HermLat

Given a local genus symbol `g` for hermitian lattices over $E/K$ at a prime ideal
$\mathfrak p$ of $\mathcal O_K$, return a hermitian lattice over $E/K$ whose
completion at $\mathfrak p$ admits `g` as local genus symbol.
"""
function representative(G::HermLocalGenus)
  E = base_field(G)
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

@doc raw"""
    genus(HermLat, E::NumField, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, data::Vector; type::Symbol = :det,
		                                           check::Bool = true)
                                                                 -> HermLocalGenus

Construct the local genus symbol `g` for hermitian lattices over the algebra `E`,
with base field $K$, at the prime ideal `p` of $\mathcal O_K$. Its invariants are
specified by `data`.

- If the prime ideal is good (not ramified-and-dyadic), the elements of `data` must
  be `(s, r, d)::Tuple{Int, Int, Int}` where `s` refers to the scale $\mathfrak P$-valuation,
  `r` the rank and `d` the determinant/discriminant class of a Jordan block of `g`, where
  $\mathfrak P$ is a prime ideal of $\mathcal O_E$ lying over `p`.

  In the unramified case, `d` is determined by `s` and `r` and can be omitted.
  Hence also `(s, r)::Tuple{Int, Int}` is allowed.

- If the prime ideal is bad (ramified and dyadic), the elements of `data` must
  be `(s, r, d, n)::Tuple{Int, Int, Int, Int}`, where in addition `n`
  refers to the norm `p`-valuation.

Additional comments:
- `d` must be in $\{[1, -1\}$;
- If `type == :disc`, the parameter `d` is interpreted as the discriminant;
- Sanity checks can be disabled by setting `check == false`.
"""
genus(::Type{HermLat}, E, p, data; type, check)

# rank zero genus
function genus(::Type{HermLat}, E::S, p::T) where {S, T}
  if is_ramified(maximal_order(E), p) && is_dyadic(p)
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
  z = HermLocalGenus{S, T}()
  z.E = E
  z.p = p
  @hassert :Lattice 1 !(is_dyadic && is_ramified)
  z.is_dyadic = is_dyadic
  z.is_ramified = is_ramified
  z.is_split = is_split
  keep = Int[i for (i, s) in enumerate(data) if s[2] != 0]  # We keep only blocks of non-zero rank
  z.data = data[keep]
  return z
end

# This is one of the two user facing functions for the good case, namely the
# unramified case. Here the determinant/discriminant class need not be supplied.
function genus(::Type{HermLat}, E, p, data::Vector{Tuple{Int, Int}}; check::Bool = true)
  @req !Hecke.is_ramified(maximal_order(E), p) "For dyadic primes the norm valuation has to be specified"
  if check
    @req all(data[i][2] >= 0 for i in 1:length(data)) "Ranks must be positive"
    @req all(data[i][1] < data[i + 1][1] for i in 1:length(data)-1) "Scales must be strictly increasing"
  end

  is_dyadic = Hecke.is_dyadic(p)

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

  is_dyadic = Hecke.is_dyadic(p)

  @req !(is_dyadic && is_ramified) "For dyadic primes the norm valuation has to be specified"

  l = length(data)

  cdata = copy(data)

  if type === :disc
    # We need to swap the sign depending on whether some rank is 2, 3 mod 4
    # and -1 is not a local norm. The latter can only happen in the ramified case
    if any(data[i][2] % 4 in [2, 3] for i in 1:l) && is_ramified
      fl = is_local_norm(E, base_field(E)(-1), p)
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
      fl = is_local_norm(E, base_field(E)(-1), p)
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
# First the internal function, which has as additional argument the vector of norm valuations.
function _genus(::Type{HermLat}, E::S, p::T, data::Vector{Tuple{Int, Int, Int}}, norms::Vector{Int}) where {S <: NumField, T}
  z = HermLocalGenus{S, T}()
  z.E = E
  z.p = p
  z.is_dyadic = is_dyadic(p)
  z.is_ramified = is_ramified(maximal_order(E), p)
  z.is_split = false
  # We test the cheap thing
  @req z.is_dyadic && z.is_ramified "Prime must be dyadic and ramified"
  keep = Int[i for (i, s) in enumerate(data) if s[2] != 0]    # We only keep the blocks of non-zero rank
  z.norm_val = norms[keep]
  z.data = data[keep]
  z.ni = _get_ni_from_genus(z)
  return z
end

# The user facing function in the bad case.
function genus(::Type{HermLat}, E::S, p::T, data::Vector{Tuple{Int, Int, Int, Int}}; type = :det, check::Bool = true) where {S <: NumField, T}
  is_dyadic = Hecke.is_dyadic(p)
  is_ramified = Hecke.is_ramified(maximal_order(E), p)
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
    fl = is_local_norm(E, base_field(E)(-1), p)
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
#  Local genus symbol of a lattice
#
################################################################################

# TODO: better documentation

@doc raw"""
    genus(L::HermLat, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> HermLocalGenus

Return the local genus symbol `g` for hermitian lattices over $E/K$ of the completion
of the hermitian lattice `L` at the prime ideal `p` of $\mathcal O_K$.
"""
function genus(L::HermLat, q)
  if typeof(q) === ideal_type(base_ring(base_ring(L)))
    # yippii, correct ideal type
    return _genus_correct_ideal_type(L, q)
  else
    if q isa QQFieldElem || q isa Int
      # we allow this in case base_ring(base_ring(L)) == ZZ
      @req base_ring(base_ring(L)) isa ZZRing "Smaller field must be QQ"
      qq = ideal(base_ring(base_ring(L)), q)::ideal_type(base_ring(base_ring(L)))
      return _genus_correct_ideal_type(L, qq)
    end
  end
end

function _genus_correct_ideal_type(L, q)
  @assert typeof(q) === ideal_type(base_ring(base_ring(L)))
  S = ideal_type(base_ring(base_ring(L)))
  GType = local_genus_herm_type(base_field(L))
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
    G = genus(HermLat, base_field(L), p, sym)
  else
    G = genus(HermLat, base_field(L), p, [Base.front(v) for v in sym])
  end
  # Just for debugging
  @hassert :Lattice 1 begin
    if is_dyadic(G) && is_ramified(G)
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

@doc raw"""
    in(L::HermLat, g::HermLocalGenus) -> Bool

Return whether `g` and the local genus symbol of the completion of the hermitian
lattice `L` at `prime(g)` agree. Note that `L` being in `g` requires both `L` and
`g` to be defined over the same extension $E/K$.
"""
Base.in(L::HermLat, G::HermLocalGenus) = base_field(L) === base_field(G) && genus(L, prime(G)) == G

################################################################################
#
#  Equality and hash
#
################################################################################

@doc raw"""
    ==(g1::HermLocalGenus, g2::HermLocalGenus) -> Bool

Given two local genus symbols `g1` and `g2`, return whether their respective Jordan
decompositions are of the same Jordan type. Note that equality requires `g1` and `g2`
to be defined over the same extension $E/K$ and at the same prime ideal $\mathfrak p$
of $\mathcal O_K$.
"""
function ==(G1::HermLocalGenus, G2::HermLocalGenus)
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

  if !is_ramified(G1) # split or unramified
    return true
    # Everything is normal and the Jordan decomposition types agree
    #return all(det(G1, i) == det(G2, i) for i in 1:t)
  end

  if is_ramified(G1) && !is_dyadic(G1) # ramified, but not dyadic
    # If s(L_i) is odd, then L_i = H(s(L_i))^(rk(L_i)/2) = H(s(L_i'))^(rk(L_i')/2) = L_i'
    # So all L_i, L_i' are locally isometric, in particular L_i is normal if and only if L_i' is normal
    # If s(L_i) = s(L_i') is even, then both L_i and L_i' have orthogonal bases, so they are
    # in particular normal.

    # Thus we only have to check Theorem 3.3.6 4.
    return all(det(G1, i) == det(G2, i) for i in 1:t if iseven(scale(G1, i)))
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

function Base.hash(g::HermLocalGenus, u::UInt)
  u = Base.hash(base_field(g), u)   # We do equality only over the same parent base field
  u = Base.hash(prime(g), u)
  # In any case, scale valuations and rank must agree
  h = reduce(xor, (hash(s[1:2]) for s in g.data), init = hash(det(g)))

  # In the split and unramified cases, we have collected all the invariants.
  # Otherwise, we need to split between dyadic and non-dyadic case. For the
  # non-dyadic case, we have only one set of invariants to consider.
  # For the dyadic case, we can't make it exhaustive but there are two sets of
  # invariants we can attach to the local genus symbols.
  if is_ramified(g)
    if !is_dyadic(g)
      # Ramified & non-dyadic: the determinants at the block of even scale are
      # invariants for the local genus symbol. At that point, if the symbols
      # share blocks with same scales and ranks, they should also share those
      # determinant value.
      # See equality test above
      h = reduce(xor, (hash(s[3]) for s in g.data if iseven(s[1])), init = h)
    else
      # Ramified & dyadic: the only things that are invariant are the values of
      # the ni's and the blocks for which the scale valuations are twice the
      # norm valuations.
      # See equality test above
      h = reduce(xor, (hash(g.data[i][1] == 2*g.norm_val[i]) for i = 1:length(g.data)), init = h)
      h = xor(h, hash(g.ni))
    end
  end
  return xor(h, u)
end

function _genus_symbol(L::HermLat, p)
  @assert order(p) == base_ring(base_ring(L))
  B, G, S = jordan_decomposition(L, p)
  R = base_ring(L)
  E = nf(R)
  K = base_field(E)
  local sym::Vector{Tuple{Int, Int, Int, Int}}
  bad = true
  if !is_dyadic(p) || !is_ramified(R, p)
    # The last entry is a dummy to make the compiler happier
    sym = Tuple{Int, Int, Int, Int}[ (S[i], nrows(B[i]), is_local_norm(E, coeff(det(G[i]), 0), p) ? 1 : -1, 0) for i in 1:length(B)]
    bad = false
  else
    P = prime_decomposition(R, p)[1][1]
    pi = E(K(uniformizer(p)))
    sym = Tuple{Int, Int, Int, Int}[]
    for i in 1:length(B)
      normal = _get_norm_valuation_from_gram_matrix(G[i], P) == S[i]
      GG = diagonal_matrix(dense_matrix_type(E)[pi^(max(0, S[i] - S[j])) * G[j] for j in 1:length(B)])
      r = nrows(B[i]) # rank
      s = S[i] # P-valuation of scale(L_i)
      det_class = is_local_norm(E, coeff(det(G[i]), 0), p) ? 1 : -1  # Norm class of determinant
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
#  Sum of local genera
#
################################################################################

@doc raw"""
    direct_sum(g1::HermLocalGenus, g2::HermLocalGenus) -> HermLocalGenus

Given two local genus symbols `g1` and `g2` for hermitian lattices over $E/K$
at the same prime ideal $\mathfrak p$ of $\mathcal O_K$, return their direct
sum. It corresponds to the local genus symbol of the $\mathfrak p$-adic completion
of the direct sum of respective representatives of `g1` and `g2`.
"""
function direct_sum(G1::HermLocalGenus, G2::HermLocalGenus)
  @req prime(G1) == prime(G2) "Local genera must have the same prime ideal"
  if !G1.is_dyadic || !G2.is_ramified
    return _direct_sum_easy(G1, G2)
  else
    L1 = representative(G1)
    L2 = representative(G2)
    L3, = direct_sum(L1, L2)
    return genus(L3, prime(G1))
  end
end

function _direct_sum_easy(G1::HermLocalGenus, G2::HermLocalGenus)
  # We do a merge sort
  i1 = 1
  i2 = 1
  z = Tuple{Int, Int, Int}[]
  while i1 <= length(G1) && i2 <= length(G2)
    if scale(G1, i1) < scale(G2, i2)
      push!(z, G1.data[i1])
      i1 += 1
    elseif scale(G2, i2) < scale(G1, i1)
      push!(z, G2.data[i2])
      i2 += 1
    else
      @assert scale(G1, i1) == scale(G2, i2)
      push!(z, (scale(G1, i1), rank(G1, i1) + rank(G2, i2), det(G1, i1) * det(G2, i2)))
      i1 += 1
      i2 += 1
    end
  end

  if i1 <= length(G1)
    append!(z, G1.data[i1:length(G1)])
  end

  if i2 <= length(G2)
    append!(z, G2.data[i2:length(G2)])
  end

  return genus(HermLat, base_field(G1), prime(G1), z)
end

################################################################################
#
#  Global genus
#
################################################################################

genus_herm_type(E) = HermGenus{typeof(E), ideal_type(order_type(base_field(E))), local_genus_herm_type(E), Dict{place_type(base_field(E)), Int}}

################################################################################
#
#  I/O
#
################################################################################

function Base.show(io::IO, ::MIME"text/plain", G::HermGenus)
  println(io, "Genus symbol for hermitian lattices")
  io = pretty(io)
  print(io, Indent(), "over ", Lowercase())
  Base.show(io, MIME"text/plain"(), maximal_order(G.E))
  println(io, Dedent())
  sig = G.signatures
  lgs = G.LGS
  if length(sig) == 1
    print(io, "Signature: ")
  else
    print(io, "Signatures: ")
  end
  print(io, Indent())
  for (pl, v) in sig
    println(io)
    print(IOContext(io, :supercompact =>true), Lowercase(), pl)
    print(io, " => ")
    print(io, v)
  end
  print(io, Dedent())
  if length(lgs) == 1
    print(io, "\n", "Local symbol:")
  else
    print(io, "\n", "Local symbols:")
  end
  print(io, Indent())
  for g in G.LGS
    println(io)
    print(IOContext(io, :compact => true), prime(g), " => ")
    print(IOContext(io, :supercompact => true), Lowercase(), g)
  end
  print(io, Dedent())
end

function show(io::IO, G::HermGenus)
  if get(io, :supercompact, false)
    print(io, "Genus symbol for hermitian lattices")
  else
    io = pretty(io)
    print(io, "Genus symbol for hermitian lattices of rank $(rank(G)) over ")
    print(IOContext(io, :supercompact => true), Lowercase(), maximal_order(G.E))
  end
end

function _print_short(io::IO, a::ArbFieldElem)
  r = BigFloat(a)
  s = string(r)
  if length(s) >= 10
    ss = s[1:9] * "…"
  else
    ss = s
  end
  print(io, ss)
end

function _print_short(io::IO, a::AcbFieldElem)
  _print_short(io, real(a))
  if !iszero(imag(a))
    print(io, " + ")
    _print_short(io, imag(a))
    print(io, " * i")
  end
end

################################################################################
#
#  Basic properties
#
################################################################################

@doc raw"""
    base_field(G::HermGenus) -> NumField

Given a global genus symbol `G` for hermitian lattices over $E/K$, return `E`.
"""
base_field(G::HermGenus) = G.E

@doc raw"""
    primes(G::HermGenus) -> Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}

Given a global genus symbol `G` for hermitian lattices over $E/K$, return
the list of prime ideals of $\mathcal O_K$ at which `G` has a local genus symbol.
"""
primes(G::HermGenus) = G.primes

@doc raw"""
    signatures(G::HermGenus) -> Dict{InfPlc, Int}

Given a global genus symbol `G` for hermitian lattices over $E/K$, return
the signatures at the infinite places of `K`. For each real place, it is
given by the negative index of inertia of the Gram matrix of the rational span of
a hermitian lattice whose global genus symbol is `G`.

The output is given as a dictionary with keys the infinite places of `K` and value
the corresponding signatures.
"""
signatures(G::HermGenus) = G.signatures

@doc raw"""
    rank(G::HermGenus) -> Int

Return the rank of any hermitian lattice with global genus symbol `G`.
"""
rank(G::HermGenus) = G.rank

function _scale(G::HermGenus)
  I = maximal_order(base_field(base_field(G)))
  for p in primes(G)
    s = minimum(scales(G[p]))
    I *= fractional_ideal(p)^s
  end
  return I
end

@doc raw"""
    scale(G::HermGenus) -> AbsSimpleNumFieldOrderFractionalIdeal

Return the scale ideal of any hermitian lattice with global genus symbol `G`.
"""
function scale(G::HermGenus)
  OE = maximal_order(base_field(G))
  I = prod(scale(g) for g in G.LGS; init = fractional_ideal(OE, [elem_in_nf(OE(1))]))
  return I
end

@doc raw"""
    norm(G::HermGenus) -> AbsSimpleNumFieldOrderFractionalIdeal

Return the norm ideal of any hermitian lattice with global genus symbol `G`.
"""
function norm(G::HermGenus)
  OK = base_ring(maximal_order(base_field(G)))
  I = prod(norm(g) for g in G.LGS; init = fractional_ideal(OK, [elem_in_nf(OK(1))]))
  return I
end

@doc raw"""
    is_integral(G::HermGenus) -> Bool

Return whether `G` defines a genus of integral hermitian lattices.
"""
is_integral(G::HermGenus) = is_integral(_scale(G))

@doc raw"""
    local_symbols(G::HermGenus) -> Vector{HermLocalGenus}

Given a global genus symbol of hermitian lattices, return its
associated local genus symbols.
"""
local_symbols(G) = copy(G.LGS)

################################################################################
#
#  Equality and hash
#
################################################################################

@doc raw"""
    ==(G1::HermGenus, G2::HermGenus) -> Bool

Given two global genus symbols `G1` and `G2` for hermitian lattices, return whether
they share the same local genus symbols. Note that equality requires `G1` and `G2`
to be defined over the same extension $E/K$.
"""
function ==(G1::HermGenus, G2::HermGenus)
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

function Base.hash(G::HermGenus, u::UInt)
  u = Base.hash(base_field(G), u)   # We only compare symbols over the same parent base field
  # According to the theory/definition, global genus symbols are uniquely
  # determined by their signatures (local infinite data) and their local symbols
  # (local finite data).
  h = reduce(xor, (hash(x) for x in local_symbols(G)), init = hash(signatures(G)))
  return xor(h, u)
end

################################################################################
#
#  Sum of global genera
#
################################################################################

@doc raw"""
    direct_sum(G1::HermGenus, G2::HermGenus) -> HermGenus

Given two global genus symbols `G1` and `G2` for hermitian lattices over $E/K$,
return their direct sum. It corresponds to the global genus symbol of the
direct sum of respective representatives of `G1` and `G2`.
"""
function direct_sum(G1::HermGenus, G2::HermGenus)
  @req G1.E === G2.E "Genera must have same base field"
  E = G1.E
  LGS = local_genus_herm_type(G1.E)[]
  prim = eltype(primes(G1))[]
  P1 = Set(primes(G1))
  P2 = Set(primes(G2))
  for p in union!(P1, P2)
    g1 = G1[p]
    g2 = G2[p]
    g3 = direct_sum(g1, g2)
    push!(prim, p)
    push!(LGS, g3)
  end
  sig1 = G1.signatures
  sig2 = G2.signatures
  g3 = merge(+, sig1, sig2)
  # For genera of hermitian lattices, are bad all primes dividing 2 and those
  # dividing the discriminant of the field extension (discriminant of the
  # maximal order of the top field in E/K).
  bd = union!(support(2*maximal_order(base_field(E))), support(discriminant(maximal_order(E))))
  # We keep only the local symbols which are defined over bad primes or which
  # are not unimodular.
  # Unimodular <=> There is only one Jordan block, and it is a scale valuation 0
  filter!(g -> (prime(g) in bd) || (scales(g) != Int[0]), LGS)
  return genus(LGS, g3)
end

Base.:(+)(G1::HermGenus, G2::HermGenus) = direct_sum(G1, G2)

################################################################################
#
#  Test if lattice is contained in global genus
#
################################################################################

@doc raw"""
    in(L::HermLat, G::HermGenus) -> Bool

Return whether `G` and the global genus symbol of the hermitian lattice `L` agree.
"""
Base.in(L::HermLat, G::HermGenus) = genus(L) == G

# This could be made more efficient

################################################################################
#
#  Constructor
#
################################################################################

@doc raw"""
    genus(S::Vector{HermLocalGenus}, signatures) -> HermGenus

Given a set of local genus symbols `S`  and a set of signatures `signatures`,
return the corresponding global genus symbol `G`. Note that the local genus symbols
in `S` must have the same rank which is also, therefore, the rank of `G`.

This constructor requires `S` to be non empty, the signatures to be non negative and
that the local invariants respect the product formula for Hilbert symbols.

`signatures` can be a dictionary with keys infinite places and values the
corresponding signatures, or a list of tuples $(::InfPlc, ::Int)$.
"""
genus(S::Vector{HermLocalGenus}, signatures)

function genus(L::Vector{<:HermLocalGenus}, signatures::Dict{<:InfPlc, Int})
  @assert !isempty(L)
  @assert all(N >= 0 for (_, N) in signatures)
  if !_check_global_genus(L, signatures)
    error("Invariants violate the product formula.")
  end
  r = rank(first(L))
  @req all(g -> rank(g) == r, L) "Local genus symbols must have the same rank"
  E = base_field(first(L))
  @req all(g -> base_field(g) == E, L) "Local genus symbols must be defined over the same extension E/K"
  bd = union!(support(2*maximal_order(base_field(E))), support(discriminant(maximal_order(E))))
  filter!(g -> (prime(g) in bd) || (scales(g) != Int[0]), L)
  return HermGenus(E, r, L, signatures)
end

function genus(L::Vector, signatures::Vector{Tuple{T, Int}}) where {T <: InfPlc}
  return genus(L, Dict(signatures))
end

@doc raw"""
    genus(L::HermLat) -> HermGenus

Return the global genus symbol `G` of the hermitian lattice `L`. `G` satisfies:
- its local genus symbols correspond to those of the completions of `L` at the bad
  prime ideals of `L`, i.e. the prime ideals dividing either the scale of `L`, or the
  volume of `L`, or the discriminant of $\mathcal O_E$, and also the dyadic prime
  ideals of $\mathcal O_K$;
- signatures are those of the Gram matrix of the rational span of `L`. They are given
  at the real infinite places of `K` which split into complex places of `E`.
"""
@attr genus_herm_type(base_field(L)) function genus(L::HermLat)
  return _genus(L)
end

function _genus(L::HermLat)
  bad = bad_primes(L; discriminant = true, dyadic = true)

  K = base_field(L)
  k = base_field(K)
  SE = filter(!is_real, infinite_places(K))
  # Only taking real places of K which split into complex places
  S = unique([restrict(r, k) for r in SE if is_real(restrict(r, k)) && !is_real(r)])
  D = diagonal(rational_span(L))
  # Only count the places with stay
  signatures = Dict{eltype(S), Int}(s => count(d -> is_negative(d, s), D) for s in S)
  return genus([genus(L, p) for p in bad], signatures)
end

################################################################################
#
#  Consistency check
#
################################################################################

function _check_global_genus(LGS, signatures)
  _non_norm = _non_norm_primes(LGS, ignore_split = true)
  P = length(_non_norm)
  I = count(v -> isodd(mod(v[2], 2)), signatures)
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

function _non_norm_primes(LGS::Vector{HermLocalGenus{S, T}}; ignore_split = false) where {S, T}
  z = T[]
  for g in LGS
    if ignore_split && is_split(g)
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

function Base.getindex(G::HermGenus, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  @req is_prime(P) "Ideal must be prime"
  E = base_field(G)
  i = findfirst(isequal(P), G.primes)
  if i === nothing
    if is_ramified(maximal_order(E), P) && is_dyadic(P)
      return genus(HermLat, E, P, Tuple{Int, Int, Int, Int}[(0, rank(G), 1, 0)])
    else
      return genus(HermLat, E, P, Tuple{Int, Int, Int}[(0, rank(G), 1)])
    end
  end
  return G.LGS[i]
end

################################################################################
#
#  Compute representatives of global genera
#
################################################################################

function _hermitian_form_with_invariants(E, dim, P, N)
  K = base_field(E)
  R = maximal_order(K)
  @req all(n -> n in 0:dim, values(N)) "Number of negative entries is impossible"
  infinite_pl = [ p for p in real_places(K) if length(extend(p, E)) == 1 ]
  length(N) != length(infinite_pl) && error("Wrong number of real places")
  S = maximal_order(E)
  prim = [ p for p in P if length(prime_decomposition(S, p)) == 1 ] # only take non-split primes
  I = [ p for p in keys(N) if isodd(N[p]) ]
  !iseven(length(I) + length(P)) && error("Invariants do not satisfy the product formula")
  e = gen(E)
  x = 2 * e - trace(e)
  b = coeff(x^2, 0) # b = K(x^2)
  a = _find_quaternion_algebra(b, prim, I)
  D = elem_type(E)[]
  for i in 1:(dim - 1)
    if length(I) == 0
      push!(D, one(E))
    else
      el = E(_weak_approximation(infinite_pl, [N[p] >= i ? -1 : 1 for p in infinite_pl]))
      push!(D, el)
    end
  end
  push!(D, a * prod(D; init = one(E)))
  Dmat = diagonal_matrix(D)
  dim0, P0, N0 = _hermitian_form_invariants(Dmat)
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
    if is_local_norm(E, d, p)
      continue
    end
    P[p] = true
  end
  for p in keys(factor(discriminant(maximal_order(E))))
    if is_local_norm(E, d, p)
      continue
    end
    P[p] = true
  end
  D = diagonal(_gram_schmidt(M, v)[1])
  I = Dict([ p=>length([coeff(d, 0) for d in D if is_negative(coeff(d, 0), p)]) for p in real_places(K) if length(extend(p, E)) == 1])
  return ncols(M), collect(keys(P)), I
end

@doc raw"""
    representative(G::HermGenus) -> HermLat

Given a global genus symbol `G` for hermitian lattices over $E/K$, return a hermitian
lattice over $E/K$ which admits `G` as global genus symbol.
"""
function representative(G::HermGenus)
  if !is_integral(G)
    s = denominator(_scale(G))
    L = representative(rescale(G, s))
    L = rescale(L, 1//s)
    return L
  end
  P = _non_norm_primes(G.LGS)
  E = base_field(G)
  V = hermitian_space(E, _hermitian_form_with_invariants(base_field(G), rank(G), P, G.signatures))
  @vprintln :Lattice 1 "Finding maximal integral lattice"
  M = maximal_integral_lattice(V)
  lp = primes(G)
  bd = union!(support(2*fixed_ring(M)), support(discriminant(maximal_order(E))))
  union!(bd, lp)
  for p in bd
    @vprintln :Lattice 1 "Finding representative for $g at $(prime(g))..."
    g = G[p]
    L = representative(g)
    @hassert :Lattice 1 genus(L, p) == g
    @vprintln :Lattice 1 "Finding sublattice"
    M = locally_isometric_sublattice(M, L, p)
  end
  return M
end

################################################################################
#
#  Enumeration of local genera
#
################################################################################

@doc raw"""
    hermitian_local_genera(E::NumField, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, rank::Int,
                           det_val::Int, min_scale::Int, max_scale::Int)
                                                      -> Vector{HermLocalGenus}

Return all local genus symbols for hermitian lattices over the algebra `E`, with base
field $K$, at the prime ideal`p` of $\mathcal O_K$. Each of them has rank equal to
`rank`, scale $\mathfrak P$-valuations bounded between `min_scale` and `max_scale`
and determinant `p`-valuations equal to `det_val`, where $\mathfrak P$ is a prime
ideal of $\mathcal O_E$ lying above `p`.
"""
function hermitian_local_genera(E, p, rank::Int, det_val::Int, min_scale::Int, max_scale::Int)
  is_ramified = Hecke.is_ramified(maximal_order(E), p)
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
  @req base_field(E) == K "Incompatible arguments: p must be a prime ideal in the base field of E"

  scales_rks = Vector{Tuple{Int, Int}}[] # possible scales and ranks

  for rkseq in _integer_lists(rank, min_scale, max_scale)
    d = 0
    pgensymbol = Tuple{Int, Int}[]
    for i in min_scale:max_scale
      d += i * rkseq[i-min_scale + 1]
      if rkseq[i-min_scale + 1] != 0
        push!(pgensymbol, (i, rkseq[i-min_scale + 1]))
      end
    end
    if d == det_val
      push!(scales_rks, pgensymbol)
    end
  end

  if !is_ramified
    # I add the 0 to make the compiler happy
    symbols = Vector{HermLocalGenus{typeof(E), typeof(p)}}(undef, length(scales_rks))
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

  symbols = HermLocalGenus{typeof(E), typeof(p)}[]
  #hyperbolic_det = hilbert_symbol(K(-1), gen(K)^2//4 - 1, p)
  hyperbolic_det = is_local_norm(E, K(-1), p) ? 1 : -1
  if !is_dyadic(p) # non-dyadic
    for g in scales_rks
      n = length(g)
      dets = Vector{Int}[]
      for b in g
        if mod(b[1], 2) == 0
          push!(dets, Int[1, -1])
        end
        if mod(b[1], 2) == 1
          push!(dets, Int[hyperbolic_det^(div(b[2], 2))])
        end
      end

      for d in cartesian_product_iterator(dets)# Iterators.product(dets...)
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
        push!(det_norms, Vector{Int}[Int[1, div(b[1], 2)], Int[-1, div(b[1], 2)]])
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
      end
    end

    for dn in cartesian_product_iterator(det_norms)
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

@doc raw"""
    hermitian_genera(E::NumField, rank::Int,
                                  signatures::Dict{InfPlc, Int},
                                  determinant::Union{Hecke.RelNumFieldOrderIdeal, Hecke.RelNumFieldOrderFractionalIdeal};
                                  min_scale::Union{Hecke.RelNumFieldOrderIdeal, Hecke.RelNumFieldOrderFractionalIdeal} = is_integral(determinant) ? inv(1*order(determinant)) : determinant,
                                  max_scale::Union{Hecke.RelNumFieldOrderIdeal, Hecke.RelNumFieldOrderFractionalIdeal} = is_integral(determinant) ? determinant : inv(1*order(determinant)))
                                                                                                                 -> Vector{HermGenus}

Return all global genus symbols for hermitian lattices over the algebra`E` with rank
`rank`, signatures given by `signatures`, scale bounded by `max_scale` and determinant
class equal to `determinant`.

If `max_scale == nothing`, it is set to be equal to `determinant`.
"""
function hermitian_genera(E::Hecke.RelSimpleNumField, rank::Int, signatures::Dict{<: InfPlc, Int},
                          determinant::Union{Hecke.RelNumFieldOrderIdeal, Hecke.RelNumFieldOrderFractionalIdeal};
                          min_scale::Union{Hecke.RelNumFieldOrderIdeal, Hecke.RelNumFieldOrderFractionalIdeal} = is_integral(determinant) ? 1*order(determinant) : determinant,
                          max_scale::Union{Hecke.RelNumFieldOrderIdeal, Hecke.RelNumFieldOrderFractionalIdeal} = is_integral(determinant) ? determinant : 1*order(determinant))
  @req rank >= 0 "Rank must be a non-negative integer"
  K = base_field(E)
  OE = maximal_order(E)
  bd = union!(support(2*maximal_order(K)), support(discriminant(OE)))
  @req !iszero(max_scale) "max_scale must be a non-zero fractional ideal"
  @req !iszero(min_scale) "min_scale must be a non-zero fractional ideal"
  @req all(v -> 0 <= v <= rank, values(signatures)) "Incompatible signatures and rank"
  union!(bd, support(norm(min_scale)))
  union!(bd, support(norm(max_scale)))
  union!(bd, support(norm(determinant)))
  sort!(bd; by = (x -> minimum(x)))
  local_symbols = Vector{local_genus_herm_type(E)}[]

  mins = norm(min_scale)
  maxs = norm(max_scale)
  ds = norm(determinant)
  for p in bd
    det_val = valuation(ds, p)
    minscale_p = valuation(mins, p)
    maxscale_p = valuation(maxs, p)
    det_val = div(det_val, 2)
    if !is_ramified(OE, p)
      minscale_p = div(minscale_p, 2)
      maxscale_p = div(maxscale_p, 2)
    end
    lgh = hermitian_local_genera(E, p, rank, det_val, minscale_p, maxscale_p)
    !isempty(lgh) && push!(local_symbols, lgh)
  end

  res = genus_herm_type(E)[]
  it = cartesian_product_iterator(local_symbols)
  for gs in it
    c = copy(gs)
    b = _check_global_genus(c, signatures)
    if b
      filter!(g -> (prime(g) in bd) || (scales(g) != Int[0]), c)
      push!(res, HermGenus(E, rank, c, signatures))
    end
  end

  return res
end

###############################################################################
#
#  Rescale
#
###############################################################################

# TODO: this is not efficient, should be done by working with valuations
# directly on the symbols of g
@doc raw"""
    rescale(g::HermLocalGenus, a::Union{FieldElem, RationalUnion})
                                                              -> HermLocalGenus

Given a local genus symbol `G` of hermitian lattices and an element `a` lying
in the base field `E` of `g`, return the local genus symbol at the prime ideal `p`
associated to `g` of any representative of `g` rescaled by `a`.
"""
function rescale(g::HermLocalGenus, a::Union{FieldElem, RationalUnion})
  L = representative(g)
  L = rescale(L, a)
  return genus(L, prime(g))
end

@doc raw"""
    rescale(G::HermGenus, a::Union{FieldElem, RationalUnion}) -> HermGenus

Given a global genus symbol `G` of hermitian lattices and an element `a` lying
in the base field `E` of `G`, return the global genus symbol of any representative
of `G` rescaled by `a`.
"""
function rescale(G::HermGenus, a::Union{FieldElem, RationalUnion})
  @req typeof(a) <: RationalUnion || parent(a) === base_field(base_field(G)) "a must be a fixed element in the base field of G under the associated involution"
  E = base_field(G)
  K = base_field(E)
  I = K(a)*maximal_order(K)
  pd = union!(support(I), primes(G))
  bd = union!(support(2*maximal_order(K)), support(discriminant(maximal_order(E))))
  LGS = local_genus_herm_type(E)[rescale(G[p], a) for p in pd]
  filter!(g -> (prime(g) in bd) || (scales(g) != Int[0]), LGS)
  r = rank(G)
  sig = copy(signatures(G))
  for p in keys(sig)
    if is_positive(K(a), p)
      continue
    end
    sig[p] = r-sig[p]
  end
  return HermGenus(E, r, LGS, sig)
end

