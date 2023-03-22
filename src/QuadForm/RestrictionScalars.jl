export hermitian_structure
export map_of_restriction_of_scalars
export restrict_scalars
export restrict_scalars_with_map
export trace_lattice
export trace_lattice_with_map

###############################################################################
#
#  Maps of restriction of scalars
#
###############################################################################

### Constructors

# TODO: add jldoctest
@doc Markdown.doc"""
    map_of_restriction_of_scalars(K::S, n::Int) where S <: Field
                                                  -> VecSpaceRes{S, elem_type(S)}

Low-level constructor for objects of type `VecSpaceRes`.

Return the map for restricting and extending scalars between the vector space $K^n$
and the vector space $\mathbb{Q}^{n\times m}$ where `m` is the absolute degree of `K`.
`K` here must be a number field and `n` a positive integer.

Note that the domain of the output is defined to be the associated $\mathbb{Q}$-vector
space and $K^n$ is the codomain.
"""
function map_of_restriction_of_scalars(K::S, n::Int) where S
  return VecSpaceRes(K, n)::VecSpaceRes{S, elem_type(K)}
end

# TODO: add jldoctest
@doc Markdown.doc"""
    map_of_restriction_of_scalars(domain::S, codomain::T; domain_basis::MatrixElem = identity_matrix(base_ring(domain), rank(domain)),
                                                          codomain_basis::MatrixElem = identity_matrix(base_ring(codomain), rank(codomain)))
                                                          where {S <: AbstractSpace, T <: AbstractSpace} -> AbstractSpaceRes{S, T}

Low-level constructor for objects of type `AbstractSpaceRes`.

Return the map for restriction and extension of scalars between the abstract hermitian spaces `domain` and `codomain`, with respective base
algebra `E` and `E` and such that `E` is a finite degree extension of `K`.

The optional argument `domain_basis` and `codomain_basis` allow to choose which bases of `domain` and `codomain` respectively one wnats to make
correspond along the associated map of restriction/extension of scalars. By default, the returned map used the standard bases of both spaces.

Note: for now, one can only work with $K = \mathbb{Q}$ and `E` is a number field.
"""
function map_of_restriction_of_scalars(domain::S, codomain::T; domain_basis::MatrixElem = identity_matrix(base_ring(domain), rank(domain)),
                                                   codomain_basis::MatrixElem = identity_matrix(base_ring(codomain), rank(codomain))) where {S, T}
  return AbstractSpaceRes(domain, codomain, domain_basis, codomain_basis)::AbstractSpaceRes{S, T}
end

# TODO: Change VecSpaceRes/AbstractSpaceRes to allow restriction of scalars
# to non rational subfields
# TODO: add jldoctest
@doc Markdown.doc"""
    restrict_scalars(V::AbstractSpace, K::QQField,
                                       alpha::FieldElem = one(base_ring(V)))
                                                          -> QuadSpace, AbstractSpaceRes

Given a space $(V, \Phi)$ and a subfield `K` of the base algebra `E` of `V`, return the
quadratic space `W` obtained by restricting the scalars of $(V, \alpha\Phi)$ to `K`,
together with the map `f` for extending the scalars back.
The form on the restriction is given by ``Tr \circ \Phi`` where ``Tr: E \to K`` is the trace form.
The rescaling factor $\alpha$ is set to 1 by default.

Note that for now one can only restrict scalars to $\mathbb Q$.
"""
function restrict_scalars(V::AbstractSpace, K::QQField,
                                            alpha::FieldElem = one(base_ring(V)))
  E = base_ring(V)
  n = rank(V)
  d = absolute_degree(E)
  B = absolute_basis(E)
  v = elem_type(E)[zero(E) for i in 1:n]
  w = elem_type(E)[zero(E) for i in 1:n]
  G = zero_matrix(FlintQQ, d * n, d * n)
  r = 1
  c = 1
  for i in 1:n
    for bi in 1:length(B)
      v[i] = B[bi]
      c = 1
      for j in 1:n
        for bj in 1:length(B)
          w[j] = B[bj]
          G[r, c] = trace(alpha * inner_product(V, v, w), FlintQQ)
          w[j] = zero(E)
          c = c + 1
        end
      end
      v[i] = zero(E)
      r = r + 1
    end
  end
  Vres = quadratic_space(FlintQQ, G, check = false)
  VrestoV = map_of_restriction_of_scalars(Vres, V)
  return Vres, VrestoV
end

# TODO: add jldoctest
@doc Markdown.doc"""
    restrict_scalars(L::AbstractLat, K::QQField,
                                     alpha::FieldElem = one(base_field(L))) -> ZLat

Given a lattice `L` in a space $(V, \Phi)$, return the $\mathcal O_K$-lattice
obtained by restricting the scalars of $(V, \alpha\Phi)$ to the number field `K`.
The rescaling factor $\alpha$ is set to 1 by default.

Note that for now one can only restrict scalars to $\mathbb Q$.
"""
function restrict_scalars(L::AbstractLat, K::QQField,
                                          alpha::FieldElem = one(base_field(L)))
  V = ambient_space(L)
  Vabs, f = restrict_scalars(V, K, alpha)
  Babs = absolute_basis(L)
  Mabs = zero_matrix(FlintQQ, length(Babs), rank(Vabs))
  for i in 1:length(Babs)
    v = f\(Babs[i])
    for j in 1:length(v)
      Mabs[i, j] = v[j]
    end
  end
  return ZLat(Vabs, Mabs)
end

# TODO: add jldoctest
@doc Markdown.doc"""
    restrict_scalars_with_map(L::AbstractLat, K::QQField,
                                              alpha::FieldElem = one(base_field(L)))
                                                        -> Tuple{ZLat, AbstractSpaceRes}

Given a lattice `L` in a space $(V, \Phi)$, return the $\mathcal O_K$-lattice
obtained by restricting the scalars of $(V, \alpha\Phi)$ to the number field `K`,
together with the map `f` for extending scalars back.
The rescaling factor $\alpha$ is set to 1 by default.

Note that for now one can only restrict scalars to $\mathbb Q$.
"""
function restrict_scalars_with_map(L::AbstractLat, K::QQField,
                                                   alpha::FieldElem = one(base_field(L)))
  V = ambient_space(L)
  Vabs, f = restrict_scalars(V, K, alpha)
  Babs = absolute_basis(L)
  Mabs = zero_matrix(FlintQQ, length(Babs), rank(Vabs))
  for i in 1:length(Babs)
    v = f\(Babs[i])
    for j in 1:length(v)
      Mabs[i, j] = v[j]
    end
  end
  return ZLat(Vabs, Mabs), f
end

# TODO: add jldoctest
@doc Markdown.doc"""
    restrict_scalars(L::AbstractLat, f::SpaceRes) -> ZLat

Given a lattice `L` in a space $(V, \Phi)$ and a map `f` for restricting the
scalars of $(V, \alpha\Phi)$ to a number field `K`, where $\alpha$ is in the
base algebra of `L`, return the associated $\mathcal O_K$-lattice obtained from
`L` with respect to `f`.

Note that for now one can only restrict scalars to $\mathbb Q$.
"""
function restrict_scalars(L::AbstractLat, f::AbstractSpaceRes)
  @req ambient_space(L) === codomain(f) "Incompatible arguments: ambient space of L must be the same as the codomain of f"
  Vabs = domain(f)
  Babs = absolute_basis(L)
  Mabs = zero_matrix(FlintQQ, length(Babs), rank(Vabs))
  for i in 1:length(Babs)
    v = f\(Babs[i])
    for j in 1:length(v)
      Mabs[i, j] = v[j]
    end
  end
  return ZLat(Vabs, Mabs)
end

### Printing methods

function Base.show(io::IO, f::VecSpaceRes)
  n = f.domain_dim
  m = f.codomain_dim
  println(io, "Restriction of scalars QQ^", n , " -> K^", m)
  println(io, "where K is")
  println(io, f.field)
end

function Base.show(io::IO, f::AbstractSpaceRes)
  println(io, "Map of restriction/extension of scalars between abstract hermitian spaces")
  println(io, "Domain:")
  println(io, "=======")
  println(io, domain(f))
  println(io, "Codomain:")
  println(io, "=========")
  println(io, codomain(f))
end

### Image functions

(f::VecSpaceRes)(a) = image(f, a)

(f::AbstractSpaceRes)(a) = image(f, a)

function image(f::VecSpaceRes{S, T}, v::Vector) where {S, T}
  if v isa Vector{QQFieldElem}
    vv = v
  else
    vv = map(QQFieldElem, v)::Vector{QQFieldElem}
  end
  return _image(f, vv)
end

function _image(f::VecSpaceRes{S, T}, v::Vector{QQFieldElem}) where {S, T}
  n = f.codomain_dim
  d = f.absolute_degree
  m = f.domain_dim
  B = f.absolute_basis
  @req length(v) == m "Vector must have length $m ($(length(v)))"
  z = Vector{T}(undef, n)
  l = 1
  for i in 1:n
    z[i] = zero(f.field)
    for k in 1:d
      z[i] = z[i] + v[l] * B[k]
      l = l + 1
    end
  end
  return z
end

function image(f::AbstractSpaceRes{S, T}, v::Vector) where {S, T}
  if v isa Vector{elem_type(base_ring(domain(f)))}
    vv = v
  else
    vv = map(base_ring(domain(f)), v)
  end
  return _image(f, vv)
end

# f makes f.btop correspond with f.bdown. So for a vector v in
# the domain of f, we get its coordinates in the basis f.btop
# using f.ibtop, we do the exntension of scalars. This gives
# the coordinates in the basis f.bdown of the codomain of f
# which we therefore multiply to f.bdown to get coordinates
# in the standard basis
function _image(f::AbstractSpaceRes{S, T}, v::Vector) where {S, T}
  E = base_ring(codomain(f))
  ibtop = f.ibtop
  bdown = f.bdown
  n = rank(codomain(f))
  d = absolute_degree(E)
  m = rank(domain(f))
  B = absolute_basis(E)
  @req length(v) == m "Vector must have length $m ($(length(v)))"
  vl = vec(collect(transpose(matrix(v))*ibtop))
  z = Vector{elem_type(E)}(undef, n)
  l = 1
  for i in 1:n
    z[i] = zero(E)
    for k in 1:d
      z[i] = z[i] + vl[l] * B[k]
      l = l + 1
    end
  end
  return vec(collect(matrix(E, 1, length(z), z)*bdown))
end

### Preimage functions

Base.:(\)(f::VecSpaceRes, a) = preimage(f, a)

Base.:(\)(f::AbstractSpaceRes, a) = preimage(f, a)

function preimage(f::VecSpaceRes{S, T}, v::Vector) where {S, T}
  if v isa Vector{T}
    vv = v
  else
    vv = map(f.field, v)::Vector{T}
  end
  return _preimage(f, vv)
end

function _preimage(f::VecSpaceRes{S, T}, w::Vector{T}) where {S, T}
  n = f.codomain_dim
  d = f.absolute_degree
  @req length(w) == n "Vector must have length $n ($(length(w)))"
  z = Vector{QQFieldElem}(undef, f.domain_dim)
  k = 1
  for i in 1:n
    y = w[i]
    @assert parent(y) === f.field
    co = absolute_coordinates(y)
    for j in 1:d
      z[k] = co[j]
      k = k + 1
    end
  end
  return z
end

function preimage(f::AbstractSpaceRes{S, T}, v::Vector) where {S, T}
  if v isa Vector{elem_type(base_ring(codomain(f)))}
    vv = v
  else
    vv = map(base_ring(codomain(f)), v)
  end
  return _preimage(f, vv)
end

# f makes f.btop correspond with f.bdown. So for a vector v in
# the codomain of f, we get its coordinates in the basis f.bdown
# using f.ibdown, we do the restrictionn of scalars. This gives
# the coordinates in the basis f.btop of the domain of f
# which we therefore multiply to f.btop to get coordinates
# in the standard basis.
function _preimage(f::AbstractSpaceRes{S, T}, w::Vector) where {S, T}
  K = base_ring(domain(f))
  btop = f.btop
  ibdown = f.ibdown
  n = rank(codomain(f))
  d = absolute_degree(base_ring(codomain(f)))
  @req length(w) == n "Vector must have length $n ($(length(w)))"
  wl = vec(collect(transpose(matrix(w))*ibdown))
  z = Vector{elem_type(K)}(undef, rank(domain(f)))
  k = 1
  for i in 1:n
    y = wl[i]
    @assert parent(y) === base_ring(codomain(f))
    co = absolute_coordinates(y)
    for j in 1:d
      z[k] = co[j]
      k = k + 1
    end
  end
  return vec(collect(matrix(QQ, 1, length(z), z)*btop))
end

###############################################################################
#
#  Trace equivalence
#
###############################################################################

# TODO: add jldoctest
@doc Markdown.doc"""
    trace_lattice(L::AbstractLat{T}; alpha::FieldElem = one(base_field(L)),
                                     beta::FieldElem = gen(base_field(L)),
                                     order::Integer = 2) where T -> ZLat, QQMatrix

Given a lattice `H` which is either a $\mathbb Z$-lattice or a hermitian lattice
over the $E/K$ with `E` a cyclotomic field and `K` a maximal real subfield of
`E`, return a pair `(L, f)` consisting on the trace lattice `L` of `H` and an
isometry `f` of `L` which is:
  - the identity if `L` is a `ZLat` and `order == 1`;
  - the opposite of the identity if `L` is a `ZLat` and `order == 2`;
  - given by the multiplication by a $n$-th root of the unity if `L` is a
    `HermLat`, where `n` is the cyclotomic type of `E`.

Note that the optional argument `order` has no effect if `L` is not a
$\mathbb Z$-lattice.

The choice of `alpha` corresponds to the choice of a "twist" for the trace construction
using [`restrict_scalars`](@ref).

The choice of `beta` corresponds to the choice of a primitive root of unity in the
base field of `L`, in the hermitian case, used to construct the isometry `f`.
An error is thrown if `beta` is not a root of unity.

Note that the isometry `f` computed is given by its action on the ambient space of the
trace lattice of `H`.
"""
function trace_lattice(L::AbstractLat{T}; alpha::FieldElem = one(base_field(L)),
                                          beta::FieldElem = gen(base_field(L)),
                                          order::Integer = 2) where T

  return trace_lattice_with_map(L, alpha=alpha, beta=beta, order=order)[1:2]
end

# TODO: add jldoctest
@doc Markdown.doc"""
    trace_lattice_with_map(L::AbstractLat{T}; alpha::FieldElem = one(base_field(L)),
                                              beta::FieldElem = gen(base_field(L)),
                                              order::Integer = 2) where T
                                                            -> ZLat, QQMatrix, AbstractSpaceRes

Return the trace lattice of `H` together with the associated isometry corresponding
to multiplication by `beta` (see [`trace_lattice(::AbstractLat)`](@ref)) and with
the map of restriction/extension of scalars associated to the underlying trace
construction.
"""
function trace_lattice_with_map(L::AbstractLat{T}; alpha::FieldElem = one(base_field(L)),
                                                   beta::FieldElem = gen(base_field(L)),
                                                   order::Integer = 2) where T
  E = base_field(L)
  
  # We only consider full rank lattices for simplicity
  @req degree(L) == rank(L) "Lattice must be of full rank"
  @req parent(beta) === E "beta must be an element of the base algebra of L"
  @req !is_zero(alpha) "alpha must be non zero"

  n = degree(L)

  # will be useful to shorten code of lattices with isometry on Oscar
  if E == QQ
    @req order in [1,2] "For ZLat the order must be 1 or 2"
    V = ambient_space(L)
    if order == 1
      f = identity_matrix(E, n)
    else
      f = -identity_matrix(E, n)
    end
    return L, f, map_of_restriction_of_scalars(V, V)
  end

  # this will be useful for the implementation of the trace construction associated
  # to lattice with isometry of infinite order
  @req maximal_order(E) == equation_order(E) "Equation order and maximal order must coincide"
  
  @req is_cyclotomic_polynomial(absolute_minpoly(beta)) "beta must be a root of unity"

  bool, m = is_cyclotomic_type(E)

  @req bool "L must be defined over a cyclotomic field" 
  @req findfirst(i -> isone(beta^i), 1:m) == m "beta must be a $m-primitive root of 1"

  # This function perform the trace construction on the level of the
  # ambient spaces - we just need to transport the lattice
  Lres, res = restrict_scalars_with_map(L, QQ, alpha)

  # This will correspond to multiplication by beta along the transfer
  iso = zero_matrix(QQ, 0, degree(Lres))

  v = vec(zeros(QQ, 1, degree(Lres)))

  for i in 1:degree(Lres)
    v[i] = one(QQ)
    v2 = res(v)
    v2 = beta.*v2
    v3 = (res\v2)
    iso = vcat(iso, transpose(matrix(v3)))
    v[i] = zero(QQ)
  end

  @assert iso*gram_matrix(ambient_space(Lres))*transpose(iso) == gram_matrix(ambient_space(Lres))

  return Lres, iso, res
end

# TODO: add jldoctest
@doc Markdown.doc"""
    trace_lattice(L::AbstractLat{T}, res::AbstractSpaceRes) where T -> ZLat, QQMatrix, AbstractSpaceRes

Return the trace lattice of `H` together with the associated isometry (see
[`trace_lattice(::AbstractLat)`](@ref)) with respect to the map of restriction of scalars
`res`.
"""
function trace_lattice(L::AbstractLat{T}, res::AbstractSpaceRes; beta::FieldElem = gen(base_field(L))) where T
  @req codomain(res) === ambient_space(L) "f must be a map of restriction of scalars associated to the ambient space of L"
  @req degree(L) == rank(L) "Lattice must be of full rank"
  E = base_field(L)

  @req is_cyclotomic_polynomial(absolute_minpoly(beta)) "beta must be a primitive root of unity"

  bool, m = is_cyclotomic_type(E)

  @req bool "L must be defined over a cyclotomic field"
  @req findfirst(i -> isone(beta^i), 1:m) == m "beta must be a $m-primitive root of unity"

  @req maximal_order(E) == equation_order(E) "Equation order and maximal order must coincide"

  Lres = restrict_scalars(L, res)
  iso = zero_matrix(QQ, 0, degree(Lres))
  v = vec(zeros(QQ, 1, degree(Lres)))

  for i in 1:degree(Lres)
    v[i] = one(QQ)
    v2 = res(v)
    v2 = beta.*v2
    v3 = (res\v2)
    iso = vcat(iso, transpose(matrix(v3)))
    v[i] = zero(QQ)
  end

  @assert iso*gram_matrix(ambient_space(Lres))*transpose(iso) == gram_matrix(ambient_space(Lres))

  return Lres, iso
end

# If the minpoly of f is cyclotomic, return a basis of the QQ-vector space
# on which f acts such that, after extension of scalars to a vector space
# over the parent of b, the associated f-action is given by multiplication
# by b. This function requires f to be invertible, b to be a primitive
# root of unity, and the number of rows of f should be divisible by the
# Euler totient of the order of b
function _admissible_basis(f::QQMatrix, b::NfRelElem; check::Bool = true)
  chi = absolute_minpoly(b)
  n = multiplicative_order(f)

  if check
    @assert is_finite(n)
    @assert is_cyclotomic_polynomial(chi)
    chi_f = minpoly(parent(chi), f)
    @assert chi == chi_f
    @assert divides(ncols(f), euler_phi(n))[1]
  end

  m = divexact(ncols(f), euler_phi(n))
  _mb = absolute_representation_matrix(b)

  # we look we a blockwise basis on which f acts
  # as mutliplication by b along extension of scalars
  mb = block_diagonal_matrix([_mb for i in 1:m])
  bca = Hecke._basis_of_commutator_algebra(f, _mb)
  @assert !is_empty(bca)

  # l will be our new basis, it is made of several blocks,
  # m blocks to be exact.
  l = zero_matrix(QQ, 0, ncols(f))
  while rank(l) != ncols(f)
    _m = popfirst!(bca)
    _l = vcat(l, _m)
    if rank(_l) > rank(l)
      l = _l
    end
  end

  @assert det(l) != 0
  @assert l*f == mb*l
  return l
end

# check whether the induced action of f on the basis l of the QQ-vector space
# on which f acts is given by multiplication by a primitive root of unity in
# E. The minpoly of f must be cyclotomic, of the same type as E (so in
# particular E must be the corresponding cyclotomic field, seen as a cm-extension)
function _is_admissible_basis(l::QQMatrix, f::QQMatrix, E::NfRel)
  ok, n = is_cyclotomic_type(E)

  # if E does not store that it is cyclotomic,
  # we check this by hand somehow, and collect
  # all primitive roots of unity
  if !ok
    n = multiplicative_order(f)
    @assert is_finite(n)
    @assert degree(E) == 2 && absolute_degree(E) == euler_phi(n)
    Et, t = E["t"]
    rt = roots(t^n-1)
    filter!(b -> findfirst(k -> b^k == one(E), 1:n) == n, rt)
    @assert length(rt) == euler_phi(n)
  else
    rt = powers(gen(E), n-1)
    filter!(b -> findfirst(k -> b^k == one(E), 1:n) == n, rt)
    @assert length(rt) == euler_phi(n)
  end

  m = divexact(ncols(f), euler_phi(n))

  # now we check whether there exists a root of unity in E
  # such that the action of f on l is given by mutliplication
  # by this root of unity after extending scalars
  for b in rt
    _mb = absolute_representation_matrix(b)
    mb = block_diagonal_matrix([_mb for i in 1:m])
    if l*f == mb*l
      return true
    end
  end

  return false
end

# TODO: add jldoctest
@doc Markdown.doc"""
    hermitian_structure(L::ZLat, f::QQMatrix; E::NfRel = nothing,
                                              check::Bool = true,
                                              ambient_representation::Bool = true,
                                              res::AbstractSpaceRes = nothing) -> HermLat, AbstractSpaceRes

Given a $\mathbb{Z}$-lattice `L` together with an isometry `f` with cyclotomic minimal polynomial,
return the associated hermitian structure on `(L, f)` together with the map of restriction of scalars.

Note that if `n` is the order of `f`, then `n` must be at least 3 (otherwise there are no hermitian structure) and
the rank of `L` must be divisible by the Euler totient of `n`.

If `L` is not of full rank, then the associated map of restriction of scalars is associated to the rational
span of `L` (see [`rational_span(::ZLat)`](@ref)), since only the action on the rational span of the lattice
matters for the trace equivalence. If `L` is of full rank, we use its ambient space as rational span since both
are isometric (see [`ambient_space(::ZLat)`](@ref))

If `ambient_representation` is set to true, then the isometry `f` is seen as an isometry of the ambient space of `L`.
If `check == true`, then the function checks whether the minimal polynomial of the action of `f` on the rational
span of `L` is cyclotomic.

One can specify the base field `E` for the hermitian structure, for caching reasons. For the sake of consistency
`E` must be, abstractly, the $n$-th cyclotomic field seen as a cm extension and `f` must act as multiplication
by the given generator of `E` (see [`gen(::NfRel)`](@ref)) on a basis of the rational span of `L`.

One can specify a given map of restriction of scalars `res` used for the trace equivalence. For the sake of consistency
the domain of `res` should be the ambient space of `L`, the codomain of `res` must be defined over `E` (if specified) and
the associated action of `f` along `res` must be given as multiplication by a primitive $n$-th root of unity.
"""
function hermitian_structure(_L::ZLat, f::QQMatrix; E = nothing,
                                                    check::Bool = true,
                                                    ambient_representation::Bool = true,
                                                    res = nothing)

  # Since the minimal polynomial of f might not be cyclotomic, but the one
  # of ites restriction to _L is, we are only concerned about _L inside
  # its rational span. So if _L is not of full rank, we consider its
  # "full rank version". Otherwise, we keep it as is and consider f as
  # acting on the ambient space (which is isometric to the rational span of _L)
  if rank(_L) != degree(_L)
    L = Zlattice(gram = gram_matrix(_L))
    if ambient_representation
      ok, f = can_solve_with_solution(basis_matrix(_L), basis_matrix(_L)*f, side=:left)
      @req ok "Isometry does not restrict to L"
    end
  else
    L = _L
    if !ambient_representation
      V = ambient_space(_L)
      B = basis_matrix(_L)
      B2 = orthogonal_complement(V, B)
      C = vcat(B, B2)
      f_ambient = block_diagonal_matrix([f, identity_matrix(QQ, nrows(B2))])
      f = inv(C)*f_ambient*C
    end
  end

  n = multiplicative_order(f)

  @req is_finite(n) && n > 0 "Isometry must be non-trivial and of finite exponent"

  if check
    @req n >= 3 "No hermitian structure for order less than 3"
    G = gram_matrix(ambient_space(L))
    @req is_cyclotomic_polynomial(minpoly(f)) "The minimal polynomial of f must be irreducible and cyclotomic"
    @req f*G*transpose(f) == G "f does not define an isometry of L"
    @req divides(rank(L), euler_phi(n))[1] "The totient of n must divides the rank of L"
  end

  if res !== nothing
    if E !== nothing
      @req base_ring(codomain(res)) === E "If mentioned, the codomain of res should should be defined over E"
    else
      E = base_ring(codomain(res))
      @req domain(res) === ambient_space(L) "The domain of res should be equal to the ambient space of L"
    end
  end

  if E === nothing
    E, b = cyclotomic_field_as_cm_extension(n)
  elseif !is_cyclotomic_type(E)[1]
    @req degree(E) == 2 && absolute_degree(E) == euler_phi(n) "E should be the $n-th cyclotomic field seen as a cm-extension of its real cyclotomic subfield"
    Et, t = E["t"]
    rt = roots(t^n-1)
    filter!(l -> findfirst(i -> isone(l^i), 1:n) == n, rt)
    @req length(rt) == euler_phi(n) "E is not of cyclotomic type"
    b = isone(rt[1]) ? rt[2] : rt[1]
  else
    b = gen(E)
  end

  m = divexact(rank(L), euler_phi(n))

  # here we get an "admissible basis", i.e. a nice basis on which
  # f acts as multiplication by b after extending scalars
  if res === nothing
    l = _admissible_basis(f, b, check=false)
  else
    l = res.btop
    if check
      @assert det(l) != 0
      @assert _is_admissible_basis(l, f, E)
    end
  end

  _mb = absolute_representation_matrix(b)
  mb = block_diagonal_matrix([_mb for j in 1:m])

  # we construct the gram matrix of the hermitian space in which to extend the scalars.
  # For this we change the basis of the ambient space/rational span of L and
  # we use the transfer formula to revert the trace construction (this is
  # where we actually need a basis on which the isometry is given by mutliplication
  # by a root of unity)
  gram = matrix(zeros(E, m, m))
  G = l*gram_matrix(ambient_space(L))*transpose(l)
  v = zero_matrix(QQ, 1, rank(L))

  for i=1:m
    for j=1:m
      vi = deepcopy(v)
      vi[1,1+(i-1)*euler_phi(n)] = one(QQ)
      vj = deepcopy(v)
      vj[1,1+(j-1)*euler_phi(n)] = one(QQ)
      alpha = sum([(vi*G*transpose(vj*mb^k))[1]*b^k for k in 0:n-1])
      gram[i,j] = alpha
    end
  end

  s = involution(E)
  @assert transpose(map_entries(s, gram)) == gram

  W = hermitian_space(E, 1//n*gram)

  # if not specified, we create the map for extending/restricting scalars
  # considering our "nice" basis keeping track of the action of the isometry
  # on the ambient space. This will be needed for the hermitian Miranda-Morrison
  # theory.
  if res === nothing
    res = map_of_restriction_of_scalars(ambient_space(L), W, domain_basis = l)
  end
  
  # once we have the map between the ambient spaces, it just remain to transfer
  # the lattice
  BL = basis_matrix(L)
  gene = Vector{elem_type(E)}[res(vec(collect(BL[i, :]))) for i in 1:degree(L)]

  Lh = lattice(W, gene)
  return Lh, res
end

