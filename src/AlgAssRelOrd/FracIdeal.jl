# Many functions are in AlgAssRelOrd/Ideal.jl

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::AlgAssRelOrdFracIdl)
  print(io, "Fractional ideal of ")
  show(IOContext(io, :compact => true), order(a))
  print(io, " with basis pseudo-matrix\n")
  show(IOContext(io, :compact => true), basis_pmatrix(a, copy = false))
end

################################################################################
#
#  Construction
#
################################################################################

@doc Markdown.doc"""
    fractional_ideal(O::AlgAssRelOrd, M::PMat, M_in_hnf::Bool = false)
      -> AlgAssRelOrdFracIdl

> Returns the fractional ideal of $O$ with basis pseudo-matrix $M$.
> If the ideal is known to be a right/left/twosided ideal of $O$, `side` may be
> set to `:right`/`:left`/`:twosided` respectively.
> If `M_in_hnf == true` it is assumed that $M$ is already in lower left pseudo HNF.
"""
function fractional_ideal(O::AlgAssRelOrd{S, T}, M::PMat{S, T}, side::Symbol = :nothing, M_in_hnf::Bool = false) where { S, T }
  !M_in_hnf ? M = pseudo_hnf(M, :lowerleft, true) : nothing
  a = AlgAssRelOrdFracIdl{S, T}(O, M)
  _set_sidedness(a, side)
  return a
end

function _zero_fractional_ideal(O::AlgAssRelOrd{S, T}) where { S, T }
  a = AlgAssRelOrdFracIdl{S, T}(O)
  a.iszero = 1
  return a
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::AlgAssRelOrdFracIdl{S, T}, dict::IdDict) where {S, T}
  b = AlgAssRelOrdFracIdl{S, T}(algebra(a))
  for x in fieldnames(typeof(a))
    if x != :order && x != :right_order && x != :left_order && isdefined(a, x)
      setfield!(b, x, Base.deepcopy_internal(getfield(a, x), dict))
    end
  end
  b.algebra = a.order
  if isdefined(a, :right_order)
    b.right_order = right_order(a)
  end
  if isdefined(a, :left_order)
    b.left_order = left_order(a)
  end
  return b
end

################################################################################
#
#  Arithmetic
#
################################################################################

@doc Markdown.doc"""
    +(a::AlgAssRelOrdFracIdl, b::AlgAssRelOrdFracIdl) -> AlgAssRelOrdFracIdl
    +(a::AlgAssRelOrdIdl, b::AlgAssRelOrdFracIdl) -> AlgAssRelOrdFracIdl
    +(a::AlgAssRelOrdFracIdl, b::AlgAssRelOrdIdl) -> AlgAssRelOrdFracIdl

> Returns $a + b$, requires `order(a) === order(b)`.
"""
function +(a::AlgAssRelOrdFracIdl{S, T}, b::Union{ AlgAssRelOrdIdl{S, T}, AlgAssRelOrdFracIdl{S, T} }) where {S, T}
  @assert order(a) === order(b)
  if iszero(a)
    if typeof(b) <: AlgAssRelOrdIdl
      return fractional_ideal(order(b), basis_pmatrix(b), true)
    end
    return deepcopy(b)
  elseif iszero(b)
    return deepcopy(a)
  end

  d = dim(order(a))
  M = vcat(basis_pmatrix(a), basis_pmatrix(b))
  M = sub(pseudo_hnf(M, :lowerleft), (d + 1):2*d, 1:d)
  return fractional_ideal(order(a), M, :nothing, true)
end

# Luckily, this is commutative
+(a::AlgAssRelOrdIdl{S, T}, b::AlgAssRelOrdFracIdl{S, T}) where {S, T} = b + a

@doc Markdown.doc"""
    *(a::AlgAssRelOrdIdl, b::AlgAssRelOrdFracIdl) -> AlgAssRelOrdFracIdl
    *(a::AlgAssRelOrdFracIdl, b::AlgAssRelOrdIdl) -> AlgAssRelOrdFracIdl
    *(a::AlgAssRelOrdFracIdl, b::AlgAssRelOrdFracIdl) -> AlgAssRelOrdFracIdl

> Returns $c := a \cdot b$.
> If `order(a) == order(b)`, then $c$ is a fractional ideal of `order(c)`.
> Otherwise it is assumed that both $a$ and $b$ are full lattices in the algebra.
> In this case $c$ is returned as a fractional ideal of `left_order(a)`.
"""
*(a::AlgAssRelOrdFracIdl{S, T}, b::AlgAssRelOrdFracIdl{S, T}) where {S, T} = _mul_frac(a, b)
*(a::AlgAssRelOrdIdl{S, T}, b::AlgAssRelOrdFracIdl{S, T}) where {S, T} = _mul_frac(a, b)
*(a::AlgAssRelOrdFracIdl{S, T}, b::AlgAssRelOrdIdl{S, T}) where {S, T} = _mul_frac(a, b)

# I don't want to convert the integral ideal into a fractional one,
# but I can't define *(Union{ ..OrdIdl, ..FracIdl }, Union{ ..OrdIdl, ..FracIdl })
# since *(..OrdIdl, ..OrdIdl} already exists.
function _mul_frac(a::Union{ AlgAssRelOrdIdl{S, T}, AlgAssRelOrdFracIdl{S, T} }, b::Union{ AlgAssRelOrdIdl{S, T}, AlgAssRelOrdFracIdl{S, T} }) where { S, T }
  if order(a) === order(b)
    return _mul_same_order_frac(a, b)
  else
    @assert isfull_lattice(a) && isfull_lattice(b)
    return _mul_full_lattice_frac(a, b)
  end
end

# The "usual" multiplication of fractional ideals of the same order.
function _mul_same_order_frac(a::Union{ AlgAssRelOrdIdl{S, T}, AlgAssRelOrdFracIdl{S, T} }, b::Union{ AlgAssRelOrdIdl{S, T}, AlgAssRelOrdFracIdl{S, T} }) where { S, T }
  if iszero(a)
    return deepcopy(a)
  elseif iszero(b)
    return deepcopy(b)
  end

  A = algebra(order(a))
  PM = __mul_pseudo_bases(A, pseudo_basis(a, copy = false), pseudo_basis(b, copy = false))

  PM.matrix = PM.matrix*basis_mat_inv(order(a), copy = false)
  H = sub(pseudo_hnf(PM, :lowerleft), (nrows(PM) - dim(A) + 1):nrows(PM), 1:dim(A))
  return fractional_ideal(order(a), H, :nothing, true)
end

# The multiplication of fractional ideals as full lattices.
# The result is a fractional ideal of left_order(a).
function _mul_full_lattice_frac(a::Union{ AlgAssRelOrdIdl{S, T}, AlgAssRelOrdFracIdl{S, T} }, b::Union{ AlgAssRelOrdIdl{S, T}, AlgAssRelOrdFracIdl{S, T} }) where { S, T }
  A = algebra(order(a))
  PM = __mul_pseudo_bases(A, pseudo_basis(a, copy = false), pseudo_basis(b, copy = false))
  O = left_order(a)
  PM.matrix = PM.matrix*basis_mat_inv(O, copy = false)
  H = sub(pseudo_hnf(PM, :lowerleft), (nrows(PM) - dim(A) + 1):nrows(PM), 1:dim(A))

  c = fractional_ideal(O, H, :left, true)
  c.left_order = O
  if isdefined(b, :right_order)
    c.right_order = right_order(b)
  end
  return c
end

@doc Markdown.doc"""
    ^(a::AlgAssRelOrdFracIdl, e::Int) -> AlgAssRelOrdFracIdl
    ^(a::AlgAssRelOrdFracIdl, e::fmpz) -> AlgAssRelOrdFracIdl

> Returns $a^e$.
"""
^(a::AlgAssRelOrdFracIdl, e::Int) = Base.power_by_squaring(a, e)
^(a::AlgAssRelOrdFracIdl, e::fmpz) = Base.power_by_squaring(a, BigInt(e))

################################################################################
#
#  Ad hoc multiplication
#
################################################################################

@doc Markdown.doc"""
    *(a::AlgAssRelOrdFracIdl{S, T}, x::S) where { S, T } -> AlgAssRelOrdFracIdl
    *(x::S, a::AlgAssRelOrdFracIdl{S, T}) where { S, T } -> AlgAssRelOrdFracIdl
    *(a::AlgAssRelOrdFracIdl, x::Int) -> AlgAssRelOrdFracIdl
    *(x::Int, a::AlgAssRelOrdFracIdl) -> AlgAssRelOrdFracIdl
    *(a::AlgAssRelOrdFracIdl, x::fmpz) -> AlgAssRelOrdFracIdl
    *(x::fmpz, a::AlgAssRelOrdFracIdl) -> AlgAssRelOrdFracIdl
    *(a::AlgAssRelOrdFracIdl, x::AbsAlgAssElem) -> AlgAssRelOrdFracIdl
    *(x::AbsAlgAssElem, a::AlgAssRelOrdFracIdl) -> AlgAssRelOrdFracIdl

> Returns the fractional ideal $a*x$ respectively $x*a$.
"""
function *(a::AlgAssRelOrdFracIdl{S, T}, x::S) where { S, T }
  if iszero(x)
    return _zero_fractional_ideal(order(a))
  end
  return fractional_ideal(order(a), x*basis_pmatrix(a, copy = false), :nothing, true)
end

*(x::S, a::AlgAssRelOrdFracIdl{S, T}) where { S, T } = a*x

function *(a::AlgAssRelOrdFracIdl, x::Union{ Int, fmpz })
  if iszero(x)
    return _zero_fractional_ideal(order(a))
  end
  b = fractional_ideal(order(a), x*basis_pmatrix(a, copy = false), :nothing, true)
  b.isleft = a.isleft
  b.isright = a.isright
  return b
end

*(x::Union{ Int, fmpz }, a::AlgAssRelOrdFracIdl) = a*x

function *(a::Union{ AlgAssRelOrdIdl, AlgAssRelOrdFracIdl }, x::AbsAlgAssElem)
  if iszero(x)
    return _zero_fractional_ideal(order(a))
  end
  A = algebra(order(a))
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  for i = 1:dim(A)
    t = pseudo_basis(a, copy = false)[i][1]*x
    elem_to_mat_row!(M, i, t)
  end
  PM = PseudoMatrix(M, [ deepcopy(pseudo_basis(a, copy = false)[i][2]) for i = 1:dim(A) ])
  PM.matrix = PM.matrix*basis_mat_inv(order(a), copy = false)
  return fractional_ideal(order(a), PM)
end

function *(x::AbsAlgAssElem, a::Union{ AlgAssRelOrdIdl, AlgAssRelOrdFracIdl })
  if iszero(x)
    return _zero_fractional_ideal(order(a))
  end
  A = algebra(order(a))
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  for i = 1:dim(A)
    t = x*pseudo_basis(a, copy = false)[i][1]
    elem_to_mat_row!(M, i, t)
  end
  PM = PseudoMatrix(M, [ deepcopy(pseudo_basis(a, copy = false)[i][2]) for i = 1:dim(A) ])
  PM.matrix = PM.matrix*basis_mat_inv(order(a), copy = false)
  return fractional_ideal(order(a), PM)
end

################################################################################
#
#  Norm
#
################################################################################

# Assumes, that det(basis_matrix(a)) == 1
function assure_has_norm(a::AlgAssRelOrdFracIdl)
  if isdefined(a, :norm)
    return nothing
  end

  if iszero(a)
    O = base_ring(order(a))
    a.norm = fractional_ideal(O, O()*O, fmpz(1))
    return nothing
  end
  c = basis_pmatrix(a, copy = false).coeffs
  d = inv_coeff_ideals(order(a), copy = false)
  n = c[1]*d[1]
  for i = 2:degree(order(a))
    n *= c[i]*d[i]
  end
  simplify(n)
  a.norm = n
  return nothing
end

@doc Markdown.doc"""
    norm(a::AlgAssRelOrdFracIdl; copy::Bool = true)

> Returns the norm of $a$ as a fractional ideal of `base_ring(order(a))`.
"""
function norm(a::AlgAssRelOrdFracIdl; copy::Bool = true)
  assure_has_norm(a)
  if copy
    return deepcopy(a.norm)
  else
    return a.norm
  end
end

function assure_has_normred(a::AlgAssRelOrdFracIdl)
  if isdefined(a, :normred)
    return nothing
  end

  A = algebra(a)
  m = isqrt(dim(A))
  @assert m^2 == dim(A)
  N = norm(a, copy = false)
  b, I = ispower(N, m)
  @assert b "Cannot compute reduced norm. Maybe the algebra is not simple and central?"
  a.normred = I
  return nothing
end

@doc Markdown.doc"""
    normred(a::AlgAssRelOrdFracIdl; copy::Bool = true)

> Returns the reduced norm of $a$ as a fractional ideal of `base_ring(order(a))`.
> It is assumed that the algebra containing $a$ is simple and central.
"""
function normred(a::AlgAssRelOrdFracIdl; copy::Bool = true)
  @assert issimple(algebra(order(a))) && iscentral(algebra(order(a))) "Only implemented for simple and central algebras"
  assure_has_normred(a)
  if copy
    return deepcopy(a.normred)
  else
    return a.normred
  end
end

################################################################################
#
#  Inverses
#
################################################################################

@doc Markdown.doc"""
    inv(a::AlgAssRelOrdIdl) -> AlgAssRelOrdFracIdl
    inv(a::AlgAssRelOrdFracIdl) -> AlgAssRelOrdFracIdl

> Returns a fractional ideal $b$ of `order(a)` such that `a*b == left_order(a)`
> and `b*a == right_order(b)`.
"""
function inv(a::Union{ AlgAssRelOrdIdl, AlgAssRelOrdFracIdl })
  if isdefined(a, :right_order)
    O = right_order(a)
    PM = _colon_raw(O(1)*O, a, :right)
  else
    O = left_order(a)
    PM = _colon_raw(O(1)*O, a, :left)
  end
  PM.matrix = PM.matrix*basis_mat_inv(order(a), copy = false)
  b = fractional_ideal(order(a), PM)
  if isdefined(a, :left_order)
    b.right_order = left_order(a)
  end
  if isdefined(a, :right_order)
    b.left_order = right_order(a)
  end
  return b
end

################################################################################
#
#  Divexact
#
################################################################################

@doc Markdown.doc"""
    divexact_left(a::AlgAssRelOrdIdl, b::AlgAssRelOrdIdl) -> AlgAssRelOrdFracIdl
    divexact_left(a::AlgAssRelOrdFracIdl, b::AlgAssRelOrdIdl)
      -> AlgAssRelOrdFracIdl
    divexact_left(a::AlgAssRelOrdIdl, b::AlgAssRelOrdFracIdl)
      -> AlgAssRelOrdFracIdl
    divexact_left(a::AlgAssRelOrdFracIdl, b::AlgAssRelOrdFracIdl)
      -> AlgAssRelOrdFracIdl

> Returns a fractional ideal $c$ such that $a = b \cdot c$.
> The order of $c$ is chosen in the following way:
> If $a$ is a right ideal of `order(a)`, then `order(c) = order(a)`.
> If otherwise $b$ is a right ideal of `order(b)`, then `order(c) = order(b)`.
> If both is not the case, then `order(c) = right_order(a)`.
"""
function divexact_left(a::Union{ AlgAssRelOrdIdl{S, T}, AlgAssRelOrdFracIdl{S, T} }, b::Union{ AlgAssRelOrdIdl{S, T}, AlgAssRelOrdFracIdl{S, T} }; set_order::Symbol = :nothing) where { S, T }
  PM = _colon_raw(a, b, :left)

  # Find a order for the quotient. The user can "choose" the order via the
  # variable set_order. See the (hopefully self-explaining) if-cases below.
  O = order(a)
  side = :left
  if set_order == :nothing
    if isright_ideal(a)
      O = order(a)
      side = :right
    elseif isright_ideal(b)
      O = order(b)
    else
      O = right_order(a)
      side = :right
    end
  elseif set_order == :basis_a
    O = order(a)
    side = :right
  elseif set_order == :basis_b
    O = order(b)
  elseif set_order == :right_a
    O = right_order(a)
    side = :right
  elseif set_order == :right_b
    O = right_order(b)
  else
    error("Option :$(set_order) for set_order not implemented")
  end

  PM.matrix = PM.matrix*basis_mat_inv(O, copy = false)
  c = fractional_ideal(O, PM, side)

  if isdefined(a, :right_order)
    c.right_order = right_order(a)
  end
  if isdefined(b, :right_order)
    c.left_order = right_order(b)
  end

  return c
end

@doc Markdown.doc"""
    divexact_right(a::AlgAssRelOrdIdl, b::AlgAssRelOrdIdl) -> AlgAssRelOrdFracIdl
    divexact_right(a::AlgAssRelOrdFracIdl, b::AlgAssRelOrdIdl)
      -> AlgAssRelOrdFracIdl
    divexact_right(a::AlgAssRelOrdIdl, b::AlgAssRelOrdFracIdl)
      -> AlgAssRelOrdFracIdl
    divexact_right(a::AlgAssRelOrdFracIdl, b::AlgAssRelOrdFracIdl)
      -> AlgAssRelOrdFracIdl

> Returns a fractional ideal $c$ such that $a = c \cdot b$.
> The order of $c$ is chosen in the following way:
> If $a$ is a left ideal of `order(a)`, then `order(c) = order(a)`.
> If otherwise $b$ is a left ideal of `order(b)`, then `order(c) = order(b)`.
> If both is not the case, then `order(c) = left_order(a)`.
"""
function divexact_right(a::Union{ AlgAssRelOrdIdl{S, T}, AlgAssRelOrdFracIdl{S, T} }, b::Union{ AlgAssRelOrdIdl{S, T}, AlgAssRelOrdFracIdl{S, T} }; set_order::Symbol = :nothing) where { S, T }
  PM = _colon_raw(a, b, :right)

  # Find a order for the quotient. The user can "choose" the order via the
  # variable set_order. See the (hopefully self-explaining) if-cases below.
  O = order(a)
  side = :left
  if set_order == :nothing
    if isleft_ideal(a)
      O = order(a)
    elseif isleft_ideal(b)
      O = order(b)
      side = :right
    else
      O = left_order(a)
    end
  elseif set_order == :basis_a
    O = order(a)
  elseif set_order == :basis_b
    O = order(b)
    side = :right
  elseif set_order == :left_a
    O = left_order(a)
  elseif set_order == :left_b
    O = left_order(b)
    side = :right
  else
    error("Option :$(set_order) for set_order not implemented")
  end

  PM.matrix = PM.matrix*basis_mat_inv(O, copy = false)
  c = fractional_ideal(O, PM, side)

  if isdefined(a, :left_order)
    c.left_order = left_order(a)
  end
  if isdefined(b, :left_order)
    c.right_order = left_order(b)
  end

  return c
end

################################################################################
#
#  Inclusion of elements
#
################################################################################

@doc Markdown.doc"""
    in(x::AbsAlgAssElem, a::AlgAssRelOrdFracIdl) -> Bool

> Returns `true` if the element $x$ is in $a$ and `false` otherwise.
"""
function in(x::AbsAlgAssElem, a::AlgAssRelOrdFracIdl)
  parent(x) !== algebra(a) && error("Algebra of element and full lattice must be equal")
  A = algebra(order(a))
  b_pmat = basis_pmatrix(a, copy = false)
  t = matrix(base_ring(A), 1, dim(A), coeffs(x, copy = false))
  t = t*basis_mat_inv(O, copy = false)*basis_mat_inv(a, copy = false)
  for i = 1:dim(A)
    if !(t[1, i] in b_pmat.coeffs[i])
      return false
    end
  end
  return true
end

################################################################################
#
#  Numerator and Denominator
#
################################################################################

function assure_has_denominator(a::AlgAssRelOrdFracIdl)
  if isdefined(a, :den)
    return nothing
  end
  if iszero(a)
    a.den = fmpz(1)
    return nothing
  end
  O = order(a)
  n = degree(O)
  PM = basis_pmatrix(a, copy = false)
  pb = pseudo_basis(O, copy = false)
  inv_coeffs = inv_coeff_ideals(O, copy = false)
  d = fmpz(1)
  for i = 1:n
    for j = 1:i
      d = lcm(d, denominator(simplify(PM.matrix[i, j]*PM.coeffs[i]*inv_coeffs[j])))
    end
  end
  a.den = d
  return nothing
end

@doc Markdown.doc"""
    denominator(a::AlgAssRelOrdFracIdl) -> fmpz

> Returns the smallest positive integer $d$ such that $da$ is contained in
> the order of $a$.
"""
function denominator(a::AlgAssRelOrdFracIdl; copy::Bool = true)
  assure_has_denominator(a)
  if copy
    return deepcopy(a.den)
  else
    return a.den
  end
end

@doc Markdown.doc"""
    numerator(a::AlgAssRelOrdFracIdl) -> AlgAssRelOrdIdl

> Returns the ideal $d*a$ where $d$ is the denominator of $a$.
"""
function numerator(a::AlgAssRelOrdFracIdl)
  d = denominator(a, copy = false)
  if isone(d)
    return ideal_type(order(a))(order(a), basis_pmatrix(a))
  end

  PM = d*basis_pmatrix(a, copy = false)
  b = ideal_type(order(a))(order(a), PM)
  b.isleft = a.isleft
  b.isright = a.isright
  return b
end

# Assumes that I is "locally integral at p", i. e. I_p \subseteq O_p with
# O = order(I).
# Returns x in R\setminus p such that Ix \subseteq O, where R = order(p)
function coprime_denominator(I::AlgAssRelOrdFracIdl, p::Union{ NfAbsOrdIdl, NfRelOrdIdl })
  O = order(I)
  basis_O, basis_I, MO, MI = coprime_bases(O, I, p)
  OK = order(p)
  S = Dict{ideal_type(OK), Int}()
  for i = 1:degree(O)
    ai = inv(basis_O[i][2])
    for j = 1:degree(O)
      c = basis_I[j][2]*ai*MI[i, j]
      if iszero(norm(c))
        continue
      end
      d = denominator(c)
      facD = factor(d)
      for (q, e) in facD
        qdec = prime_decomposition(OK, q)
        for (Q, _) in qdec
          v = valuation(c, Q)
          if v >= 0
            continue
          end
          if haskey(S, Q)
            f = S[Q]
            S[Q] = max(f, -v)
          else
            S[Q] = -v
          end
        end
      end
    end
  end
  if haskey(S, p)
    error("The ideal is not locally integral at p")
  end
  primes = Vector{ideal_type(OK)}()
  vals = Vector{Int}()
  for (q, e) in S
    push!(primes, q)
    push!(vals, e)
  end
  push!(primes, p)
  push!(vals, 0)
  return approximate_nonnegative(vals, primes)
end

# Returns pseudo bases (a_i, alpha_i)_i of O and (b_i, beta_i)_i of I, a basis
# matrix of O_p and a basis matrix (b_{ij})_{i,j} of I_p in the basis of O_p,
# such that O_p = \bigoplus_i R_p alpha_i and I_p = \bigoplus_i R_p beta_i,
# where R = order(p) and O = \bigoplus a_i alpha_i and I = \bigoplus b_i beta_i,
# beta_i = sum_j b_{ij} alpha_j.
function coprime_bases(O::AlgAssRelOrd, I::Union{ AlgAssRelOrdIdl, AlgAssRelOrdFracIdl }, p::Union{ NfAbsOrdIdl, NfRelOrdIdl })
  A = algebra(O)
  OK = base_ring(O)
  u = uniformizer(p)
  iu = inv(elem_in_nf(u))
  basis_O = Vector{Tuple{elem_type(A), fractional_ideal_type(OK)}}()
  for (b, c) in pseudo_basis(O, copy = false)
    v = valuation(c, p)
    if v == 0
      push!(basis_O, (deepcopy(b), deepcopy(c)))
    elseif v < 0
      v = -v
      b = b*iu^v
      c = c*u^v
      push!(basis_O, (b, c))
    else
      b = b*u^v
      c = c*iu^v
      push!(basis_O, (b, c))
    end
  end

  basis_I = Vector{Tuple{elem_type(A), fractional_ideal_type(OK)}}()
  for (b, c) in pseudo_basis(I, copy = false)
    v = valuation(c, p)
    if v == 0
      push!(basis_I, (deepcopy(b), deepcopy(c)))
    elseif v < 0
      v = -v
      b = b*iu^v
      c = c*u^v
      push!(basis_I, (b, c))
    else
      b = b*u^v
      c = c*iu^v
      push!(basis_I, (b, c))
    end
  end

  MO = zero_matrix(base_ring(A), dim(A), dim(A))
  for i = 1:dim(A)
    elem_to_mat_row!(MO, i, basis_O[i][1])
  end

  MI = zero_matrix(base_ring(A), dim(A), dim(A))
  for i = 1:dim(A)
    elem_to_mat_row!(MI, i, basis_I[i][1])
  end
  MI = MI*inv(MO)

  return basis_O, basis_I, MO, MI
end
