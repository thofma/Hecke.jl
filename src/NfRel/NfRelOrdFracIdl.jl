# for pseudo_basis, basis_pmat, etc. see NfRel/NfRelOrdIdl.jl

################################################################################
#
#  Basic field access
#
################################################################################

@doc Markdown.doc"""
***
    order(a::NfRelOrdFracIdl) -> NfRelOrd

> Returns the order of $a$.
"""
order(a::NfRelOrdFracIdl) = a.order

@doc Markdown.doc"""
***
    nf(a::NfRelOrdFracIdl) -> RelativeExtension

> Returns the number field, of which $a$ is an fractional ideal.
"""
nf(a::NfRelOrdFracIdl) = nf(order(a))

################################################################################
#
#  Parent
#
################################################################################

parent(a::NfRelOrdFracIdl) = a.parent

################################################################################
#
#  iszero/isone
#
################################################################################

iszero(a::NfRelOrdFracIdl) = iszero(basis_mat(a, Val{false})[1, 1])

function isone(a::NfRelOrdFracIdl)
  if denominator(a) != 1
    return false
  end
  @assert isone(basis_pmat(a, Val{false}).matrix[1, 1])
  @assert isone(basis_pmat(order(a), Val{false}).matrix[1, 1])

  return isone(basis_pmat(a, Val{false}).coeffs[1])
end

################################################################################
#
#  Numerator and Denominator
#
################################################################################

function assure_has_denominator(a::NfRelOrdFracIdl)
  if isdefined(a, :den)
    return nothing
  end
  if iszero(a)
    a.den = fmpz(1)
    return nothing
  end
  O = order(a)
  n = degree(O)
  PM = basis_pmat(a, Val{false})
  pb = pseudo_basis(O, Val{false})
  inv_coeffs = inv_coeff_ideals(O, Val{false})
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
***
    denominator(a::NfRelOrdFracIdl) -> fmpz

> Returns the smallest positive integer $d$ such that $da$ is contained in
> the order of $a$.
"""
function denominator(a::NfRelOrdFracIdl)
  assure_has_denominator(a)
  return a.den
end

@doc Markdown.doc"""
***
    numerator(a::NfRelOrdFracIdl) -> NfRelOrdIdl

> Returns the ideal $d*a$ where $d$ is the denominator of $a$.
"""
function numerator(a::NfRelOrdFracIdl)
  d = denominator(a)
  PM = basis_pmat(a)
  if isone(d)
    return NfRelOrdIdl{typeof(a).parameters...}(order(a), PM)
  end
  for i = 1:degree(order(a))
    PM.coeffs[i] = PM.coeffs[i]*d
    PM.coeffs[i] = simplify(PM.coeffs[i])
  end
  return NfRelOrdIdl{typeof(a).parameters...}(order(a), PM)
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, s::NfRelOrdFracIdlSet)
  print(io, "Set of fractional ideals of ")
  print(io, s.order)
end

function show(io::IO, a::NfRelOrdFracIdl)
  compact = get(io, :compact, false)
  if compact
    print(io, "Fractional ideal with basis pseudo-matrix\n")
    show(IOContext(io, :compact => true), basis_pmat(a, Val{false}))
  else
    print(io, "Fractional ideal of\n")
    show(IOContext(io, :compact => true), order(a))
    print(io, "\nwith basis pseudo-matrix\n")
    show(IOContext(io, :compact => true), basis_pmat(a, Val{false}))
  end
end

################################################################################
#
#  Construction
#
################################################################################

@doc Markdown.doc"""
***
    frac_ideal(O::NfRelOrd, M::PMat, M_in_hnf::Bool = false) -> NfRelOrdFracIdl

> Creates the fractional ideal of $\mathcal O$ with basis pseudo-matrix $M$. If
> M_in_hnf is set, then it is assumed that $M$ is already in lower left pseudo
> HNF.
"""
function frac_ideal(O::NfRelOrd{T, S}, M::PMat{T, S}, M_in_hnf::Bool = false) where {T, S}
  !M_in_hnf ? M = pseudo_hnf(M, :lowerleft, true) : nothing
  return NfRelOrdFracIdl{T, S}(O, M)
end

@doc Markdown.doc"""
***
    frac_ideal(O::NfRelOrd, M::Generic.Mat) -> NfRelOrdFracIdl

> Creates the fractional ideal of $\mathcal O$ with basis matrix $M$.
"""
function frac_ideal(O::NfRelOrd{T, S}, M::Generic.Mat{T}) where {T, S}
  coeffs = deepcopy(basis_pmat(O, Val{false})).coeffs
  return frac_ideal(O, PseudoMatrix(M, coeffs))
end

function frac_ideal(O::NfRelOrd{T, S}, x::RelativeElement{T}) where {T, S}
  d = degree(O)
  pb = pseudo_basis(O, Val{false})
  M = zero_matrix(base_ring(nf(O)), d, d)
  if iszero(x)
    return NfRelOrdFracIdl{T, S}(O, PseudoMatrix(M, [ deepcopy(pb[i][2]) for i = 1:d ]))
  end
  for i = 1:d
    elem_to_mat_row!(M, i, pb[i][1]*x)
  end
  M = M*basis_mat_inv(O, Val{false})
  PM = PseudoMatrix(M, [ deepcopy(pb[i][2]) for i = 1:d ])
  PM = pseudo_hnf(PM, :lowerleft)
  return NfRelOrdFracIdl{T, S}(O, PM)
end

*(O::NfRelOrd{T, S}, x::RelativeElement{T}) where {T, S} = frac_ideal(O, x)

*(x::RelativeElement{T}, O::NfRelOrd{T, S}) where {T, S} = frac_ideal(O, x)

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::NfRelOrdFracIdl{T, S}, dict::IdDict) where {T, S}
  z = NfRelOrdFracIdl{T, S}(a.order)
  for x in fieldnames(typeof(a))
    if x != :order && x != :parent && isdefined(a, x)
      setfield!(z, x, Base.deepcopy_internal(getfield(a, x), dict))
    end
  end
  z.order = a.order
  z.parent = a.parent
  return z
end

################################################################################
#
#  Equality
#
################################################################################

@doc Markdown.doc"""
***
    ==(a::NfOrdRelFracIdl, b::NfRelOrdFracIdl) -> Bool

> Returns whether $a$ and $b$ are equal.
"""
function ==(a::NfRelOrdFracIdl, b::NfRelOrdFracIdl)
  order(a) != order(b) && return false
  return basis_pmat(a, Val{false}) == basis_pmat(b, Val{false})
end

################################################################################
#
#  Norm
#
################################################################################

# Assumes, that det(basis_mat(a)) == 1
function assure_has_norm(a::NfRelOrdFracIdl)
  if a.has_norm
    return nothing
  end
  if iszero(a)
    O = order(basis_pmat(a, Val{false}).coeffs[1])
    a.norm = nf(O)()*O
    a.has_norm = true
    return nothing
  end
  c = basis_pmat(a, Val{false}).coeffs
  d = inv_coeff_ideals(order(a), Val{false})
  n = c[1]*d[1]
  for i = 2:degree(order(a))
    n *= c[i]*d[i]
  end
  simplify(n)
  a.norm = n
  a.has_norm = true
  return nothing
end

@doc Markdown.doc"""
***
    norm(a::NfRelOrdFracIdl{T, S}) -> S

> Returns the norm of $a$
"""
function norm(a::NfRelOrdFracIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_norm(a)
  if copy == Val{true}
    return deepcopy(a.norm)
  else
    return a.norm
  end
end

################################################################################
#
#  Ideal addition / GCD
#
################################################################################

@doc Markdown.doc"""
***
    +(a::NfRelOrdFracIdl, b::NfRelOrdFracIdl) -> NfRelOrdFracIdl

> Returns $a + b$.
"""
function +(a::NfRelOrdFracIdl{T, S}, b::NfRelOrdFracIdl{T, S}) where {T, S}
  d = degree(order(a))
  H = vcat(basis_pmat(a), basis_pmat(b))
  if T != nf_elem
    H = sub(pseudo_hnf(H, :lowerleft), (d + 1):2*d, 1:d)
    return frac_ideal(order(a), H, true)
  end
  den = lcm(denominator(a), denominator(b))
  for i = 1:d
    # We assume that the basis_pmats are lower triangular
    for j = 1:i
      H.matrix[i, j] *= den
      H.matrix[i + d, j] *= den
    end
  end
  m = simplify(den^d*(norm(a) + norm(b)))
  @assert isone(denominator(m))
  H = sub(pseudo_hnf_full_rank_with_modulus(H, numerator(m), :lowerleft), (d + 1):2*d, 1:d)
  for i = 1:d
    H.coeffs[i].den = H.coeffs[i].den*den
    H.coeffs[i] = simplify(H.coeffs[i])
  end
  return frac_ideal(order(a), H, true)
end

################################################################################
#
#  Ideal multiplication
#
################################################################################

@doc Markdown.doc"""
    *(a::NfRelOrdFracIdl, b::NfRelOrdFracIdl) -> NfRelOrdFracIdl

> Returns $a \cdot b$.
"""
function *(a::NfRelOrdFracIdl{T, S}, b::NfRelOrdFracIdl{T, S}) where {T, S}
  if iszero(a) || iszero(b)
    return nf(order(a))()*order(a)
  end
  pba = pseudo_basis(a, Val{false})
  pbb = pseudo_basis(b, Val{false})
  ma = basis_mat(a, Val{false})
  mb = basis_mat(b, Val{false})
  den = denominator(a)*denominator(b)
  L = nf(order(a))
  K = base_ring(L)
  d = degree(order(a))
  M = zero_matrix(K, d^2, d)
  C = Array{typeof(a).parameters[2], 1}(undef, d^2)
  t = L()
  for i = 1:d
    for j = 1:d
      mul!(t, pba[i][1], pbb[j][1])
      T == nf_elem ? t = t*den : nothing
      elem_to_mat_row!(M, (i - 1)*d + j, t)
      C[(i - 1)*d + j] = pba[i][2]*pbb[j][2]
    end
  end
  if T != nf_elem
    H = sub(pseudo_hnf(PseudoMatrix(M, C), :lowerleft), (d*(d - 1) + 1):d^2, 1:d)
    H.matrix = H.matrix*basis_mat_inv(order(a), Val{false})
    H = pseudo_hnf(H, :lowerleft)
    return frac_ideal(order(a), H, true)
  end
  m = simplify(den^(2*d)*norm(a)*norm(b))
  @assert isone(denominator(m))
  H = sub(pseudo_hnf_full_rank_with_modulus(PseudoMatrix(M, C), numerator(m), :lowerleft), (d*(d - 1) + 1):d^2, 1:d)
  H.matrix = H.matrix*basis_mat_inv(order(a), Val{false})
  H = pseudo_hnf_full_rank_with_modulus(H, numerator(m), :lowerleft)
  for i = 1:d
    H.coeffs[i].den = H.coeffs[i].den*den
    H.coeffs[i] = simplify(H.coeffs[i])
  end
  return frac_ideal(order(a), H, true)
end

Base.:(^)(A::NfRelOrdFracIdl, b::Int) = Base.power_by_squaring(A, p)

################################################################################
#
#  Division
#
################################################################################

@doc Markdown.doc"""
***
      divexact(a::NfRelOrdFracIdl, b::NfRelOrdFracIdl) -> NfRelOrdFracIdl
      divexact(a::NfRelOrdFracIdl, b::NfRelOrdIdl) -> NfRelOrdFracIdl
      divexact(a::NfRelOrdIdl, b::NfRelOrdFracIdl) -> NfRelOrdFracIdl

> Returns $ab^{-1}$.
"""
divexact(a::NfRelOrdFracIdl{T, S}, b::NfRelOrdFracIdl{T, S}) where {T, S} = a*inv(b)

divexact(a::NfRelOrdFracIdl{T, S}, b::NfRelOrdIdl{T, S}) where {T, S} = a*inv(b)

function divexact(a::NfRelOrdIdl{T, S}, b::NfRelOrdFracIdl{T, S}) where {T, S}
  O = order(a)
  return frac_ideal(O, basis_pmat(a, Val{false}), true)*inv(b)
end

//(a::NfRelOrdFracIdl{T, S}, b::NfRelOrdFracIdl{T, S}) where {T, S} = divexact(a, b)

//(a::NfRelOrdFracIdl{T, S}, b::NfRelOrdIdl{T, S}) where {T, S} = divexact(a, b)

//(a::NfRelOrdIdl{T, S}, b::NfRelOrdFracIdl{T, S}) where {T, S} = divexact(a, b)

################################################################################
#
#  Ad hoc multiplication
#
################################################################################

function *(a::NfRelOrdFracIdl{T, S}, b::RelativeElement{T}) where {T, S}
  if iszero(b)
    return b*order(a)
  end
  c = b*order(a)
  return c*a
end

*(b::RelativeElement{T}, a::NfRelOrdFracIdl{T, S}) where {T, S} = a*b

################################################################################
#
#  Integral ideal testing
#
################################################################################

isintegral(a::NfRelOrdFracIdl) = defines_ideal(order(a), basis_pmat(a, Val{false}))

################################################################################
#
#  "Simplification"
#
################################################################################

# The basis_pmat of a NfRelOrdFracIdl should be in pseudo hnf, so it should already
# be "simple". Maybe we could simplify the coefficient ideals?
simplify(a::NfRelOrdFracIdl) = a

################################################################################
#
#  Reduction of element modulo ideal
#
################################################################################

function mod(x::nf_elem, y::NfOrdFracIdl)
  return _mod(x, y)
end

function mod(x::RelativeElement, y::NfRelOrdFracIdl)
  return _mod(x, y)
end

function _mod(x, y::T) where {T}
  K = parent(x)
  O = order(y)
  d = K(lcm(denominator(x, O), denominator(y)))
  dx = d*x
  dy = d*y
  if T == NfOrdFracIdl
    dy = simplify(dy)
    dynum = numerator(dy)
  else
    dynum = NfRelOrdIdl{T.parameters...}(O, basis_pmat(dy, Val{false}))
  end
  dz = mod(O(dx), dynum)
  z = divexact(K(dz), d)
  return z
end

################################################################################
#
#  Inclusion of elements in ideals
#
################################################################################

@doc Markdown.doc"""
***
    in(x::RelativeElement, y::NfRelOrdFracIdl)

> Returns whether $x$ is contained in $y$.
"""
function in(x::RelativeElement, y::NfRelOrdFracIdl)
  parent(x) != nf(order(y)) && error("Number field of element and ideal must be equal")
  O = order(y)
  b_pmat = basis_pmat(y, Val{false})
  t = zero_matrix(base_ring(nf(O)), 1, degree(O))
  elem_to_mat_row!(t, 1, x)
  t = t*basis_mat_inv(O, Val{false})
  t = t*basis_mat_inv(y, Val{false})
  for i = 1:degree(O)
    if !(t[1, i] in b_pmat.coeffs[i])
      return false
    end
  end
  return true
end

################################################################################
#
#  Valuation
#
################################################################################

function valuation(A::NfRelOrdFracIdl, P::NfRelOrdIdl)
  return valuation(numerator(A), P) - valuation(denominator(A), P)
end

function valuation_naive(a::RelativeElement, P::NfRelOrdIdl)
  @assert !iszero(a)
  return valuation(a*order(P), P)
end

valuation(a::RelativeElement, P::NfRelOrdIdl) = valuation_naive(a, P)

################################################################################
#
#  Random elements
#
################################################################################

function rand(a::NfRelOrdFracIdl, B::Int)
  pb = pseudo_basis(a, Val{false})
  z = nf(order(a))()
  for i = 1:degree(order(a))
    t = rand(pb[i][2], B)
    z += t*pb[i][1]
  end
  return z
end
