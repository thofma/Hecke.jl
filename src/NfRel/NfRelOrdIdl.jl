################################################################################
#
#  Basic field access
#
################################################################################

@doc Markdown.doc"""
***
    order(a::NfRelOrdIdl) -> NfRelOrd

> Returns the order of $a$.
"""
order(a::NfRelOrdIdl) = a.order

@doc Markdown.doc"""
***
    nf(a::NfRelOrdIdl) -> RelativeExtension

> Returns the number field, of which $a$ is an integral ideal.
"""
nf(a::NfRelOrdIdl) = nf(order(a))

################################################################################
#
#  Parent
#
################################################################################

parent(a::NfRelOrdIdl) = a.parent

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_basis_pmat(a::Union{NfRelOrdIdl, NfRelOrdFracIdl})
  if isdefined(a, :basis_pmat)
    return nothing
  end
  if !isdefined(a, :pseudo_basis)
    error("No pseudo_basis and no basis_pmat defined.")
  end
  pb = pseudo_basis(a, Val{false})
  L = nf(order(a))
  M = zero_matrix(base_ring(L), degree(L), degree(L))
  C = Vector{S}()
  for i = 1:degree(L)
    elem_to_mat_row!(M, i, pb[i][1])
    push!(C, deepcopy(pb[i][2]))
  end
  M = M*basis_mat_inv(order(a), Val{false})
  a.basis_pmat = pseudo_hnf(PseudoMatrix(M, C), :lowerleft, true)
  return nothing
end

function assure_has_pseudo_basis(a::Union{NfRelOrdIdl, NfRelOrdFracIdl})
  if isdefined(a, :pseudo_basis)
    return nothing
  end
  if !isdefined(a, :basis_pmat)
    error("No pseudo_basis and no basis_pmat defined.")
  end
  P = basis_pmat(a, Val{false})
  B = basis_nf(order(a), Val{false})
  L = nf(order(a))
  K = base_ring(L)
  pseudo_basis = Vector{Tuple{elem_type(L), typeof(a).parameters[2]}}()
  for i = 1:degree(L)
    t = L()
    for j = 1:degree(L)
      t += P.matrix[i, j]*B[j]
    end
    push!(pseudo_basis, (t, deepcopy(P.coeffs[i])))
  end
  a.pseudo_basis = pseudo_basis
  return nothing
end

function assure_has_basis_mat(a::Union{NfRelOrdIdl, NfRelOrdFracIdl})
  if isdefined(a, :basis_mat)
    return nothing
  end
  a.basis_mat = basis_pmat(a).matrix
  return nothing
end

function assure_has_basis_mat_inv(a::Union{NfRelOrdIdl, NfRelOrdFracIdl})
  if isdefined(a, :basis_mat_inv)
    return nothing
  end
  a.basis_mat_inv = inv(basis_mat(a, Val{false}))
  return nothing
end

################################################################################
#
#  Pseudo basis / basis pseudo-matrix
#
################################################################################

@doc Markdown.doc"""
***
      pseudo_basis(a::NfRelOrdIdl{T, S}) -> Vector{Tuple{RelativeElement{T}, S}}
      pseudo_basis(a::NfRelOrdFracIdl{T, S}) -> Vector{Tuple{RelativeElement{T}, S}}

> Returns the pseudo-basis of $a$.
"""
function pseudo_basis(a::Union{NfRelOrdIdl, NfRelOrdFracIdl}, copy::Type{Val{T}} = Val{true}) where T
  assure_has_pseudo_basis(a)
  if copy == Val{true}
    return deepcopy(a.pseudo_basis)
  else
    return a.pseudo_basis
  end
end

@doc Markdown.doc"""
***
      basis_pmat(a::NfRelOrdIdl) -> PMat
      basis_pmat(a::NfRelOrdFracIdl) -> PMat

> Returns the basis pseudo-matrix of $a$.
"""
function basis_pmat(a::Union{NfRelOrdIdl, NfRelOrdFracIdl}, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_pmat(a)
  if copy == Val{true}
    return deepcopy(a.basis_pmat)
  else
    return a.basis_pmat
  end
end

################################################################################
#
#  Basis / (inverse) basis matrix
#
################################################################################

@doc Markdown.doc"""
***
      basis_mat(a::NfRelOrdIdl{T, S}) -> Generic.Mat{T}
      basis_mat(a::NfRelOrdFracIdl{T, S}) -> Generic.Mat{T}

> Returns the basis matrix of $a$.
"""
function basis_mat(a::Union{NfRelOrdIdl, NfRelOrdFracIdl}, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat(a)
  if copy == Val{true}
    return deepcopy(a.basis_mat)
  else
    return a.basis_mat
  end
end

@doc Markdown.doc"""
***
      basis_mat_inv(a::NfRelOrdIdl{T, S}) -> Generic.Mat{T}
      basis_mat_inv(a::NfRelOrdFracIdl{T, S}) -> Generic.Mat{T}

> Returns the inverse of the basis matrix of $a$.
"""
function basis_mat_inv(a::Union{NfRelOrdIdl, NfRelOrdFracIdl}, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat_inv(a)
  if copy == Val{true}
    return deepcopy(a.basis_mat_inv)
  else
    return a.basis_mat_inv
  end
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, s::NfRelOrdIdlSet)
  print(io, "Set of ideals of ")
  print(io, s.order)
end

function show(io::IO, a::NfRelOrdIdl)
  compact = get(io, :compact, false)
  if compact
    print(io, "Ideal with basis pseudo-matrix\n")
    show(IOContext(io, :compact => true), basis_pmat(a, Val{false}))
  else
    print(io, "Ideal of\n")
    show(IOContext(io, :compact => true), order(a))
    print(io, "\nwith basis pseudo-matrix\n")
    show(IOContext(io, :compact => true), basis_pmat(a, Val{false}))
  end
end

################################################################################
#
#  Parent object overloading and user friendly constructors
#
################################################################################

function defines_ideal(O::NfRelOrd{T, S}, M::PMat{T, S}) where {T, S}
  K = base_ring(nf(O))
  coeffs = basis_pmat(O, Val{false}).coeffs
  I = PseudoMatrix(identity_matrix(K, degree(O)), deepcopy(coeffs))
  return _spans_subset_of_pseudohnf(M, I, :lowerleft)
end

@doc Markdown.doc"""
***
    ideal(O::NfRelOrd, M::PMat, check::Bool = true, M_in_hnf::Bool = false) -> NfRelOrdIdl

> Creates the ideal of $\mathcal O$ with basis pseudo-matrix $M$. If check is set,
> then it is checked whether $M$ defines an ideal. If M_in_hnf is set, then it is
> assumed that $M$ is already in lower left pseudo HNF.
"""
function ideal(O::NfRelOrd{T, S}, M::PMat{T, S}, check::Bool = true, M_in_hnf::Bool = false) where {T, S}
  if check
    !defines_ideal(O, M) && error("The pseudo-matrix does not define an ideal.")
  end
  !M_in_hnf ? M = pseudo_hnf(M, :lowerleft, true) : nothing
  return NfRelOrdIdl{T, S}(O, M)
end

@doc Markdown.doc"""
***
    ideal(O::NfRelOrd, M::Generic.Mat, check::Bool = true) -> NfRelOrdIdl

> Creates the ideal of $\mathcal O$ with basis matrix $M$. If check is set,
> then it is checked whether $M$ defines an ideal.
"""
function ideal(O::NfRelOrd{T, S}, M::Generic.Mat{T}, check::Bool = true) where {T, S}
  coeffs = deepcopy(basis_pmat(O, Val{false})).coeffs
  return ideal(O, PseudoMatrix(M, coeffs), check)
end

@doc Markdown.doc"""
***
    ideal(O::NfRelOrd{T, S}, x::NfRelElem{T}, y::NfRelElem{T}, a::S, b::S, check::Bool = true) -> NfRelOrdIdl{T, S}

> Creates the ideal $x\cdot a + y\cdot b$ of $\mathcal O$. If check is set,
> then it is checked whether these elements define an ideal.
"""
function ideal(O::NfRelOrd{T, S}, x::RelativeElement{T}, y::RelativeElement{T}, a::S, b::S, check::Bool = true) where {T, S}
  d = degree(O)
  pb = pseudo_basis(O, Val{false})
  M = zero_matrix(base_ring(nf(O)), 2*d, d)
  C = Array{S}(undef, 2*d)
  for i = 1:d
    elem_to_mat_row!(M, i, pb[i][1]*x)
    C[i] = pb[i][2]*a
  end
  for i = (d + 1):2*d
    elem_to_mat_row!(M, i, pb[i - d][1]*y)
    C[i] = pb[i - d][2]*b
  end
  M = M*basis_mat_inv(O, Val{false})
  PM = PseudoMatrix(M, C)
  if check
    !defines_ideal(O, PM) && error("The elements do not define an ideal.")
  end
  PM = sub(pseudo_hnf(PM, :lowerleft), (d + 1):2*d, 1:d)
  return NfRelOrdIdl{T, S}(O, PM)
end

function ideal(O::NfRelOrd{T, S}, x::RelativeElement{T}, y::RelativeElement{T}, a::NfOrdIdl, b::NfOrdIdl, check::Bool = true) where {T, S}
  aa = frac_ideal(order(a), a, fmpz(1))
  bb = frac_ideal(order(b), b, fmpz(1))
  return ideal(O, x, y, aa, bb, check)
end

function ideal(O::NfRelOrd{T, S}, x::RelativeElement{T}, y::RelativeElement{T}, a::NfRelOrdIdl, b::NfRelOrdIdl, check::Bool = true) where {T, S}
  aa = frac_ideal(order(a), basis_pmat(a), true)
  bb = frac_ideal(order(b), basis_pmat(b), true)
  return ideal(O, x, y, aa, bb, check)
end

@doc Markdown.doc"""
***
    ideal(O::NfRelOrd{T, S}, x::NfRelOrdElem{T}) -> NfRelOrdIdl{T, S}
    *(O::NfRelOrd{T, S}, x::NfRelOrdElem{T}) -> NfRelOrdIdl{T, S}
    *(x::NfRelOrdElem{T}, O::NfRelOrd{T, S}) -> NfRelOrdIdl{T, S}

> Creates the ideal $x\cdot \mathcal O$ of $\mathcal O$.
"""
function ideal(O::NfRelOrd{T, S}, x::NfRelOrdElem{T}) where {T, S}
  parent(x) != O && error("Order of element does not coincide with order")

  d = degree(O)
  pb = pseudo_basis(O, Val{false})
  M = zero_matrix(base_ring(nf(O)), d, d)
  if iszero(x)
    return NfRelOrdIdl{T, S}(O, PseudoMatrix(M, [ deepcopy(pb[i][2]) for i = 1:d ]))
  end
  for i = 1:d
    elem_to_mat_row!(M, i, pb[i][1]*nf(O)(x))
  end
  M = M*basis_mat_inv(O, Val{false})
  PM = PseudoMatrix(M, [ deepcopy(pb[i][2]) for i = 1:d ])
  PM = pseudo_hnf(PM, :lowerleft)
  return NfRelOrdIdl{T, S}(O, PM)
end

*(O::NfRelOrd, x::NfRelOrdElem) = ideal(O, x)

*(x::NfRelOrdElem, O::NfRelOrd) = ideal(O, x)

@doc Markdown.doc"""
***
    ideal(O::NfRelOrd{T, S}, a::S, check::Bool = true) -> NfRelOrdIdl{T, S}

> Creates the ideal $a \cdot \mathcal O$ of $\mathcal O$. If check is set,
> then it is checked whether $a$ defines an (integral) ideal.
"""
function ideal(O::NfRelOrd{T, S}, a::S, check::Bool = true) where {T, S}
  d = degree(O)
  pb = pseudo_basis(O, Val{false})
  M = identity_matrix(base_ring(nf(O)), d)
  PM = PseudoMatrix(M, [ a*pb[i][2] for i = 1:d ])
  if check
    !defines_ideal(O, PM) && error("The coefficient ideal does not define an ideal.")
  end
  PM = pseudo_hnf(PM, :lowerleft)
  return NfRelOrdIdl{T, S}(O, PM)
end

function ideal(O::NfRelOrd{nf_elem, NfOrdFracIdl}, a::NfOrdIdl, check::Bool = true)
  aa = frac_ideal(order(a), a, fmpz(1))
  return ideal(O, aa, check)
end

function ideal(O::NfRelOrd, a::NfRelOrdIdl, check::Bool = true)
  @assert order(a) == order(pseudo_basis(O, Val{false})[1][2])

  aa = frac_ideal(order(a), basis_pmat(a), true)
  return ideal(O, aa, check)
end

@doc Markdown.doc"""
***
    *(O::NfRelOrd{T, S}, a::S) -> NfRelOrdIdl{T, S}
    *(a::S, O::NfRelOrd{T, S}) -> NfRelOrdIdl{T, S}

> Creates the ideal $a \cdot \mathcal O$ of $\mathcal O$.
"""
*(O::NfRelOrd{T, S}, a::S) where {T, S} = ideal(O, a)

*(a::S, O::NfRelOrd{T, S}) where {T, S} = ideal(O, a)

*(O::NfRelOrd, a::Union{NfOrdIdl, NfRelOrdIdl}) = ideal(O, a)

*(a::Union{NfOrdIdl, NfRelOrdIdl}, O::NfRelOrd) = ideal(O, a)

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::NfRelOrdIdl{T, S}, dict::IdDict) where {T, S}
  z = NfRelOrdIdl{T, S}(a.order)
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
#  Copy
#
################################################################################

function copy(a::NfRelOrdIdl)
  return a
end

################################################################################
#
#  Equality
#
################################################################################

@doc Markdown.doc"""
***
    ==(a::NfRelOrdIdl, b::NfRelOrdIdl) -> Bool

> Returns whether $a$ and $b$ are equal.
"""
function ==(a::NfRelOrdIdl, b::NfRelOrdIdl)
  order(a) != order(b) && return false
  return basis_pmat(a, Val{false}) == basis_pmat(b, Val{false})
end

################################################################################
#
#  iszero/isone
#
################################################################################

iszero(a::NfRelOrdIdl) = iszero(basis_mat(a, Val{false})[1, 1])

isone(a::NfRelOrdIdl) = isone(minimum(a))

################################################################################
#
#  Norm
#
################################################################################

# Assumes, that det(basis_mat(a)) == 1
function assure_has_norm(a::NfRelOrdIdl{T, S}) where {T, S}
  if a.has_norm
    return nothing
  end
  if iszero(a)
    O = order(basis_pmat(a, Val{false}).coeffs[1])
    a.norm = O()*O
    a.has_norm = true
    return nothing
  end
  c = basis_pmat(a, Val{false}).coeffs
  d = inv_coeff_ideals(order(a), Val{false})
  n = c[1]*d[1]
  for i = 2:degree(order(a))
    n *= c[i]*d[i]
  end
  if T == nf_elem
    simplify(n)
    @assert n.den == 1
    a.norm = n.num
  else
    @assert denominator(n) == 1
    a.norm = NfRelOrdIdl{typeof(n).parameters...}(order(n), basis_pmat(n, Val{false}))
  end
  a.has_norm = true
  return nothing
end

@doc Markdown.doc"""
***
    norm(a::NfRelOrdIdl) -> NfOrdIdl

> Returns the norm of $a$.
"""
function norm(a::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
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
    +(a::NfRelOrdIdl, b::NfRelOrdIdl) -> NfRelOrdIdl

> Returns $a + b$.
"""
function +(a::NfRelOrdIdl{T, S}, b::NfRelOrdIdl{T, S}) where {T, S}
  d = degree(order(a))
  H = vcat(basis_pmat(a), basis_pmat(b))
  if T == nf_elem
    m = norm(a) + norm(b)
    H = sub(pseudo_hnf_full_rank_with_modulus(H, m, :lowerleft), (d + 1):2*d, 1:d)
  else
    H = sub(pseudo_hnf(H, :lowerleft), (d + 1):2*d, 1:d)
  end
  return ideal(order(a), H, false, true)
end

################################################################################
#
#  Ideal multiplication
#
################################################################################

@doc Markdown.doc"""
    *(a::NfRelOrdIdl, b::NfRelOrdIdl) -> NfRelOrdIdl

> Returns $a \cdot b$.
"""
function *(a::NfRelOrdIdl{T, S}, b::NfRelOrdIdl{T, S}) where {T, S}
  if iszero(a) || iszero(b)
    return order(a)()*order(a)
  end
  pba = pseudo_basis(a, Val{false})
  pbb = pseudo_basis(b, Val{false})
  ma = basis_mat(a, Val{false})
  mb = basis_mat(b, Val{false})
  L = nf(order(a))
  K = base_ring(L)
  d = degree(order(a))
  M = zero_matrix(K, d^2, d)
  C = Array{typeof(a).parameters[2], 1}(undef, d^2)
  t = L()
  for i = 1:d
    for j = 1:d
      mul!(t, pba[i][1], pbb[j][1])
      elem_to_mat_row!(M, (i - 1)*d + j, t)
      C[(i - 1)*d + j] = simplify(pba[i][2]*pbb[j][2])
    end
  end
  if T == nf_elem
    m = norm(a)*norm(b)
    H = sub(pseudo_hnf_full_rank_with_modulus(PseudoMatrix(M, C), m, :lowerleft), (d*(d - 1) + 1):d^2, 1:d)
  else
    H = sub(pseudo_hnf(PseudoMatrix(M, C), :lowerleft), (d*(d - 1) + 1):d^2, 1:d)
  end
  H.matrix = H.matrix*basis_mat_inv(order(a), Val{false})
  if T == nf_elem
    H = pseudo_hnf_full_rank_with_modulus(H, m, :lowerleft)
  else
    H = pseudo_hnf(H, :lowerleft)
  end
  return ideal(order(a), H, false, true)
end

Base.:(^)(A::NfRelOrdIdl, e::Int) = Base.power_by_squaring(A, e)

################################################################################
#
#  Ad hoc multiplication
#
################################################################################

@doc Markdown.doc"""
***
    *(a:NfRelOrdIdl{T, S}, x::T) -> NfRelOrdIdl{T, S}

> Returns the ideal $x\cdot a$.
"""
function *(a::NfRelOrdIdl{T, S}, x::T) where {T, S}
  if iszero(x)
    return order(a)()*order(a)
  end
  bp = basis_pmat(a)
  P = PseudoMatrix(bp.matrix, Ref(x) .* bp.coeffs)
  return ideal(order(a), P, true, true)
end

*(x::T, a::NfRelOrdIdl{T, S}) where {T, S} = a*x

function *(a::Union{NfRelOrdIdl, NfRelOrdFracIdl}, b::fmpz)
  if iszero(b)
    return order(a)()*order(a)
  end
  PM = basis_pmat(a)
  for i = 1:degree(order(a))
    PM.coeffs[i] = PM.coeffs[i]*b
    PM.coeffs[i] = simplify(PM.coeffs[i])
  end
  return typeof(a)(order(a), PM)
end

*(b::fmpz, a::Union{NfRelOrdIdl, NfRelOrdFracIdl}) = a*b

################################################################################
#
#  Intersection / LCM
#
################################################################################

@doc Markdown.doc"""
    intersection(a::NfRelOrdIdl, b::NfRelOrdIdl) -> NfRelOrdIdl

> Returns $a \cap b$.
"""
function intersection(a::NfRelOrdIdl{T, S}, b::NfRelOrdIdl{T, S}) where {T, S}
  d = degree(order(a))
  Ma = basis_pmat(a)
  Mb = basis_pmat(b)
  M1 = hcat(Ma, deepcopy(Ma))
  z = zero_matrix(base_ring(Ma.matrix), d, d)
  M2 = hcat(PseudoMatrix(z, Mb.coeffs), Mb)
  M = vcat(M1, M2)
  if T == nf_elem
    m = intersection(norm(a), norm(b))
    H = sub(pseudo_hnf_full_rank_with_modulus(M, m, :lowerleft), 1:d, 1:d)
  else
    H = sub(pseudo_hnf(M, :lowerleft), 1:d, 1:d)
  end
  return ideal(order(a), H, false, true)
end

################################################################################
#
#  Inverse
#
################################################################################

@doc Markdown.doc"""
***
      inv(a::NfRelOrdIdl) -> NfRelOrdFracIdl
      inv(a::NfRelOrdFracIdl) -> NfRelOrdFracIdl

> Computes the inverse of $a$, that is, the fractional ideal $b$ such that
> $ab = O$, where $O$ is the ambient order of $a$. $O$ must be maximal.
"""
function inv(a::Union{NfRelOrdIdl{T, S}, NfRelOrdFracIdl{T, S}}) where {T, S}
  if !ismaximal(order(a))
    error("Not implemented (yet).")
  end
  @assert !iszero(a)
  O = order(a)
  d = degree(O)
  pb = pseudo_basis(a, Val{false})
  bmO = basis_mat(O, Val{false})
  bmOinv = basis_mat_inv(O, Val{false})
  M = bmO*representation_matrix(pb[1][1])*bmOinv
  for i = 2:d
    M = hcat(M, bmO*representation_matrix(pb[i][1])*bmOinv)
  end
  invcoeffs = inv_coeff_ideals(O, Val{false})
  C = Array{S}(undef, d^2)
  for i = 1:d
    for j = 1:d
      C[(i - 1)*d + j] = simplify(pb[i][2]*invcoeffs[j])
    end
  end
  PM = PseudoMatrix(transpose(M), C)
  PM = sub(pseudo_hnf(PM, :upperright, true), 1:d, 1:d)
  N = inv(transpose(PM.matrix))
  PN = PseudoMatrix(N, [ simplify(inv(I)) for I in PM.coeffs ])
  PN = pseudo_hnf(PN, :lowerleft, true)
  return frac_ideal(O, PN, true)
end

################################################################################
#
#  Division
#
################################################################################

@doc Markdown.doc"""
***
      divexact(a::NfRelOrdIdl, b::NfRelOrdIdl) -> NfRelOrdFracIdl

> Returns $ab^{-1}$.
"""
function divexact(a::NfRelOrdIdl{T, S}, b::NfRelOrdIdl{T, S}) where {T, S}
  O = order(a)
  return frac_ideal(O, basis_pmat(a, Val{false}), true)*inv(b)
end

//(a::NfRelOrdIdl{T, S}, b::NfRelOrdIdl{T, S}) where {T, S} = divexact(a, b)

################################################################################
#
#  P-radical
#
################################################################################

# Returns an element x with v_p(x) = v_p(a) for all p in primes.
function element_with_valuation(a::T, primes::Vector{T}) where {T <: Union{NfOrdIdl, NfRelOrdIdl}}
  products = Vector{T}()
  for p in primes
    push!(products, a*p)
  end
  foundOne = false
  x = order(a)()
  while !foundOne
    x = rand(a, 2^61) # magic number
    foundOne = true
    for p in products
      if x in p
        foundOne = false
        break
      end
    end
  end
  return x
end

@doc Markdown.doc"""
***
      pradical(O::NfRelOrd, P::NfOrdIdl) -> NfRelOrdIdl

> Given a prime ideal $P$, this function returns the $P$-radical
> $\sqrt{P\mathcal O}$ of $\mathcal O$, which is
> just $\{ x \in \mathcal O \mid \exists k \in \mathbf Z_{\geq 0} \colon x^k
> \in P\mathcal O \}$. It is not checked that $P$ is prime.
"""
# Algorithm V.8. and VI.8. in "Berechnung relativer Ganzheitsbasen mit dem
# Round-2-Algorithmus" by C. Friedrichs.
function pradical(O::NfRelOrd, P::Union{NfOrdIdl, NfRelOrdIdl})
  d = degree(O)
  L = nf(O)
  K = base_ring(L)
  OK = maximal_order(K)
  pb = pseudo_basis(O, Val{false})

  is_absolute = (typeof(K) == AnticNumberField)

  # Compute a pseudo basis of O with integral ideals:
  basis_mat_int = zero_matrix(K, d, d)
  pbint = Vector{Tuple{elem_type(L), typeof(P)}}()
  for i = 1:d
    t = divexact(pb[i][1], denominator(pb[i][2]))
    if is_absolute
      push!(pbint, (t, deepcopy(numerator(pb[i][2]))))
    else
      push!(pbint, (t, numerator(pb[i][2])))
    end
    elem_to_mat_row!(basis_mat_int, i, t)
  end
  if is_absolute
    Oint = typeof(O)(L, PseudoMatrix(basis_mat_int, [ frac_ideal(OK, pbint[i][2], fmpz(1)) for i = 1:d ]))
  else
    Oint = typeof(O)(L, PseudoMatrix(basis_mat_int, [ frac_ideal(OK, basis_pmat(pbint[i][2], Val{false})) for i = 1:d ]))
  end

  if is_absolute
    pOK = ideal(OK, OK(minimum(P)))
  else
    pOK = minimum(P, Val{false})*OK
  end
  prime_ideals = factor(pOK)

  elts_with_val = Vector{elem_type(OK)}(undef, d)
  for i = 1:d
    elts_with_val[i] = element_with_valuation(pbint[i][2], [ p for (p, e) in prime_ideals ])
  end
  F, mF = ResidueField(OK, P)
  mmF = extend(mF, K)
  A = zero_matrix(F, d, d)

  # If the prime number in P is too small one can't use the trace.
  if is_absolute
    p = minimum(P)
  else
    p = prime_number(P)
  end
  if p <= d
    q = order(F)
    k = clog(fmpz(degree(Oint)), q)
    for i = 1:d
      t = Oint((L(K(elts_with_val[i]))*pbint[i][1])^(q^k))
      ar = elem_in_basis(t)
      for j = 1:d
        A[j, i] = mmF(divexact(ar[j], K(elts_with_val[j])))
      end
    end
  else
    for i = 1:d
      for j = i:d
        t = L(K(elts_with_val[i]))*pbint[i][1]*L(K(elts_with_val[j]))*pbint[j][1]
        A[i, j] = mF(OK(tr(t)))
        A[j, i] = deepcopy(A[i, j])
      end
    end
  end

  B = nullspace(A)[2]
  M1 = zero_matrix(K, d, d)
  imF = inv(mF)
  # Write a basis of the kernel of A in the rows of M1.
  for i = 1:cols(B)
    for j = 1:rows(B)
      M1[i, j] = K(imF(B[j, i])*elts_with_val[j])
    end
  end
  M2 = identity_matrix(K, d)
  PM1 = PseudoMatrix(M1)
  # PM2 is the basis pseudo matrix of P*Oint
  PM2 = PseudoMatrix(M2, [ pbint[i][2]*deepcopy(P) for i = 1:d ])
  PM = sub(pseudo_hnf(vcat(PM1, PM2), :lowerleft, true), (d + 1):2*d, 1:d)

  # Write PM in the basis of O (and not Oint)
  for j = 1:d
    t = K(denominator(pb[j][2]))
    for i = j:d
      PM.matrix[i, j] = divexact(PM.matrix[i, j], t)
    end
  end
  # TODO: Use that the matrix is already triangular
  PM = pseudo_hnf(PM, :lowerleft, true)
  return ideal(O, PM, false, true)
end

################################################################################
#
#  Ring of multipliers
#
################################################################################

@doc Markdown.doc"""
***
    ring_of_multipliers(a::NfRelOrdIdl) -> NfRelOrd

> Computes the order $(a : a)$, which is the set of all $x \in K$
> with $xa \subseteq a$, where $K$ is the ambient number field
> of $a$.
"""
# Algorithm VII.1. in "Berechnung relativer Ganzheitsbasen mit dem
# Round-2-Algorithmus" by C. Friedrichs.
function ring_of_multipliers(a::NfRelOrdIdl{T1, T2}) where {T1, T2}
  O = order(a)
  K = base_ring(nf(O))
  d = degree(O)
  pb = pseudo_basis(a, Val{false})
  S = basis_mat_inv(O, Val{false})*basis_mat_inv(a, Val{false})
  M = basis_mat(O, Val{false})*representation_matrix(pb[1][1])*S
  for i = 2:d
    M = hcat(M, basis_mat(O, Val{false})*representation_matrix(pb[i][1])*S)
  end
  invcoeffs = [ simplify(inv(pb[i][2])) for i = 1:d ]
  C = Array{T2}(undef, d^2)
  for i = 1:d
    for j = 1:d
      if i == j
        C[(i - 1)*d + j] = K(1)*order(pb[i][2])
      else
        C[(i - 1)*d + j] = simplify(pb[i][2]*invcoeffs[j])
      end
    end
  end
  PM = PseudoMatrix(transpose(M), C)
  PM = sub(pseudo_hnf(PM, :upperright, true), 1:d, 1:d)
  N = inv(transpose(PM.matrix))*basis_mat(O, Val{false})
  PN = PseudoMatrix(N, [ simplify(inv(I)) for I in PM.coeffs ])
  PN = pseudo_hnf(PN, :lowerleft, true)
  return NfRelOrd{T1, T2}(nf(O), PN)
end

################################################################################
#
#  Absolute to relative
#
################################################################################

function relative_ideal(a::NfOrdIdl, m::NfRelToNf)
  L = domain(m)
  Labs = codomain(m)
  @assert nf(order(a)) == Labs
  K = base_ring(L)
  O = relative_order(order(a), m)
  mm = inv(m)
  B = basis(a, Val{false})
  d = degree(L)
  dabs = degree(Labs)
  M = zero_matrix(K, dabs, d)
  for i = 1:dabs
    elem_to_mat_row!(M, i, mm(Labs(B[i])))
  end
  M = M*basis_mat_inv(O, Val{false})
  PM = sub(pseudo_hnf(PseudoMatrix(M), :lowerleft, true), (dabs - d + 1):dabs, 1:d)
  return ideal(O, PM, false, true)
end

################################################################################
#
#  Index divisors
#
################################################################################

function isindex_divisor(O::NfRelOrd, p::Union{NfOrdIdl, NfRelOrdIdl})
  f = nf(O).pol
  return valuation(discriminant(f), p) != valuation(discriminant(O), p)
end

################################################################################
#
#  Prime decomposition
#
################################################################################

function prime_decomposition(O::NfRelOrd, p::Union{NfOrdIdl, NfRelOrdIdl})
  if isindex_divisor(O, p)
    return prime_dec_index(O, p)
  end

  return prime_dec_nonindex(O, p)
end

function prime_dec_nonindex(O::NfRelOrd, p::Union{NfOrdIdl, NfRelOrdIdl})
  L = nf(O)
  OK = order(p)
  @assert OK == O.basis_pmat.coeffs[1].order
  @assert OK.ismaximal == 1
  a = gen(L)
  K = base_ring(L)
  f = L.pol

  Kx = parent(f)
  Fp, mF = ResidueField(OK, p)
  mmF = extend(mF, K)
  immF = inv(mmF)
  Fy, y = PolynomialRing(Fp,"y", cached=false)
  fmodp = Hecke.nf_elem_poly_to_fq_poly(Fy, mmF, f)
  fac = factor(fmodp)
  result = Array{Tuple{NfRelOrdIdl{typeof(O).parameters...}, Int}, 1}()
  for (q, e) in fac
    g = Hecke.fq_poly_to_nf_elem_poly(Kx, immF, q)
    ga = g(a)
    P = ideal(O, L(1), ga, p, OK(1)*OK)
    P.is_prime = 1
    P.splitting_type = (e, degree(q))
    P.minimum = deepcopy(p)
    P.non_index_div_poly = q
    Oga = O(ga)
    # TODO: Warum funktioniert das? Muss uniformizer(p) ein p-uniformizer sein?
    if iszero(Oga)
      @assert e == 1
      P.p_uniformizer = O(uniformizer(p))
    else
      if e != 1
        P.p_uniformizer = Oga
      else
        if valuation(Oga, P) == 1
          P.p_uniformizer = Oga
        else
          P.p_uniformizer = Oga + O(uniformizer(p))
        end
      end
    end
    push!(result, (P, e))
  end
  return result
end

function prime_dec_index(O::NfRelOrd, p::Union{NfOrdIdl, NfRelOrdIdl})
  L = nf(O)
  K = base_ring(L)
  pbasisO = pseudo_basis(O, Val{false})
  pO = p*O

  Ip = pradical(O, p)
  A, OtoA = AlgAss(O, Ip, p)
  AtoO = inv(OtoA)
  AA = decompose(A)

  result = Vector{Tuple{NfRelOrdIdl{typeof(O).parameters...}, Int}}()
  m = PseudoMatrix(zero_matrix(K, 1, degree(O)))
  for (B, BtoA) in AA
    f = dim(B)
    idem = BtoA(B[1]) # Assumes that B == idem*A
    M = representation_matrix(idem)
    ker = left_kernel(M)
    N = basis_pmat(Ip)
    for i = 1:length(ker)
      b = elem_in_basis(AtoO(A(ker[i])))
      for j = 1:degree(O)
        m.matrix[1, j] = b[j]
      end
      N = vcat(N, deepcopy(m))
    end
    N = sub(pseudo_hnf(N, :lowerleft), rows(N) - degree(O) + 1:rows(N), 1:degree(O))
    P = ideal(O, N, false, true)
    P.is_prime = 1
    e = valuation(pO, P)
    P.splitting_type = (e, f)
    P.minimum = deepcopy(p)
    push!(result, (P, e))
  end

  return result
end

################################################################################
#
#  Reduction of element modulo ideal
#
################################################################################

function mod(a::NfRelOrdElem, I::NfRelOrdIdl)
  O = order(I)
  b = elem_in_basis(a)
  PM = basis_pmat(I, Val{false}) # PM is assumed to be in pseudo hnf
  for i = degree(O):-1:1
    t = b[i] - mod(b[i], PM.coeffs[i])
    for j = 1:i
      b[j] = b[j] - t*PM.matrix[i, j]
    end
  end
  return O(b)
end

################################################################################
#
#  Valuation
#
################################################################################

function valuation_naive(A::NfRelOrdIdl{T, S}, B::NfRelOrdIdl{T, S}) where {T, S}
  @assert order(A.basis_pmat.coeffs[1]) == order(B.basis_pmat.coeffs[1])
  @assert !iszero(A) && !iszero(B)
  O = order(A)
  Afrac = frac_ideal(O, basis_pmat(A), true)
  Bi = inv(B)
  i = 0
  C = Afrac*Bi
  @assert C != Afrac
  while isintegral(C)
    C = C*Bi
    i += 1
  end
  return i
end

valuation(A::NfRelOrdIdl{T, S}, B::NfRelOrdIdl{T, S}) where {T, S} = valuation_naive(A, B)

function valuation_naive(a::NfRelOrdElem{T}, B::NfRelOrdIdl{T, S}) where {T, S}
  @assert !iszero(a)
  @assert order(parent(a).basis_pmat.coeffs[1]) == order(B.basis_pmat.coeffs[1])
  @assert order((a * parent(a)).basis_pmat.coeffs[1]) == order(B.basis_pmat.coeffs[1])
  return valuation(a*parent(a), B)
end

valuation(a::NfRelOrdElem{T}, B::NfRelOrdIdl{T, S}) where {T, S} = valuation_naive(a, B)

valuation(a::fmpz, B::NfRelOrdIdl) = valuation(order(B)(a), B)

################################################################################
#
#  Factorization into prime ideals
#
################################################################################

function factor(A::NfRelOrdIdl{T, S}) where {T, S}
  n = norm(A)
  normFactors = factor(n)
  result = Dict{NfRelOrdIdl{T, S}, Int}()
  O = order(A)
  for p in keys(normFactors)
    prime_dec = prime_decomposition(O, p)
    for (P, e) in prime_dec
      v = valuation(A, P)
      if v != 0
        result[P] = v
        n = n//norm(P)^v
        simplify(n)
      end
      if isone(n)
        return result
      end
    end
  end
  return result
end

################################################################################
#
#  Minimum
#
################################################################################

@doc Markdown.doc"""
***
      minimum(A::NfRelOrdIdl) -> NfOrdIdl
      minimum(A::NfRelOrdIdl) -> NfRelOrdIdl

> Returns the ideal $A \cap O$ where $O$ is the maximal order of the coefficient
> ideals of $A$.
"""
function minimum(A::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_minimum(A)
  if copy == Val{true}
    return deepcopy(A.minimum)
  else
    return A.minimum
  end
end

function assure_has_minimum(A::NfRelOrdIdl)
  if isdefined(A, :minimum)
    return nothing
  end
  @assert isone(basis_pmat(A, Val{false}).matrix[1, 1])
  @assert isone(basis_pmat(order(A), Val{false}).matrix[1, 1])

  M = deepcopy(basis_pmat(A, Val{false}).coeffs[1])
  M = simplify(M)
  A.minimum = numerator(M)
  return nothing
end

################################################################################
#
#  Order modulo prime ideal
#
################################################################################

function ResidueField(O::NfRelOrd{T, S}, P::NfRelOrdIdl{T, S}) where {T, S}
  @assert order(P) == O
  @assert P.is_prime == 1
  mF = NfRelOrdToFqMor{T, S}(O, P)
  return codomain(mF), mF
end

################################################################################
#
#  Idempotents
#
################################################################################

@doc Markdown.doc"""
    idempotents(x::NfRelOrdIdl, y::NfRelOrdIdl) -> NfRelOrdElem, NfRelOrdElem

> Returns a tuple `(e, f)` consisting of elements `e in x`, `f in y` such that
> `1 = e + f`.
>
> If the ideals are not coprime, an error is raised.
"""
function idempotents(x::NfRelOrdIdl{T, S}, y::NfRelOrdIdl{T, S}) where {T, S}
  !(order(x) == order(y)) && error("Parent mismatch")

  O = order(x)
  mx = minimum(x, Val{false})
  my = minimum(y, Val{false})
  g = mx + my
  if isone(g)
    u, v = idempotents(mx, my)
    return O(u), O(v)
  end

  d = degree(O)
  L = nf(O)
  K = base_ring(L)
  OK = maximal_order(K)
  M = zero_matrix(K, 2*d + 1, 2*d + 1)

  M[1, 1] = K(1)
  z = elem_in_basis(one(O))
  for i = 1:d
    M[1, i + 1] = z[i]
  end
  for i = 1:d
    for j = 1:d
      M[i + 1, j + 1] = deepcopy(basis_mat(x, Val{false})[i, j])
      M[i + 1 + d, j + 1] = deepcopy(basis_mat(y, Val{false})[i, j])
    end
    M[i + 1, i + d + 1] = K(1)
  end

  #=
    M is now
    ( 1 |  1  |  0  )
    ( 0 | M_x | I_d )
    ( 0 | M_y |  0  )
  =#

  coeffsx = deepcopy(basis_pmat(x, Val{false}).coeffs)
  coeffsy = deepcopy(basis_pmat(y, Val{false}).coeffs)
  C = [ K(1)*OK, coeffsx..., coeffsy... ]
  PM = PseudoMatrix(M, C)
  PM = pseudo_hnf(PM, :upperright)

  for i = 2:(d + 1)
    if !iszero(PM.matrix[1, i])
      error("Ideals are not coprime")
    end
  end

  pbx = pseudo_basis(x, Val{false})
  u = pbx[1][1]*PM.matrix[1, d + 2]
  for i = 2:d
    u += pbx[i][1]*PM.matrix[1, d + 1 + i]
  end

  @assert -u in x
  @assert u + 1 in y

  return O(-u), O(u + 1)
end

################################################################################
#
#  Inclusion of elements in ideals
#
################################################################################

@doc Markdown.doc"""
***
    in(x::NfRelOrdElem, y::NfRelOrdIdl)
    in(x::RelativeElement, y::NfRelOrdIdl)
    in(x::fmpz, y::NfRelOrdIdl)

> Returns whether $x$ is contained in $y$.
"""
function in(x::NfRelOrdElem, y::NfRelOrdIdl)
  parent(x) != order(y) && error("Order of element and ideal must be equal")
  O = order(y)
  b_pmat = basis_pmat(y, Val{false})
  t = transpose(matrix(base_ring(nf(O)), degree(O), 1, elem_in_basis(x)))
  t = t*basis_mat_inv(y, Val{false})
  for i = 1:degree(O)
    if !(t[1, i] in b_pmat.coeffs[i])
      return false
    end
  end
  return true
end

function in(x::RelativeElement, y::NfRelOrdIdl)
  parent(x) != nf(order(y)) && error("Number field of element and ideal must be equal")
  return in(order(y)(x),y)
end

in(x::fmpz, y::NfRelOrdIdl) = in(order(y)(x),y)

################################################################################
#
#  (Anti-)Uniformizer
#
################################################################################

@doc Markdown.doc"""
***
    uniformizer(P::NfRelOrdIdl) -> NfRelOrdElem

> Returns an element $u \in P$ with valuation(u, P) == 1.
"""
function uniformizer(P::NfRelOrdIdl)
  @assert P.is_prime == 1

  if P.splitting_type[1] == 1
    return order(P)(uniformizer(minimum(P, Val{false})))
  end

  r = 500 # hopefully enough
  z = rand(P, r)
  while true
    if !iszero(z) && valuation(z, P) == 1
      break
    end
    z = rand(P, r)
  end
  return z
end

function _is_p_uniformizer(z::NfRelOrdElem, P::T, primes::Vector{T}) where {T <: NfRelOrdIdl}
  if iszero(z)
    return false
  end
  if valuation(z, P) != 1
    return false
  end
  for PP in primes
    if valuation(z, PP) != 0
      return false
    end
  end
  return true
end

@doc Markdown.doc"""
***
    p_uniformizer(P::NfRelOrdIdl) -> NfRelOrdElem

> Returns an element $u \in P$ with valuation(u, P) == 1 and valuation 0 at all
> other prime ideals lying over minimum(P).
"""
function p_uniformizer(P::NfRelOrdIdl)
  @assert P.is_prime == 1

  if isdefined(P, :p_uniformizer)
    return P.p_uniformizer
  end

  p = minimum(P, Val{false})
  prime_dec = prime_decomposition(order(P), p)
  primes = Vector{typeof(P)}()
  for (PP, e) in prime_dec
    if PP != P
      push!(primes, PP)
    end
  end
  r = 500
  z = rand(P, r)
  while !_is_p_uniformizer(z, P, primes)
    z = rand(P, r)
  end
  P.p_uniformizer = z
  return z
end

@doc Markdown.doc"""
***
    anti_uniformizer(P::NfRelOrdIdl) -> RelativeElement

> Returns an element $a$ in the number field containing $P$ with valuation(a, P) == -1
> and non-negative valuation at all other prime ideals.
"""
function anti_uniformizer(P::NfRelOrdIdl{T, S}) where {T, S}
  @assert P.is_prime == 1

  if isdefined(P, :anti_uniformizer)
    return P.anti_uniformizer
  end

  p = minimum(P, Val{false})
  # We need a pseudo basis of O, where the coefficient ideals have valuation
  # 0 at p.
  O = order(P)
  N = basis_mat(O)
  NN = basis_mat_inv(O)
  d = Vector{T}(undef, degree(O))
  a = elem_in_nf(uniformizer(p))
  for i = 1:degree(O)
    v = valuation(pseudo_basis(O, Val{false})[i][2], p)
    if !iszero(v)
      d[i] = a^v
      mul_row!(N, i, d[i])
      mul_col!(NN, i, inv(d[i]))
    else
      d[i] = base_ring(nf(O))(1)
    end
  end

  u = elem_in_nf(p_uniformizer(P))
  M = representation_matrix(u)
  M = N*M*NN

  F, mF = ResidueField(order(p), p)
  mmF = extend(mF, nf(order(p)))
  immF = inv(mmF)
  Mp = zero_matrix(F, rows(M), cols(M))
  for i = 1:rows(M)
    for j = 1:cols(M)
      Mp[i, j] = mmF(M[i, j])
    end
  end
  K = left_kernel(Mp)
  @assert length(K) > 0
  x = nf(O)()
  for i = 1:degree(O)
    x += immF(K[1][i])*pseudo_basis(O, Val{false})[i][1]*d[i]
  end
  P.anti_uniformizer = x*anti_uniformizer(p)
  return P.anti_uniformizer
end

################################################################################
#
#  Random elements
#
################################################################################

function rand(a::NfRelOrdIdl, B::Int)
  pb = pseudo_basis(a, Val{false})
  z = nf(order(a))()
  for i = 1:degree(order(a))
    t = rand(pb[i][2], B)
    z += t*pb[i][1]
  end
  return order(a)(z)
end

################################################################################
#
#  Prime number in a prime ideal
#
################################################################################

function prime_number(p::NfRelOrdIdl)
  @assert p.is_prime == 1
  m = minimum(p, Val{false})
  if typeof(m) == NfOrdIdl
    return minimum(m)
  else
    return prime_number(m)
  end
end

################################################################################
#
#  Something with coprime
#
################################################################################

function coprime_to(I::NfRelOrdFracIdl, p::NfRelOrdIdl)
  pi = anti_uniformizer(p)
  a = rand(I, 500)
  l = valuation(a, p)
  @assert l >= 0
  if l > 0
    a = pi^l*a
  end
  @assert valuation(a, p) == 0
  return a
end
