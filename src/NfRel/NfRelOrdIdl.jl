################################################################################
#
#  Basic field access
#
################################################################################

doc"""
***
    order(a::NfRelOrdIdl) -> NfRelOrd

> Returns the order of $a$.
"""
order(a::NfRelOrdIdl) = a.order

doc"""
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

doc"""
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

doc"""
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

doc"""
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

doc"""
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
    showcompact(io, basis_pmat(a, Val{false}))
  else
    print(io, "Ideal of\n")
    showcompact(order(a))
    print(io, "\nwith basis pseudo-matrix\n")
    showcompact(io, basis_pmat(a, Val{false}))
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

doc"""
***
    ideal(O::NfRelOrd, M::PMat, check::Bool = true) -> NfRelOrdIdl

> Creates the ideal of $\mathcal O$ with basis pseudo-matrix $M$. If check is set,
> then it is checked whether $M$ defines an ideal.
"""
function ideal(O::NfRelOrd{T, S}, M::PMat{T, S}, check::Bool = true) where {T, S}
  if check
    !defines_ideal(O, M) && error("The pseudo-matrix does not define an ideal.")
  end
  H = pseudo_hnf(M, :lowerleft, true)
  return NfRelOrdIdl{T, S}(O, H)
end

doc"""
***
    ideal(O::NfRelOrd, M::Generic.Mat, check::Bool = true) -> NfRelOrdIdl

> Creates the ideal of $\mathcal O$ with basis matrix $M$. If check is set,
> then it is checked whether $M$ defines an ideal.
"""
function ideal(O::NfRelOrd{T, S}, M::Generic.Mat{T}, check::Bool = true) where {T, S}
  coeffs = deepcopy(basis_pmat(O, Val{false})).coeffs
  return ideal(O, PseudoMatrix(M, coeffs), check)
end

doc"""
***
    ideal(O::NfRelOrd{T, S}, x::NfRelElem{T}, y::NfRelElem{T}, a::S, b::S, check::Bool = true) -> NfRelOrdIdl{T, S}

> Creates the ideal $x\cdot a + y\cdot b$ of $\mathcal O$. If check is set,
> then it is checked whether these elements define an ideal.
"""
function ideal(O::NfRelOrd{T, S}, x::NfRelElem{T}, y::NfRelElem{T}, a::S, b::S, check::Bool = true) where {T, S}
  d = degree(O)
  pb = pseudo_basis(O, Val{false})
  M = zero_matrix(base_ring(nf(O)), 2*d, d)
  C = Array{S}(2*d)
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

doc"""
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

doc"""
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

doc"""
***
    *(O::NfRelOrd{T, S}, a::S) -> NfRelOrdIdl{T, S}
    *(a::S, O::NfRelOrd{T, S}) -> NfRelOrdIdl{T, S}

> Creates the ideal $a \cdot \mathcal O$ of $\mathcal O$.
"""
*(O::NfRelOrd{T, S}, a::S) where {T, S} = ideal(O, a)

*(a::S, O::NfRelOrd{T, S}) where {T, S} = ideal(O, a)

*(O::NfRelOrd{nf_elem, NfOrdFracIdl}, a::NfOrdIdl) = ideal(O, a)

*(a::NfOrdIdl, O::NfRelOrd{nf_elem, NfOrdFracIdl}) = ideal(O, a)

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::NfRelOrdIdl{T, S}, dict::ObjectIdDict) where {T, S}
  z = NfRelOrdIdl{T, S}(a.order)
  for x in fieldnames(a)
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

doc"""
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
#  Norm
#
################################################################################

# Assumes, that det(basis_mat(a)) == 1
function assure_has_norm(a::NfRelOrdIdl)
  if a.has_norm
    return nothing
  end
  c = basis_pmat(a, Val{false}).coeffs
  d = inv_coeff_ideals(order(a), Val{false})
  n = c[1]*d[1]
  for i = 2:degree(order(a))
    n *= c[i]*d[i]
  end
  simplify(n)
  @assert n.den == 1
  a.norm = n.num
  a.has_norm = true
  return nothing
end

doc"""
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

doc"""
***
    +(a::NfRelOrdIdl, b::NfRelOrdIdl) -> NfRelOrdIdl
    +(a::NfRelOrdFracIdl, b::NfRelOrdFracIdl) -> NfRelOrdFracIdl

> Returns $a + b$.
"""
function +(a::Union{NfRelOrdIdl{T, S}, NfRelOrdFracIdl{T, S}}, b::Union{NfRelOrdIdl{T, S}, NfRelOrdFracIdl{T, S}}) where {T, S}
  d = degree(order(a))
  H = vcat(basis_pmat(a), basis_pmat(b))
  #m = norm(a) + norm(b)
  #H = sub(pseudo_hnf_full_rank_with_modulus(H, m, :lowerleft), (d + 1):2*d, 1:d)
  H = sub(pseudo_hnf(H, :lowerleft, true), (d + 1):2*d, 1:d)
  return typeof(a)(order(a), H)
end

################################################################################
#
#  Ideal multiplication
#
################################################################################

doc"""
    *(a::NfRelOrdIdl, b::NfRelOrdIdl) -> NfRelOrdIdl
    *(a::NfRelOrdFracIdl, b::NfRelOrdFracIdl) -> NfRelOrdFracIdl

> Returns $a \cdot b$.
"""
function *(a::Union{NfRelOrdIdl{T, S}, NfRelOrdFracIdl{T, S}}, b::Union{NfRelOrdIdl{T, S}, NfRelOrdFracIdl{T, S}}) where {T, S}
  pba = pseudo_basis(a, Val{false})
  pbb = pseudo_basis(b, Val{false})
  ma = basis_mat(a, Val{false})
  mb = basis_mat(b, Val{false})
  L = nf(order(a))
  K = base_ring(L)
  d = degree(order(a))
  M = zero_matrix(K, d^2, d)
  C = Array{S, 1}(d^2)
  t = L()
  for i = 1:d
    for j = 1:d
      mul!(t, pba[i][1], pbb[j][1])
      elem_to_mat_row!(M, (i - 1)*d + j, t)
      C[(i - 1)*d + j] = simplify(pba[i][2]*pbb[j][2])
    end
  end
  #m = norm(a)*norm(b)
  #H = sub(pseudo_hnf_full_rank_with_modulus(PseudoMatrix(M, C), m, :lowerleft), (d*(d - 1) + 1):d^2, 1:d)
  H = sub(pseudo_hnf(PseudoMatrix(M, C), :lowerleft, true), (d*(d - 1) + 1):d^2, 1:d)
  H.matrix = H.matrix*basis_mat_inv(order(a), Val{false})
  #H = pseudo_hnf_full_rank_with_modulus(H, m, :lowerleft)
  H = pseudo_hnf(H, :lowerleft, true)
  return typeof(a)(order(a), H)
end

################################################################################
#
#  Ad hoc multiplication
#
################################################################################

doc"""
***
    *(a:NfRelOrdIdl{T, S}, x::T) -> NfRelOrdIdl{T, S}

> Returns the ideal $x\cdot a$.
"""
function *(a::NfRelOrdIdl{T, S}, x::T) where {T, S}
  bp = basis_pmat(a)
  P = PseudoMatrix(bp.matrix, x.*bp.coeffs)
  !defines_ideal(order(a), P) && error("The pseudo-matrix does not define an ideal.")
  return NfRelOrdIdl{T, S}(order(a), P)
end

*(x::T, a::NfRelOrdIdl{T, S}) where {T, S} = a*x

################################################################################
#
#  Intersection / LCM
#
################################################################################

doc"""
    intersection(a::NfRelOrdIdl, b::NfRelOrdIdl) -> NfRelOrdIdl
    intersection(a::NfRelOrdFracIdl, b::NfRelOrdFracIdl) -> NfRelOrdFracIdl

> Returns $a \cap b$.
"""
function intersection(a::Union{NfRelOrdIdl{T, S}, NfRelOrdFracIdl{T, S}}, b::Union{NfRelOrdIdl{T, S}, NfRelOrdFracIdl{T, S}}) where {T, S}
  d = degree(order(a))
  Ma = basis_pmat(a)
  Mb = basis_pmat(b)
  M1 = hcat(Ma, deepcopy(Ma))
  z = zero_matrix(base_ring(Ma.matrix), d, d)
  M2 = hcat(PseudoMatrix(z, Mb.coeffs), Mb)
  M = vcat(M1, M2)
  #m = intersection(norm(a), norm(b))
  #H = sub(pseudo_hnf_full_rank_with_modulus(M, m, :lowerleft), 1:d, 1:d)
  H = sub(pseudo_hnf(M, :lowerleft, true), 1:d, 1:d)
  return typeof(a)(order(a), H)
end

################################################################################
#
#  Inverse
#
################################################################################

doc"""
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
  O = order(a)
  d = degree(O)
  pb = pseudo_basis(a, Val{false})
  bmO = basis_mat(O, Val{false})
  bmOinv = basis_mat_inv(O, Val{false})
  M = bmO*representation_mat(pb[1][1])*bmOinv
  for i = 2:d
    M = hcat(M, bmO*representation_mat(pb[i][1])*bmOinv)
  end
  invcoeffs = inv_coeff_ideals(O, Val{false})
  C = Array{S}(d^2)
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
  return NfRelOrdFracIdl{T, S}(O, PN)
end

################################################################################
#
#  Division
#
################################################################################

doc"""
***
      divexact(a::NfRelOrdIdl, b::NfRelOrdIdl) -> NfRelOrdFracIdl

> Returns $ab^{-1}$.
"""
function divexact(a::NfRelOrdIdl{T, S}, b::NfRelOrdIdl{T, S}) where {T, S}
  O = order(a)
  return NfRelOrdFracIdl{T, S}(O, basis_pmat(a))*inv(b)
end

################################################################################
#
#  P-radical
#
################################################################################

# Returns an element x with v_p(x) = v_p(a) for all p in primes.
function element_with_valuation(a::NfOrdIdl, primes::Vector{NfOrdIdl})
  products = Vector{NfOrdIdl}()
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

doc"""
***
      pradical(O::NfRelOrd, p::NfOrdIdl) -> NfRelOrdIdl

> Given a prime ideal number $p$, this function returns the $p$-radical
> $\sqrt{p\mathcal O}$ of $\mathcal O$, which is
> just $\{ x \in \mathcal O \mid \exists k \in \mathbf Z_{\geq 0} \colon x^k
> \in p\mathcal O \}$. It is not checked that $p$ is prime.
"""
# Algorithm V.8. and VI.8. in "Berechnung relativer Ganzheitsbasen mit dem
# Round-2-Algorithmus" by C. Friedrichs.
# If return_integral is true then the returned ideal is ideal of a
# order with integral coefficient ideals.
function pradical(O::NfRelOrd{nf_elem, NfOrdFracIdl}, p::NfOrdIdl, return_integral::Bool = false)
  d = degree(O)
  L = nf(O)
  K = base_ring(L)
  OK = maximal_order(K)
  pb = pseudo_basis(O, Val{false})

  # Compute a pseudo basis of O with integral ideals:
  basis_mat_int = zero_matrix(K, d, d)
  pbint = Vector{Tuple{elem_type(L), NfOrdIdl}}()
  for i = 1:d
    t = divexact(pb[i][1], denominator(pb[i][2]))
    push!(pbint, (t, deepcopy(numerator(pb[i][2]))))
    elem_to_mat_row!(basis_mat_int, i, t)
  end
  Oint = NfRelOrd{nf_elem, NfOrdFracIdl}(L, PseudoMatrix(basis_mat_int, [ frac_ideal(OK, pbint[i][2], fmpz(1)) for i = 1:d ]))

  pOK = ideal(OK, OK(minimum(p)))
  prime_ideals = factor(pOK)
  elts_with_val = Vector{NfOrdElem}(d)
  for i = 1:d
    elts_with_val[i] = element_with_valuation(pbint[i][2], [ p for (p, e) in prime_ideals ])
  end
  F, mF = ResidueField(OK, p)
  mmF = extend(mF, K)
  A = zero_matrix(F, d, d)

  # If minimum(p) is too small one can't use the trace.
  if minimum(p) <= d
    q = norm(p)
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
        A[i, j] = mF(OK(trace(t)))
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
  # PM2 is the basis pseudo matrix of p*Oint
  PM2 = PseudoMatrix(M2, [ pbint[i][2]*deepcopy(p) for i = 1:d ])
  PM = sub(pseudo_hnf(vcat(PM1, PM2), :lowerleft, true), (d + 1):2*d, 1:d)

  if return_integral
    return NfRelOrdIdl{nf_elem, NfOrdFracIdl}(Oint, PM)
  end

  # Write PM in the basis of O (and not Oint)
  for j = 1:d
    t = K(denominator(pb[j][2]))
    for i = j:d
      PM.matrix[i, j] = divexact(PM.matrix[i, j], t)
    end
  end
  # TODO: Use that the matrix is already triangular
  PM = pseudo_hnf(PM, :lowerleft, true)
  return NfRelOrdIdl{nf_elem, NfOrdFracIdl}(O, PM)
end

################################################################################
#
#  Ring of multipliers
#
################################################################################

doc"""
***
    ring_of_multipliers(a::NfRelOrdIdl) -> NfRelOrd

> Computes the order $(a : a)$, which is the set of all $x \in K$
> with $xa \subseteq a$, where $K$ is the ambient number field
> of $a$.
"""
# Algorithm VII.1. in "Berechnung relativer Ganzheitsbasen mit dem
# Round-2-Algorithmus" by C. Friedrichs.
function ring_of_multipliers(a::NfRelOrdIdl{nf_elem, NfOrdFracIdl})
  O = order(a)
  K = base_ring(nf(O))
  d = degree(O)
  pb = pseudo_basis(a, Val{false})
  S = basis_mat_inv(O, Val{false})*basis_mat_inv(a, Val{false})
  M = basis_mat(O, Val{false})*representation_mat(pb[1][1])*S
  for i = 2:d
    M = hcat(M, basis_mat(O, Val{false})*representation_mat(pb[i][1])*S)
  end
  invcoeffs = [ simplify(inv(pb[i][2])) for i = 1:d ]
  C = Array{NfOrdFracIdl}(d^2)
  for i = 1:d
    for j = 1:d
      if i == j
        C[(i - 1)*d + j] = ideal(order(pb[i][2]), K(1))
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
  return NfRelOrd{nf_elem, NfOrdFracIdl}(nf(O), PN)
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
  return NfRelOrdIdl{typeof(PM.matrix[1, 1]), typeof(PM.coeffs[1])}(O, PM)
end

################################################################################
#
#  Index divisors
#
################################################################################

function isindex_divisor(O::NfRelOrd{nf_elem, NfOrdFracIdl}, p::NfOrdIdl)
  f = nf(O).pol
  return valuation(discriminant(f), p) != valuation(discriminant(O), p)
end

################################################################################
#
#  Prime decomposition
#
################################################################################

function prime_decomposition(O::NfRelOrd{nf_elem, NfOrdFracIdl}, p::NfOrdIdl)
  if isindex_divisor(O, p)
    return prime_dec_index(O, p)
  end

  return prime_dec_nonindex(O, p)
end

function prime_dec_nonindex(O::NfRelOrd{nf_elem, NfOrdFracIdl}, p::NfOrdIdl)
  L = nf(O)
  a = gen(L)
  K = base_ring(L)
  OK = MaximalOrder(K)
  @assert order(p) == OK
  f = L.pol

  Kx = parent(f)
  Fp, mF = ResidueField(OK, p)
  mmF = extend(mF, K)
  immF = inv(mmF)
  Fy, y = PolynomialRing(Fp,"y", cached=false)
  fmodp = Hecke.nf_elem_poly_to_fq_poly(Fy, mmF, f)
  fac = factor(fmodp)
  result = Array{Tuple{NfRelOrdIdl{nf_elem, NfOrdFracIdl}, Int}, 1}()
  for (q, e) in fac
    g = Hecke.fq_poly_to_nf_elem_poly(Kx, immF, q)
    P = ideal(O, L(1), g(a), frac_ideal(OK, p), ideal(OK, K(1)))
    P.is_prime = 1
    P.splitting_type = (e, degree(q))
    P.minimum = deepcopy(p)
    P.non_index_div_poly = q
    push!(result, (P, e))
  end
  return result
end

function prime_dec_index(O::NfRelOrd{nf_elem, NfOrdFracIdl}, p::NfOrdIdl)
  L = nf(O)
  K = base_ring(L)
  pbasisO = pseudo_basis(O, Val{false})
  pO = p*O

  Ipint = pradical(O, p, true)
  Oint = order(Ipint) # same as O but with integral coefficient ideals
  A, AtoOint = AlgAss(Oint, Ipint, p, true)
  AA = split(A)

  result = Vector{Tuple{NfRelOrdIdl{nf_elem, NfOrdFracIdl}, Int}}()
  m = PseudoMatrix(zero_matrix(K, 1, degree(O)))
  for (B, BtoA) in AA
    f = dim(B)
    idem = BtoA(B[1]) # Assumes that B == idem*A
    M = representation_mat(idem)
    ker = left_kernel(M)
    N = basis_pmat(Ipint)
    for i = 1:length(ker)
      b = elem_in_basis(AtoOint(A(ker[i])))
      for j = 1:degree(O)
        m.matrix[1, j] = b[j]
      end
      N = vcat(N, deepcopy(m))
    end
    N = sub(pseudo_hnf_full_rank_with_modulus(N, p, :lowerleft), rows(N) - degree(O) + 1:rows(N), 1:degree(O))
    for i = 1:degree(O)
      t = K(denominator(pbasisO[i][2]))
      for j = i:degree(O)
        N.matrix[j, i] = divexact(N.matrix[j, i], t)
      end
    end
    N = pseudo_hnf(N, :lowerleft, true)
    P = NfRelOrdIdl{nf_elem, NfOrdFracIdl}(O, N)
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

function mod(a::NfRelOrdElem{nf_elem}, I::NfRelOrdIdl{nf_elem, NfOrdFracIdl})
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
  O = order(A)
  Afrac = NfRelOrdFracIdl{T, S}(O, basis_pmat(A))
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

function minimum(A::NfRelOrdIdl{T, S}, copy::Type{Val{V}} = Val{true}) where {T, S, V}
  if A.is_prime != 1
    error("Not implemented yet.")
  end
  if copy == Val{true}
    return deepcopy(A.minimum)
  else
    return A.minimum
  end
end

################################################################################
#
#  Order modulo prime ideal
#
################################################################################

function ResidueField(O::NfRelOrd{T, S}, P::NfRelOrdIdl{T, S}) where {T, S}
  @assert order(P) == O
  @assert P.is_prime == 1
  mF = NfRelOrdToFqMor(O, P)
  return codomain(mF), mF
end
