export iscommutative, trred_matrix, any_order, pmaximal_overorder, phereditary_overorder, ismaximal

elem_type(::AlgAssRelOrd{S, T}) where {S, T} = AlgAssRelOrdElem{S, T}

elem_type(::Type{AlgAssRelOrd{S, T}}) where {S, T} = AlgAssRelOrdElem{S, T}

ideal_type(::AlgAssRelOrd{S, T}) where {S, T} = AlgAssRelOrdIdl{S, T}

ideal_type(::Type{AlgAssRelOrd{S, T}}) where {S, T} = AlgAssRelOrdIdl{S, T}

@doc Markdown.doc"""
    algebra(O::AlgAssRelOrd) -> AbsAlgAss

> Returns the algebra which contains $O$.
"""
algebra(O::AlgAssRelOrd) = O.algebra

_algebra(O::AlgAssRelOrd) = algebra(O)

@doc Markdown.doc"""
    base_ring(O::AlgAssRelOrd) -> Union{ NfAbsOrd, NfRelOrd }

> Returns an order $R$ in the base ring of `algebra(O)`, such that $O$ is an $R$-order.
"""
base_ring(O::AlgAssRelOrd) = order(basis_pmat(O, copy = false).coeffs[1])

@doc Markdown.doc"""
    iscommutative(O::AlgAssRelOrd) -> Bool

> Returns `true` if $O$ is a commutative ring and `false` otherwise.
"""
iscommutative(O::AlgAssRelOrd) = iscommutative(algebra(O))

################################################################################
#
#  Construction
#
################################################################################

@doc Markdown.doc"""
    Order(A::AbsAlgAss{<: NumFieldElem}, M::Generic.Mat{<: NumFieldElem})
      -> AlgAssRelOrd

> Returns the order of $A$ with basis matrix $M$.
"""
function Order(A::AbsAlgAss{S}, M::Generic.Mat{S}) where S <: NumFieldElem
  return AlgAssRelOrd{S, frac_ideal_type(order_type(base_ring(A)))}(A, deepcopy(M))
end

@doc Markdown.doc"""
    Order(A::AbsAlgAss{<: NumFieldElem}, M::PMat{<: NumFieldElem, T})
      -> AlgAssRelOrd

> Returns the order of $A$ with basis pseudo-matrix $M$.
"""
function Order(A::AbsAlgAss{S}, M::PMat{S, T}) where { S <: NumFieldElem, T }
  return AlgAssRelOrd{S, T}(A, deepcopy(M))
end

@doc Markdown.doc"""
    Order(A::AbsAlgAss{<: NumFieldElem}, B::Vector{<: AbsAlgAssElem{ <: NumFieldElem}})
      -> AlgAssRelOrd

> Returns the order of $A$ with basis $B$.
"""
function Order(A::AbsAlgAss{S}, B::Vector{ <: AbsAlgAssElem{S} }) where { S <: NumFieldElem }
  @assert length(B) == dim(A)
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  for i = 1:dim(A)
    elem_to_mat_row!(M, i, B[i])
  end
  return Order(A, M)
end
################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_basis_pmat(O::AlgAssRelOrd{S, T}) where {S, T}
  if isdefined(O, :basis_pmat)
    return nothing
  end
  if !isdefined(O, :pseudo_basis)
    error("No pseudo_basis and no basis_pmat defined.")
  end
  pb = pseudo_basis(O, copy = false)
  A = algebra(O)
  M = zero_matrix(base_ring(A), degree(O), degree(O))
  C = Vector{T}()
  for i = 1:degree(O)
    elem_to_mat_row!(M, i, pb[i][1])
    push!(C, deepcopy(pb[i][2]))
  end
  O.basis_pmat = PseudoMatrix(M, C)
  return nothing
end

function assure_has_pseudo_basis(O::AlgAssRelOrd{S, T}) where {S, T}
  if isdefined(O, :pseudo_basis)
    return nothing
  end
  if !isdefined(O, :basis_pmat)
    error("No pseudo_basis and no basis_pmat defined.")
  end
  P = basis_pmat(O, copy = false)
  A = algebra(O)
  pseudo_basis = Vector{Tuple{elem_type(A), T}}()
  for i = 1:degree(O)
    a = elem_from_mat_row(A, P.matrix, i)
    push!(pseudo_basis, (a, deepcopy(P.coeffs[i])))
  end
  O.pseudo_basis = pseudo_basis
  return nothing
end

function assure_has_basis_mat(O::AlgAssRelOrd)
  if isdefined(O, :basis_mat)
    return nothing
  end
  O.basis_mat = basis_pmat(O).matrix
  return nothing
end

function assure_has_basis_mat_inv(O::AlgAssRelOrd)
  if isdefined(O, :basis_mat_inv)
    return nothing
  end
  O.basis_mat_inv = inv(basis_mat(O, copy = false))
  return nothing
end

function assure_has_inv_coeff_ideals(O::AlgAssRelOrd)
  if isdefined(O, :inv_coeff_ideals)
    return nothing
  end
  pb = pseudo_basis(O, copy = false)
  O.inv_coeff_ideals = [ inv(pb[i][2]) for i in 1:degree(O) ]
  return nothing
end

################################################################################
#
#  Pseudo basis / basis pseudo-matrix
#
################################################################################

@doc Markdown.doc"""
    pseudo_basis(O::AlgAssRelOrd; copy::Bool = true)

> Returns the pseudo basis of $O$, i. e. a vector $v$ of pairs $(e_i, a_i)$ such
> that $O = \bigoplus_i a_i e_i$, where $e_i$ is an element of `algebra(O)`
> and $a_i$ a fractional ideal of `base_ring(O)`.
"""
function pseudo_basis(O::AlgAssRelOrd; copy::Bool = true)
  assure_has_pseudo_basis(O)
  if copy
    return deepcopy(O.pseudo_basis)
  else
    return O.pseudo_basis
  end
end

@doc Markdown.doc"""
    basis_pmat(O::AlgAssRelOrd; copy::Bool = true) -> PMat

> Returns the basis pseudo-matrix of $O$.
"""
function basis_pmat(O::AlgAssRelOrd; copy::Bool = true)
  assure_has_basis_pmat(O)
  if copy
    return deepcopy(O.basis_pmat)
  else
    return O.basis_pmat
  end
end

function inv_coeff_ideals(O::AlgAssRelOrd; copy::Bool = true)
  assure_has_inv_coeff_ideals(O)
  if copy
    return deepcopy(O.inv_coeff_ideals)
  else
    return O.inv_coeff_ideals
  end
end

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

@doc Markdown.doc"""
    basis_mat(O::AlgAssRelOrd; copy::Bool = true) -> MatElem

> Returns the basis matrix of $O$, that is the basis pseudo-matrix of $O$ without
> the coefficient ideals.
"""
function basis_mat(O::AlgAssRelOrd; copy::Bool = true)
  assure_has_basis_mat(O)
  if copy
    return deepcopy(O.basis_mat)
  else
    return O.basis_mat
  end
end

@doc Markdown.doc"""
    basis_mat_inv(O::AlgAssRelOrd; copy::Bool = true) -> MatElem

> Returns the inverse of the basis matrix of $O$.
"""
function basis_mat_inv(O::AlgAssRelOrd; copy::Bool = true)
  assure_has_basis_mat_inv(O)
  if copy
    return deepcopy(O.basis_mat_inv)
  else
    return O.basis_mat_inv
  end
end

################################################################################
#
#  Degree
#
################################################################################

@doc Markdown.doc"""
    degree(O::AlgAssRelOrd) -> Int

> Returns the dimension of the algebra containing $O$.
"""
function degree(O::AlgAssRelOrd)
  return dim(algebra(O))
end

################################################################################
#
#  Inclusion of algebra elements
#
################################################################################

function _check_elem_in_order(a::AbsAlgAssElem{S}, O::AlgAssRelOrd{S, T}, short::Type{Val{U}} = Val{false}) where {S, T, U}
  t = zero_matrix(base_ring(algebra(O)), 1, degree(O))
  elem_to_mat_row!(t, 1, a)
  t = t*basis_mat_inv(O, copy = false)
  b_pmat = basis_pmat(O, copy = false)
  if short == Val{true}
    for i = 1:degree(O)
      if !(t[1, i] in b_pmat.coeffs[i])
        return false
      end
    end
    return true
  else
    for i = 1:degree(O)
      if !(t[1, i] in b_pmat.coeffs[i])
        return false, Vector{S}()
      end
    end
    v = Vector{S}(undef, degree(O))
    for i = 1:degree(O)
      v[i] = deepcopy(t[1, i])
    end
    return true, v
  end
end

@doc Markdown.doc"""
    in(a::AbsAlgAssElem, O::AlgAssRelOrd) -> Bool

> Returns `true` if the algebra element $a$ is in $O$ and `false` otherwise.
"""
function in(a::AbsAlgAssElem{S}, O::AlgAssRelOrd{S, T}) where {S, T}
  return _check_elem_in_order(a, O, Val{true})
end

################################################################################
#
#  Denominator in an order
#
################################################################################

@doc Markdown.doc"""
    denominator(a::AbsAlgAssElem, O::AlgAssRelOrd) -> fmpz

> Returns $d\in \mathbb Z$ such that $d \cdot a \in O$.
"""
function denominator(a::AbsAlgAssElem, O::AlgAssRelOrd)
  t = zero_matrix(base_ring(algebra(O)), 1, degree(O))
  elem_to_mat_row!(t, 1, a)
  t = t*basis_mat_inv(O, copy = false)
  d = fmpz(1)
  inv_coeff = inv_coeff_ideals(O, copy = false)
  for i = 1:degree(O)
    tt = inv_coeff[i]*t[1, i]
    tt = simplify(tt)
    d = lcm(d, denominator(tt))
  end
  return d
end

################################################################################
#
#  Random elements
#
################################################################################

@doc Markdown.doc"""
    rand(O::AlgAssRelOrd, B::Int) -> AlgAssRelOrdElem

> Returns a random element of $O$ whose coefficient size is controlled by $B$.
"""
function rand(O::AlgAssRelOrd, B::Int)
  pb = pseudo_basis(O, copy = false)
  z = algebra(O)()
  for i = 1:degree(O)
    t = rand(pb[i][2], B)
    z += t*pb[i][1]
  end
  return O(z)
end

################################################################################
#
#  Print
#
################################################################################

function show(io::IO, O::AlgAssRelOrd)
  compact = get(io, :compact, false)
  if compact
    print(io, "Order of ")
    show(IOContext(io, :compact => true), algebra(O))
  else
    print(io, "Order of ")
    println(io, algebra(O))
    print(io, "with pseudo-basis ")
    pb = pseudo_basis(O, copy = false)
    for i = 1:degree(O)
      print(io, "\n(")
      show(IOContext(io, :compact => true), pb[i][1])
      print(io, ", ")
      show(IOContext(io, :compact => true), pb[i][2])
      print(io, ")")
    end
  end
end

################################################################################
#
#  Equality
#
################################################################################

@doc Markdown.doc"""
    ==(R::AlgAssRelOrd, S::AlgAssRelOrd) -> Bool

> Returns `true` if $R$ and $S$ are equal and `false` otherwise.
"""
function ==(R::AlgAssRelOrd, S::AlgAssRelOrd)
  algebra(R) != algebra(S) && return false
  return basis_pmat(R, copy = false) == basis_pmat(S, copy = false)
end

################################################################################
#
#  Discriminant and Reduced Trace Matrix
#
################################################################################

@doc Markdown.doc"""
    trred_matrix(O::AlgssRelOrd) -> MatElem

> Returns the reduced trace matrix $M$ of $O$, i. e. `M[i, j] = trred(b[i]*b[j])`,
> where $b$ is a basis of $O$.
"""
function trred_matrix(O::AlgAssRelOrd)
  if isdefined(O, :trred_matrix)
    return deepcopy(O.trred_matrix)
  end
  A = algebra(O)
  b = pseudo_basis(O, copy = false)
  d = dim(A)
  M = zero_matrix(base_ring(A), d, d)
  for i = 1:d
    t = trred(b[i][1]*b[i][1])
    M[i, i] = t
    for j = i + 1:d
      t = trred(b[i][1]*b[j][1])
      M[i, j] = t
      M[j, i] = t
    end
  end
  O.trred_matrix = M
  return deepcopy(M)
end

@doc Markdown.doc"""
    discriminant(O::AlgssRelOrd)

> Returns the discriminant of $O$.
"""
function discriminant(O::AlgAssRelOrd)
  if isdefined(O, :disc)
    return O.disc
  end
  d = det(trred_matrix(O))
  pb = pseudo_basis(O, copy = false)
  a = pb[1][2]^2
  for i = 2:degree(O)
    a *= pb[i][2]^2
  end
  disc = d*a
  simplify(disc)
  O.disc = numerator(disc)
  return deepcopy(O.disc)
end

################################################################################
#
#  Maximal Order
#
################################################################################

@doc Markdown.doc"""
    maximal_order(A::AbsAlgAss{ <: NumFieldElem }) -> AlgAssRelOrd

> Returns a maximal $R$-order of $A$ where $R$ is the maximal order of `base_ring(A)`.
"""
function maximal_order(A::AbsAlgAss{T}) where { T <: NumFieldElem }
  if isdefined(A, :maximal_order)
    return A.maximal_order
  end

  # So far ..._absolute is usually faster for linear, quadratic and cubic base fields,
  # but of course there are exceptions.
  # Feel free to adjust this if-condition.
  if base_field(base_ring(A)) == FlintQQ && degree(base_ring(A)) <= 3
    O = maximal_order_via_absolute(A)
  else
    O = maximal_order_via_relative(A)
  end
  A.maximal_order = O
  return O
end

function maximal_order_via_absolute(A::AbsAlgAss{T}) where { T <: NumFieldElem }
  B, BtoA = AlgAss(A)
  C, BtoC, CtoB = restrict_scalars(B, FlintQQ)
  OC = maximal_order(C)
  M = zero_matrix(base_ring(A), degree(OC), dim(A))
  for i = 1:degree(OC)
    elem_to_mat_row!(M, i, BtoA(CtoB(elem_in_algebra(basis(OC, copy = false)[i], copy = false))))
  end
  PM = sub(pseudo_hnf(PseudoMatrix(M), :lowerleft, true), (degree(OC) - dim(A) + 1):degree(OC), 1:dim(A))
  O = Order(A, PM)
  O.ismaximal = 1
  return O
end

function maximal_order_via_relative(A::AbsAlgAss{T}) where { T <: NumFieldElem }
  O = any_order(A)
  return maximal_order(O)
end

@doc Markdown.doc"""
    maximal_order(O::AlgAssRelOrd) -> AlgAssRelOrd

> Returns a maximal order of `algera(O)` containing $O$.
"""
function maximal_order(O::AlgAssRelOrd)
  A = algebra(O)

  d = discriminant(O)
  fac = factor(d)

  OO = O
  for (p, e) in fac
    if e == 1
      continue
    end
    OO += pmaximal_overorder(O, p)
  end
  OO.ismaximal = 1
  return OO
end

@doc Markdown.doc"""
    any_order(A::AbsAlgAss{ <: NumFieldElem }) -> AlgAssRelOrd

> Returns any $R$-order of $A$ where $R$ is the maximal order of `base_ring(A)`.
"""
function any_order(A::AbsAlgAss{T}) where { T <: NumFieldElem }
  K = base_ring(A)
  return any_order(A, maximal_order(K))
end

@doc Markdown.doc"""
    any_order(A::AbsAlgAss{ <: NumFieldElem}, R::Union{ NfAbsOrd, NfRelOrd })
      -> AlgAssRelOrd

> Returns any $R$-order of $A$.
"""
function any_order(A::AbsAlgAss{T}, R::Union{ NfAbsOrd, NfRelOrd }) where { T <: NumFieldElem }
  K = base_ring(A)
  d = _denominator_of_mult_table(A, R)

  M = vcat(zero_matrix(K, 1, dim(A)), d*identity_matrix(K, dim(A)))
  oneA = one(A)
  for i = 1:dim(A)
    M[1, i] = deepcopy(coeffs(oneA, copy = false)[i])
  end
  PM = PseudoMatrix(M)
  PM = pseudo_hnf(PM, :lowerleft, true)
  O = Order(A, sub(PM, 2:dim(A) + 1, 1:dim(A)))
  return O
end

function _denominator_of_mult_table(A::AbsAlgAss{T}, R::Union{ NfAbsOrd, NfRelOrd }) where { T <: NumFieldElem }
  l = denominator(multiplication_table(A, copy = false)[1, 1, 1], R)
  for i = 1:dim(A)
    for j = 1:dim(A)
      for k = 1:dim(A)
        l = lcm(l, denominator(multiplication_table(A, copy = false)[i, j, k], R))
      end
    end
  end
  return l
end

_denominator_of_mult_table(A::AlgGrp{T}, R::Union{ NfAbsOrd, NfRelOrd }) where { T <: NumFieldElem } = fmpz(1)

# Requires that O is maximal and A = K^(n\times n) for a number field K.
# Computes a maximal order of type
#  (  O    ...   O    a )
#  (  :          :    : )
#  (  O    ...   O    a )
#  (a^(-1) ... a^(-1) O )
# for an ideal a of O.
# See Bley, Johnston "Computing generators of free modules over orders in group
# algebras", Prop. 5.1.
function _simple_maximal_order(O::AlgAssRelOrd, with_trafo::Type{Val{T}} = Val{false}) where T
  A = algebra(O)
  @assert A isa AlgMat
  n = degree(A)
  K = coefficient_ring(A)

  # Build a matrix with the first rows of basis elements of O
  M = zero_matrix(K, dim(A), n)
  for i = 1:dim(A)
    for j = 1:n
      M[i, j] = deepcopy(matrix(pseudo_basis(O, copy = false)[i][1], copy = false)[1, j])
    end
  end
  PM = PseudoMatrix(M, deepcopy(basis_pmat(O, copy = false).coeffs))
  PM = pseudo_hnf(PM, :upperright)

  M = sub(PM.matrix, 1:n, 1:n)
  PM = PseudoMatrix(M, PM.coeffs[1:n])
  U = similar(PM.matrix, 0, 0)
  steinitz_form!(PM, U, false)

  a = PM.coeffs[end]
  if !isone(a.den)
    mul_row!(PM.matrix, nrows(PM.matrix), K(a.den))
  end

  # Compute M^(-1)*O*M
  M = PM.matrix
  iM = inv(M)
  N = zero_matrix(K, dim(A), dim(A))
  for i = 1:dim(A)
    elem_to_mat_row!(N, i, iM*pseudo_basis(O, copy = false)[i][1]*M)
  end

  PN = PseudoMatrix(N, deepcopy(basis_pmat(O, copy = false).coeffs))
  PN = pseudo_hnf(PN, :lowerleft)

  if with_trafo == Val{true}
    return Order(A, PN), A(M)
  else
    return Order(A, PN)
  end
end

@doc Markdown.doc"""
    ismaximal(O::AlgAssRelOrd) -> Bool

> Returns `true` if $O$ is a maximal order and `false` otherwise.
"""
function ismaximal(O::AlgAssRelOrd)
  if O.ismaximal == 1
    return true
  end
  if O.ismaximal == 2
    return false
  end

  A = algebra(O)
  d = discriminant(O)
  if isdefined(A, :maximal_order)
    if d == discriminant(maximal_order(A))
      O.ismaximal = 1
      return true
    else
      O.ismaximal = 2
      return false
    end
  end

  fac = factor(d)

  for (p, e) in fac
    if e == 1
      continue
    end

    d2 = discriminant(pmaximal_overorder(O, p))
    if d != d2
      O.ismaximal = 2
      return false
    end
  end
  O.ismaximal = 1
  return true
end

ismaximal_known(O::AlgAssRelOrd) = O.ismaximal != 0

################################################################################
#
#  p-hereditary / p-maximal overorders
#
################################################################################

# See Friedrichs: "Berechnung von Maximalordnungen über Dedekindringen", Algorithmus 4.12
@doc Markdown.doc"""
    phereditary_overorder(O::AlgAssRelOrd, p::Union{ NfAbsOrdIdl, NfRelOrdIdl })
      -> AlgAssRelOrd

> Returns an order $O'$ containing $O$ such that the localization $O'_p$ is
> hereditary where $p$ is a prime ideal of `base_ring(O)`.
"""
function phereditary_overorder(O::AlgAssRelOrd, p::Union{ NfAbsOrdIdl, NfRelOrdIdl }; return_pradical::Type{Val{T}} = Val{false}) where T
  d = discriminant(O)
  prad = pradical(O, p)
  OO = left_order(prad)
  dd = discriminant(OO)
  while d != dd
    d = dd
    prad = pradical(OO, p)
    OO = left_order(prad)
    dd = discriminant(OO)
  end
  if return_pradical == Val{true}
    return order(prad), prad
  else
    return OO
  end
end

# See Friedrichs: "Berechnung von Maximalordnungen über Dedekindringen", Algorithmus 3.16
function _pmaximal_overorder(O::AlgAssRelOrd, p::Union{ NfAbsOrdIdl, NfRelOrdIdl })
  return _pmaximal_overorder(O, pradical(O, p), p)
end

function _pmaximal_overorder(O::AlgAssRelOrd, prad::AlgAssRelOrdIdl, p::Union{ NfAbsOrdIdl, NfRelOrdIdl }; strict_containment::Bool = false)
  d = discriminant(O)
  primes = _prime_ideals_over(O, prad, p, strict_containment = strict_containment)
  for P in primes
    OO = left_order(P)
    dd = discriminant(OO)
    if d != dd
      return _pmaximal_overorder(OO, p)
    end
  end
  return O
end

@doc Markdown.doc"""
    pmaximal_overorder(O::AlgAssRelOrd, p::Union{ NfAbsOrdIdl, NfRelOrdIdl })
      -> AlgAssRelOrd

> Returns an order $O'$ containing $O$ such that the index $(O'':O')$ of any maximal
> order $O''$ containing $O$ is not divisible by $p$ where $p$ is a prime ideal
> of `base_ring(O)`.
"""
function pmaximal_overorder(O::AlgAssRelOrd, p::Union{ NfAbsOrdIdl, NfRelOrdIdl })
  O, prad = phereditary_overorder(O, p, return_pradical = Val{true})
  return _pmaximal_overorder(O, prad, p, strict_containment = true)
end

################################################################################
#
#  Addition
#
################################################################################

function +(a::AlgAssRelOrd{S, T}, b::AlgAssRelOrd{S, T}) where { S, T }
  @assert algebra(a) === algebra(b)
  aB = basis_pmat(a, copy = false)
  bB = basis_pmat(b, copy = false)
  d = degree(a)
  PM = sub(pseudo_hnf(vcat(aB, bB), :lowerleft, true), d + 1:2*d, 1:d)
  return Order(algebra(a), PM)
end

################################################################################
#
#  Units of quotients
#
################################################################################

# Computes a generating system of U in O, where U is a set of representatives of
# the image of the projection map \pi:O^\times -> (O/g*O)^\times.
# Assumes that O is a maximal order in Mat_{n\times n}(K).
# See Bley, Johnson: "Computing generators of free modules over orders in
# group algebras", section 6.
function enum_units(O::AlgAssRelOrd, g::NfAbsOrdIdl)
  A = algebra(O)
  @assert A isa AlgMat
  @assert degree(A)^2 == dim(A)

  n = degree(A)

  K = base_ring(A)
  OK = base_ring(O)
  L = _simple_maximal_order(O)
  a = deepcopy(basis_pmat(L, copy = false).coeffs[end - 1])
  ai = deepcopy(basis_pmat(L, copy = false).coeffs[n])

  gensOKg = Vector{elem_type(K)}()
  for b in basis(OK)
    bmod = mod(b, g)
    if iszero(bmod)
      continue
    end
    push!(gensOKg, elem_in_nf(bmod))
  end

  if isone(a)
    gensinvag = gensOKg
  else
    gensinvag = Vector{elem_type(K)}()
    aig = ai*g
    for b in basis(ai)
      bmod = mod(b, aig)
      if iszero(bmod)
        continue
      end
      push!(gensinvag, bmod)
    end
  end

  if isone(a)
    gensag = gensOKg
  else
    gensag = Vector{elem_type(K)}()
    ag = a*g
    for b in basis(a)
      bmod = mod(b, ag)
      if iszero(bmod)
        continue
      end
      push!(gensag, bmod)
    end
  end

  result = Vector{elem_type(L)}()
  n1 = n - 1
  # n \nmid i, j or n \mid i, j
  for i = 1:n1
    for j = 1:n1
      if j == i
        continue
      end
      for x in gensOKg
        E = identity_matrix(K, n)
        E[i, j] = deepcopy(x)
        push!(result, L(A(E)))
      end
    end
  end

  # n \nmid i and n \mid j
  for i = 1:n1
    for x in gensag
      E = identity_matrix(K, n)
      E[i, n] = deepcopy(x)
      push!(result, L(A(E)))
    end
  end

  # n \mid i and n \nmid j
  for j = 1:n1
    for x in gensinvag
      E = identity_matrix(K, n)
      E[n, j] = deepcopy(x)
      push!(result, L(A(E)))
    end
  end

  U, mU = unit_group(OK)
  for i = 1:ngens(U)
    x = elem_in_nf(mU(U[i]))
    E = identity_matrix(K, n)
    E[1, 1] = x
    push!(result, L(A(E)))
  end
  return result
end
