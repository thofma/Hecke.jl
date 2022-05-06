export iscommutative, trred_matrix, any_order, pmaximal_overorder, phereditary_overorder, ismaximal

elem_type(::AlgAssRelOrd{S, T, U}) where {S, T, U} = AlgAssRelOrdElem{S, T, U}

elem_type(::Type{AlgAssRelOrd{S, T, U}}) where {S, T, U} = AlgAssRelOrdElem{S, T, U}

ideal_type(::AlgAssRelOrd{S, T, U}) where {S, T, U} = AlgAssRelOrdIdl{S, T, U}

ideal_type(::Type{AlgAssRelOrd{S, T, U}}) where {S, T, U} = AlgAssRelOrdIdl{S, T, U}

@doc Markdown.doc"""
    algebra(O::AlgAssRelOrd) -> AbsAlgAss

Returns the algebra which contains $O$.
"""
algebra(O::AlgAssRelOrd) = O.algebra

_algebra(O::AlgAssRelOrd) = algebra(O)

@doc Markdown.doc"""
    base_ring(O::AlgAssRelOrd) -> Union{NfAbsOrd, NfRelOrd}

Returns an order $R$ in the base ring of the algebra of $O$, such that $O$ is an $R$-order.
"""
base_ring(O::AlgAssRelOrd) = order(basis_pmatrix(O, copy = false).coeffs[1])

@doc Markdown.doc"""
    iscommutative(O::AlgAssRelOrd) -> Bool

Returns `true` if $O$ is a commutative ring and `false` otherwise.
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

Returns the order of $A$ with basis matrix $M$.
"""
function Order(A::AbsAlgAss{S}, M::Generic.Mat{S}) where S <: NumFieldElem
  return AlgAssRelOrd{S, fractional_ideal_type(order_type(base_ring(A))), typeof(A)}(A, deepcopy(M))
end

@doc Markdown.doc"""
    Order(A::AbsAlgAss{<: NumFieldElem}, M::PMat{<: NumFieldElem, T})
      -> AlgAssRelOrd

Returns the order of $A$ with basis pseudo-matrix $M$.
"""
function Order(A::AbsAlgAss{S}, M::PMat{S, T}) where { S <: NumFieldElem, T }
  return AlgAssRelOrd{S, T, typeof(A)}(A, deepcopy(M))
end

@doc Markdown.doc"""
    Order(A::AbsAlgAss{<: NumFieldElem}, B::Vector{<: AbsAlgAssElem{ <: NumFieldElem}})
      -> AlgAssRelOrd

Returns the order of $A$ with basis $B$.
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

function assure_has_basis_pmatrix(O::AlgAssRelOrd{S, T, U}) where {S, T, U}
  if isdefined(O, :basis_pmatrix)
    return nothing
  end
  if !isdefined(O, :pseudo_basis)
    error("No pseudo_basis and no basis_pmatrix defined.")
  end
  pb = pseudo_basis(O, copy = false)
  A = algebra(O)
  M = zero_matrix(base_ring(A), degree(O), degree(O))
  C = Vector{T}()
  for i = 1:degree(O)
    elem_to_mat_row!(M, i, pb[i][1])
    push!(C, deepcopy(pb[i][2]))
  end
  O.basis_pmatrix = PseudoMatrix(M, C)
  return nothing
end

function assure_has_pseudo_basis(O::AlgAssRelOrd{S, T, U}) where {S, T, U}
  if isdefined(O, :pseudo_basis)
    return nothing
  end
  if !isdefined(O, :basis_pmatrix)
    error("No pseudo_basis and no basis_pmatrix defined.")
  end
  P = basis_pmatrix(O, copy = false)
  A = algebra(O)
  pseudo_basis = Vector{Tuple{elem_type(A), T}}()
  for i = 1:degree(O)
    a = elem_from_mat_row(A, P.matrix, i)
    push!(pseudo_basis, (a, deepcopy(P.coeffs[i])))
  end
  O.pseudo_basis = pseudo_basis
  return nothing
end

function assure_has_basis_matrix(O::AlgAssRelOrd)
  if isdefined(O, :basis_matrix)
    return nothing
  end
  O.basis_matrix = basis_pmatrix(O).matrix
  return nothing
end

function assure_has_basis_mat_inv(O::AlgAssRelOrd)
  if isdefined(O, :basis_mat_inv)
    return nothing
  end
  O.basis_mat_inv = inv(basis_matrix(O, copy = false))
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

Returns the pseudo basis of $O$, i. e. a vector $v$ of pairs $(e_i, a_i)$ such
that $O = \bigoplus_i a_i e_i$, where $e_i$ is an element of `algebra(O)`
and $a_i$ a fractional ideal of `base_ring(O)`.
"""
function pseudo_basis(O::AlgAssRelOrd{S, T, U}; copy::Bool = true) where {S, T, U}
  assure_has_pseudo_basis(O)
  if copy
    return deepcopy(O.pseudo_basis)::Vector{Tuple{elem_type(U), T}}
  else
    return O.pseudo_basis::Vector{Tuple{elem_type(U), T}}
  end
end

@doc Markdown.doc"""
    basis_pmatrix(O::AlgAssRelOrd; copy::Bool = true) -> PMat

Returns the basis pseudo-matrix of $O$.
"""
function basis_pmatrix(O::AlgAssRelOrd; copy::Bool = true)
  assure_has_basis_pmatrix(O)
  if copy
    return deepcopy(O.basis_pmatrix)
  else
    return O.basis_pmatrix
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

# Returns a basis of O as Z-module
function absolute_basis(O::AlgAssRelOrd)
  pb = pseudo_basis(O, copy = false)
  res = Vector{elem_type(O)}()
  for i = 1:degree(O)
    for b in absolute_basis(pb[i][2])
      push!(res, O(b*pb[i][1]))
    end
  end
  return res
end

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

@doc Markdown.doc"""
    basis_matrix(O::AlgAssRelOrd; copy::Bool = true) -> MatElem

Returns the basis matrix of $O$, that is the basis pseudo-matrix of $O$ without
the coefficient ideals.
"""
function basis_matrix(O::AlgAssRelOrd; copy::Bool = true)
  assure_has_basis_matrix(O)
  if copy
    return deepcopy(O.basis_matrix)
  else
    return O.basis_matrix
  end
end

@doc Markdown.doc"""
    basis_mat_inv(O::AlgAssRelOrd; copy::Bool = true) -> MatElem

Returns the inverse of the basis matrix of $O$.
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

Returns the dimension of the algebra containing $O$.
"""
function degree(O::AlgAssRelOrd)
  return dim(algebra(O))
end

################################################################################
#
#  Inclusion of algebra elements
#
################################################################################

function _check_elem_in_order(a::AbsAlgAssElem{S}, O::AlgAssRelOrd{S, T, V}, short::Type{Val{U}} = Val{false}) where {S, T, U, V}
  t = zero_matrix(base_ring(algebra(O)), 1, degree(O))
  elem_to_mat_row!(t, 1, a)
  t = t*basis_mat_inv(O, copy = false)
  b_pmat = basis_pmatrix(O, copy = false)
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

Returns `true` if the algebra element $a$ is in $O$ and `false` otherwise.
"""
function in(a::AbsAlgAssElem{S}, O::AlgAssRelOrd{S, T, U}) where {S, T, U}
  return _check_elem_in_order(a, O, Val{true})
end

################################################################################
#
#  Denominator in an order
#
################################################################################

@doc Markdown.doc"""
    denominator(a::AbsAlgAssElem, O::AlgAssRelOrd) -> fmpz

Returns $d\in \mathbb Z$ such that $d \cdot a \in O$.
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

Returns a random element of $O$ whose coefficient size is controlled by $B$.
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

Returns `true` if $R$ and $S$ are equal and `false` otherwise.
"""
function ==(R::AlgAssRelOrd, S::AlgAssRelOrd)
  algebra(R) != algebra(S) && return false
  return basis_pmatrix(R, copy = false) == basis_pmatrix(S, copy = false)
end

################################################################################
#
#  Discriminant and Reduced Trace Matrix
#
################################################################################

@doc Markdown.doc"""
    trred_matrix(O::AlgssRelOrd) -> MatElem

Returns the reduced trace matrix $M$ of $O$, i. e. `M[i, j] = trred(b[i]*b[j])`,
where $b$ is a basis of $O$.
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

Returns the discriminant of $O$.
"""
function discriminant(O::AlgAssRelOrd{S, T, U}) where {S, T, U}
  if isdefined(O, :disc)
    return O.disc::ideal_type(order_type(parent_type(S)))
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
  return deepcopy(O.disc)::ideal_type(order_type(parent_type(S)))
end

################################################################################
#
#  Maximal Order
#
################################################################################

function ismaximal_order_known(A::AbsAlgAss{T}) where { T <: NumFieldElem }
  return isdefined(A, :maximal_order)
end

@doc Markdown.doc"""
    maximal_order(A::AbsAlgAss{ <: NumFieldElem }) -> AlgAssRelOrd

Returns a maximal $R$-order of $A$ where $R$ is the maximal order of the base ring of $A$.
"""
function maximal_order(A::AbsAlgAss{T}) where { T <: NumFieldElem }
  if isdefined(A, :maximal_order)
    return A.maximal_order::order_type(A)
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
  return O::order_type(A)
end

function maximal_order_via_absolute(A::AbsAlgAss{T}) where { T <: NumFieldElem }
  B, BtoA = AlgAss(A)
  C, CtoB = restrict_scalars(B, FlintQQ)
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

Returns a maximal order of the algebra of $O$ containing itself.
"""
function maximal_order(O::AlgAssRelOrd{S, T, U}) where {S, T, U}
  A = algebra(O)

  if isdefined(A, :maximal_order)
    # Check whether O \subseteq OO
    OO = A.maximal_order::AlgAssRelOrd{S, T, U}
    if _spans_subset_of_pseudohnf(basis_pmatrix(O, copy = false), basis_pmatrix(OO, copy = false), :lowerleft)
      return OO
    end
  end

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

  if !isdefined(A, :maximal_order)
    A.maximal_order = OO
  end
  return OO::AlgAssRelOrd{S, T, U}
end

@doc Markdown.doc"""
    any_order(A::AbsAlgAss{ <: NumFieldElem }) -> AlgAssRelOrd

Returns any $R$-order of $A$ where $R$ is the maximal order of the base ring of $A$.
"""
function any_order(A::AbsAlgAss{T}) where { T <: NumFieldElem }
  K = base_ring(A)
  return any_order(A, maximal_order(K))
end

@doc Markdown.doc"""
    any_order(A::AbsAlgAss{ <: NumFieldElem}, R::Union{ NfAbsOrd, NfRelOrd })
      -> AlgAssRelOrd

Returns any $R$-order of $A$.
"""
function any_order(A::AbsAlgAss{T}, R::Union{ NfAbsOrd, NfRelOrd }) where { T <: NumFieldElem }
  K = base_ring(A)
  d = _denominator_of_mult_table(A, R)

  M = vcat(zero_matrix(K, 1, dim(A)), d*identity_matrix(K, dim(A)))
  oneA = one(A)
  for i = 1:dim(A)
    M[1, i] = deepcopy(coefficients(oneA, copy = false)[i])
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

# TODO: This is type unstable
# Requires that O is maximal and A = K^(n\times n) for a number field K.
# Computes a maximal order of type
#  (  O    ...   O  a^-1 )
#  (  :          :  :    )
#  (  O    ...   O  a^-1 )
#  (  a    ...   a  O    )
# for an ideal a of O.
# See Bley, Johnston "Computing generators of free modules over orders in group
# algebras", Prop. 5.1.
function _simple_maximal_order(O::AlgAssRelOrd, make_free::Bool = true, with_trafo::Type{Val{T}} = Val{false}) where T
  A = algebra(O)
  @assert A isa AlgMat
  n = degree(A)
  K = coefficient_ring(A)

  # Build a matrix with the first columns of basis elements of O
  M = zero_matrix(K, dim(A), n)
  for i = 1:dim(A)
    b = matrix(pseudo_basis(O, copy = false)[i][1], copy = false)
    for j = 1:n
      M[i, j] = deepcopy(b[j, 1])
    end
  end
  PM = PseudoMatrix(M, [pseudo_basis(O, copy = false)[i][2] for i in 1:dim(A)])
  PM = pseudo_hnf(PM, :upperright)


  M = sub(PM.matrix, 1:n, 1:n)
  PM = PseudoMatrix(M, PM.coeffs[1:n])
  U = similar(PM.matrix, 0, 0)
  steinitz_form!(PM, U, false)

  a = PM.coeffs[end]
  a = simplify(a)
  fl = false

  if make_free
    fl, beta = isprincipal(a)
  end

  if fl
    mul_row!(PM.matrix, nrows(PM.matrix), beta)
    a = K(1) * base_ring(PM)
  else
    d = denominator(a)
    if !isone(d)
      mul_row!(PM.matrix, nrows(PM.matrix), K(1//d))
    end
    a = a * d
  end

  M = transpose(PM.matrix)
  iM = inv(M)
  N = zero_matrix(K, dim(A), dim(A))
  for i = 1:dim(A)
    elem_to_mat_row!(N, i, iM*pseudo_basis(O, copy = false)[i][1]*M)
  end

  PN = PseudoMatrix(N, deepcopy(basis_pmatrix(O, copy = false).coeffs))
  PN = pseudo_hnf(PN, :lowerleft)

  niceorder = Order(A, PN)
  niceorder.isnice = true
  niceorder.nice_order_ideal = a

  if with_trafo == Val{true}
    return niceorder, A(iM)
  else
    return niceorder
  end
end

@doc Markdown.doc"""
    nice_order(O::AlgAssRelOrd) -> AlgAssRelOrd, AlgElem

Given a maximal order $O$ in a full matrix algebra over a number field, return a
nice maximal order $R$ and element $a$ such that $a O a^-1 = R$.
"""
function nice_order(O::AlgAssRelOrd{S, T, U}; cached::Bool = true) where {S, T, U}
  if cached && isdefined(O, :nice_order)
    return O.nice_order::Tuple{typeof(O), elem_type(U)}
  else
    sO, A = _simple_maximal_order(O, true, Val{true})
    if cached
      O.nice_order = sO, A
    end
    return sO::typeof(O), A::elem_type(U)
  end
end

function nice_order_ideal(O::AlgAssRelOrd)
  !O.isnice && error("Order must be nice")
  return O.nice_order_ideal
end

@doc Markdown.doc"""
    ismaximal(O::AlgAssRelOrd) -> Bool

Returns `true` if $O$ is a maximal order and `false` otherwise.
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

Returns an order $O'$ containing $O$ such that the localization $O'_p$ is
hereditary where $p$ is a prime ideal of the base ring of $O$.
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
    if valuation(dd, p) < 2
      break
    end
  end
  if return_pradical == Val{true}
    return OO, prad
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
    if valuation(dd, p) < 2
      return OO
    end
    if d != dd
      return _pmaximal_overorder(OO, p)
    end
  end
  return O
end

@doc Markdown.doc"""
    pmaximal_overorder(O::AlgAssRelOrd, p::Union{ NfAbsOrdIdl, NfRelOrdIdl })
      -> AlgAssRelOrd

Returns an order $O'$ containing $O$ such that the index $(O'':O')$ of any maximal
order $O''$ containing $O$ is not divisible by $p$ where $p$ is a prime ideal
of the base ring of $O$.
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

function +(a::AlgAssRelOrd{S, T, U}, b::AlgAssRelOrd{S, T, U}) where { S, T, U}
  @assert algebra(a) === algebra(b)
  aB = basis_pmatrix(a, copy = false)
  bB = basis_pmatrix(b, copy = false)
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
  a = deepcopy(basis_pmatrix(L, copy = false).coeffs[end - 1])
  ai = deepcopy(basis_pmatrix(L, copy = false).coeffs[n])

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

################################################################################
#
#  Ramifying primes
#
################################################################################

# Returns a vector of tuples (p, m, k) where p is prime ideal at which the
# algebra ramifies, m its local index (Schur index) and k its local capacity.
# See Reiner: "Maximal order" Theorem 32.1
function ramified_prime_ideals(O::AlgAssRelOrd)
  A = algebra(O)
  @assert issimple(A)
  n2 = dim(A)
  n = isqrt(n2)
  @assert n^2 == n2

  d = discriminant(O)
  facd = factor(d)
  result = Vector{Tuple{ideal_type(base_ring(O)), Int, Int}}()
  for (p, e) in facd
    k = divexact(n2 - e, n)
    m = divexact(n, k)
    push!(result, (p, m, k))
    @assert m*k == n
  end

  return result
end

################################################################################
#
#  "All" maximal orders
#
################################################################################

# Returns a vector containing a system of representatives of the maximal orders
# of A with respect to conjugation, that is, any maximal order of A is conjugated
# to one of them and no two returned orders are conjugated.
# Only works for algebras fulfilling the Eichler condition.
representatives_of_maximal_orders(A::AlgAss{nf_elem}) = representatives_of_maximal_orders(maximal_order(A))

function representatives_of_maximal_orders(O::AlgAssRelOrd)
  A = algebra(O)
  @assert issimple(A)
  @assert iseichler(A)
  @assert ismaximal(O)
  K = base_ring(A)
  OK = base_ring(O)
  n2 = dim(A)
  n = isqrt(n2)
  @assert n^2 == n2

  inf_plc = ramified_infinite_places(A)

  R, mR = ray_class_group(OK(1)*OK, inf_plc)
  S, mS = snf(R)
  if order(S) == 1
    return [ O ]
  end

  ram_primes = ramified_prime_ideals(O)

  U = Vector{elem_type(S)}()
  for i = 1:ngens(S)
    push!(U, n*S[i])
  end
  for (p, m, k) in ram_primes
    push!(U, k*(mS\(mR\p)))
  end

  SU, mSU = quo(S, U)
  if order(SU) == 1
    return [ O ]
  end

  # Each element of SU corresponds now to a maximal order.
  # We have to find a prime ideal in each of these classes.
  reps_found = Set{elem_type(SU)}()
  primes = Vector{ideal_type(OK)}()
  push!(reps_found, id(SU))
  P = PrimeIdealsSet(OK, 1, -1, indexdivisors = false, ramified = false)
  for p in P
    g = mSU(mS\(mR\p))
    if g in reps_found
      continue
    end

    push!(reps_found, g)
    push!(primes, p)

    if length(reps_found) == order(SU)
      break
    end
  end

  # For each of the prime ideals compute a maximal ideal with left order O.
  # Then the right orders of these form a system of representatives.
  max_ideals = Vector{ideal_type(O)}()
  for i = 1:length(primes)
    push!(max_ideals, maximal_integral_ideal(O, primes[i], :left))
  end

  result = Vector{typeof(O)}()
  push!(result, O)
  for i = 1:length(max_ideals)
    push!(result, right_order(max_ideals[i]))
  end

  return result
end


