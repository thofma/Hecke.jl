export pseudo_basis, basis_pmatrix

add_verbose_scope(:NfRelOrd)


################################################################################
#
#  Basic field access
#
################################################################################

@doc Markdown.doc"""
      nf(O::NfRelOrd) -> NumField

Returns the ambient number field of $\mathcal O$.
"""
nf(O::NfRelOrd) = O.nf

_algebra(O::NfRelOrd) = nf(O)

@doc Markdown.doc"""
    parent(O::NfRelOrd) -> NfRelOrdSet

Returns the parent of $\mathcal O$, that is, the set of orders of the ambient
number field.
"""
parent(O::NfRelOrd) = O.parent

base_ring(O::NfRelOrd) = order(pseudo_basis(O, copy = false)[1][2])

@doc Markdown.doc"""
    isequation_order(O::NfRelOrd) -> Bool

Returns whether $\mathcal O$ is the equation order of the ambient number
field.
"""
isequation_order(O::NfRelOrd) = O.isequation_order

ismaximal_known(O::NfRelOrd) = O.ismaximal != 0

ismaximal_known_and_maximal(O::NfRelOrd) = O.ismaximal == 1

function ismaximal(O::NfRelOrd)
  if ismaximal_known(O)
    return ismaximal_known_and_maximal(O)
  end
  OK = maximal_order(O)
  if discriminant(OK) == discriminant(O)
    O.ismaximal = 1
    return true
  else
    O.ismaximal = 2
    return false
  end
end

issimple(O::NfRelOrd) = issimple(nf(O))

iscommutative(O::NfRelOrd) = true

elem_type(::NfRelOrd{T, S}) where {T, S} = NfRelOrdElem{T}

elem_type(::Type{NfRelOrd{T, S}}) where {T, S} = NfRelOrdElem{T}

ideal_type(::NfRelOrd{T, S}) where {T, S} = NfRelOrdIdl{T, S}

ideal_type(::Type{NfRelOrd{T, S}}) where {T, S} = NfRelOrdIdl{T, S}

fractional_ideal_type(::NfRelOrd{T, S}) where {T, S} = NfRelOrdFracIdl{T, S}

fractional_ideal_type(::Type{NfRelOrd{T, S}}) where {T, S} = NfRelOrdFracIdl{T, S}

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_basis_pmatrix(O::NfRelOrd{T, S}) where {T, S}
  if isdefined(O, :basis_pmatrix)
    return nothing
  end
  if !isdefined(O, :pseudo_basis)
    error("No pseudo_basis and no basis_pmatrix defined.")
  end
  pb = pseudo_basis(O, copy = false)
  L = nf(O)
  M = zero_matrix(base_field(L), degree(O), degree(O))
  C = Vector{S}()
  for i = 1:degree(O)
    elem_to_mat_row!(M, i, pb[i][1])
    push!(C, deepcopy(pb[i][2]))
  end
  O.basis_pmatrix = PseudoMatrix(M, C)
  return nothing
end

function assure_has_pseudo_basis(O::NfRelOrd{T, S}) where {T, S}
  if isdefined(O, :pseudo_basis)
    return nothing
  end
  if !isdefined(O, :basis_pmatrix)
    error("No pseudo_basis and no basis_pmatrix defined.")
  end
  P = basis_pmatrix(O, copy = false)
  L = nf(O)
  pseudo_basis = Vector{Tuple{elem_type(L), S}}()
  for i = 1:degree(O)
    a = elem_from_mat_row(L, P.matrix, i)
    push!(pseudo_basis, (a, deepcopy(P.coeffs[i])))
  end
  O.pseudo_basis = pseudo_basis
  return nothing
end

function assure_has_basis_nf(O::NfRelOrd{T, S}) where {T, S}
  if isdefined(O, :basis_nf)
    return nothing
  end
  L = nf(O)
  pb = pseudo_basis(O)
  basis_nf = Vector{elem_type(L)}()
  for i = 1:degree(O)
    push!(basis_nf, pb[i][1])
  end
  O.basis_nf = basis_nf
  return nothing
end

function assure_has_basis_matrix(O::NfRelOrd)
  if isdefined(O, :basis_matrix)
    return nothing
  end
  O.basis_matrix = basis_pmatrix(O).matrix
  return nothing
end

function assure_has_basis_mat_inv(O::NfRelOrd)
  if isdefined(O, :basis_mat_inv)
    return nothing
  end
  O.basis_mat_inv = inv(basis_matrix(O, copy = false))
  return nothing
end

function assure_has_inv_coeff_ideals(O::NfRelOrd)
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
      pseudo_basis(O::NfRelOrd{T, S}) -> Vector{Tuple{NumFieldElem{T}{T}, S}}

Returns the pseudo-basis of $\mathcal O$.
"""
function pseudo_basis(O::NfRelOrd; copy::Bool = true)
  assure_has_pseudo_basis(O)
  if copy
    return deepcopy(O.pseudo_basis)
  else
    return O.pseudo_basis
  end
end

@doc Markdown.doc"""
      basis_pmatrix(O::NfRelOrd) -> PMat

Returns the basis pseudo-matrix of $\mathcal O$ with respect to the power basis
of the ambient number field.
"""
function basis_pmatrix(O::NfRelOrd; copy::Bool = true)
  assure_has_basis_pmatrix(O)
  if copy
    return deepcopy(O.basis_pmatrix)
  else
    return O.basis_pmatrix
  end
end

@doc Markdown.doc"""
      inv_coeff_ideals(O::NfRelOrd{T, S}) -> Vector{S}

Returns the inverses of the coefficient ideals of the pseudo basis of $O$.
"""
function inv_coeff_ideals(O::NfRelOrd; copy::Bool = true)
  assure_has_inv_coeff_ideals(O)
  if copy
    return deepcopy(O.inv_coeff_ideals)
  else
    return O.inv_coeff_ideals
  end
end

################################################################################
#
#  Basis / (inverse) basis matrix
#
################################################################################

@doc Markdown.doc"""
      basis_nf(O::NfRelOrd) -> Array{NumFieldElem, 1}

Returns the elements of the pseudo-basis of $\mathcal O$ as elements of the
ambient number field.
"""
function basis_nf(O::NfRelOrd; copy::Bool = true)
  assure_has_basis_nf(O)
  if copy
    return deepcopy(O.basis_nf)
  else
    return O.basis_nf
  end
end

@doc Markdown.doc"""
      basis_matrix(O::NfRelOrd{T, S}) -> Generic.Mat{T}

Returns the basis matrix of $\mathcal O$ with respect to the power basis
of the ambient number field.
"""
function basis_matrix(O::NfRelOrd; copy::Bool = true)
  assure_has_basis_matrix(O)
  if copy
    return deepcopy(O.basis_matrix)
  else
    return O.basis_matrix
  end
end

@doc Markdown.doc"""
      basis_mat_inv(O::NfRelOrd{T, S}) -> Generic.Mat{T}

Returns the inverse of the basis matrix of $\mathcal O$.
"""
function basis_mat_inv(O::NfRelOrd; copy::Bool = true)
  assure_has_basis_mat_inv(O)
  if copy
    return deepcopy(O.basis_mat_inv)
  else
    return O.basis_mat_inv
  end
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, S::NfRelOrdSet)
  print(io, "Set of orders of the number field ")
  print(io, S.nf)
end

function show(io::IO, O::NfRelOrd)
  compact = get(io, :compact, false)
  if compact
    if ismaximal_known_and_maximal(O) 
      print(io, "Relative maximal order with pseudo-basis ")
    else
      print(io, "Relative order with pseudo-basis ")
    end
    pb = pseudo_basis(O, copy = false)
    for i = 1:degree(O)
      print(io, "($(pb[i][1])) * ")
      show(IOContext(io, :compact => true), pb[i][2])
      if i != degree(O)
        print(io, ", ")
      end
    end
  else
    if ismaximal_known_and_maximal(O)
      print(io, "Relative maximal order of ")
    else
      print(io, "Relative order of ")
    end
    println(io, nf(O))
    print(io, "with pseudo-basis ")
    pb = pseudo_basis(O, copy = false)
    for i = 1:degree(O)
      print(io, "\n(")
      print(io, pb[i][1])
      print(io, ", ")
      show(IOContext(io, :compact => true), pb[i][2])
      print(io, ")")
    end
  end
end

################################################################################
#
#  Discriminant
#
################################################################################

function assure_has_discriminant(O::NfRelOrd{nf_elem, NfOrdFracIdl})
  if isdefined(O, :disc_abs)
    return nothing
  end
  if isequation_order(O)
    K = nf(O)
    F = base_field(K)
    OF = maximal_order(F)
    d = OF(discriminant(K.pol))
    O.disc_abs = ideal(OF, d)
    return nothing
  end
  d = det(trace_matrix(O, copy = false))
  pb = pseudo_basis(O, copy = false)
  a = pb[1][2]^2
  for i = 2:degree(O)
    a *= pb[i][2]^2
  end
  disc = d*a
  simplify(disc)
  O.disc_abs = numerator(disc)
  return nothing
end


function assure_has_discriminant(O::NfRelOrd{T, S}) where {T, S}
  if isdefined(O, :disc_rel)
    return nothing
  end
  d = det(trace_matrix(O, copy = false))
  pb = pseudo_basis(O, copy = false)
  a = pb[1][2]^2
  for i = 2:degree(O)
    a *= pb[i][2]^2
  end
  disc = d*a
  simplify(disc)
  O.disc_rel = numerator(disc)
  return nothing
end

function discriminant(O::NfRelOrd{nf_elem, S}) where S
  assure_has_discriminant(O)
  return deepcopy(O.disc_abs)
end

function discriminant(O::NfRelOrd{T, S}) where {T <: NumFieldElem{U} where U, S}
  assure_has_discriminant(O)
  return deepcopy(O.disc_rel)
end

################################################################################
#
#  Codifferent
#
################################################################################

@doc Markdown.doc"""
    codifferent(O::NfRelOrd) -> NfRelOrdFracIdl

Returns the codifferent of $\mathcal O$.
"""
function codifferent(O::NfRelOrd)
  T = trace_matrix(O, copy = false)
  R = base_ring(O)
  K = nf(R)
  pm = pseudo_matrix(inv(change_base_ring(K, T)))
  return fractional_ideal(O, pm)
end

@doc Markdown.doc"""
    different(O::NfRelOrd) -> NfRelOrdIdl

Returns the different of $\mathcal O$.
"""
function different(O::NfRelOrd)
  if !ismaximal_known_and_maximal(O)
    throw(error("Order not known to be maximal"))
  end
  return ideal(O, basis_pmatrix(inv(codifferent(O))))
end

################################################################################
#
#  Degree
#
################################################################################

@doc Markdown.doc"""
    degree(O::NfRelOrd) -> Int

Returns the degree of $\mathcal O$.
"""
degree(O::NfRelOrd) = degree(nf(O))

################################################################################
#
#  Deepcopy
#
################################################################################

@doc Markdown.doc"""
      deepcopy(O::NfRelOrd) -> NfRelOrd

Makes a copy of $\mathcal O$.
"""
function Base.deepcopy_internal(O::NfRelOrd{T, S}, dict::IdDict) where {T, S}
  z = NfRelOrd{T, S}(O.nf)
  for x in fieldnames(typeof(O))
    if x != :nf && x != :parent && isdefined(O, x)
      setfield!(z, x, Base.deepcopy_internal(getfield(O, x), dict))
    end
  end
  z.nf = O.nf
  z.parent = O.parent
  return z
end

################################################################################
#
#  Inclusion of number field elements
#
################################################################################

function _check_elem_in_order(a::NumFieldElem{T}, O::NfRelOrd{T, S}, short::Type{Val{V}} = Val{false}) where {T, S, V}
  b_pmat = basis_pmatrix(O, copy = false)
  t = zero_matrix(base_field(nf(O)), 1, degree(O))
  elem_to_mat_row!(t, 1, a)
  t = t*basis_mat_inv(O, copy = false)
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
        return false, Vector{T}()
      end
    end
    v = Vector{T}(undef, degree(O))
    for i in 1:degree(O)
      v[i] = deepcopy(t[1, i])
    end
    return true, v
  end
end

@doc Markdown.doc"""
      in(a::NumFieldElem, O::NfRelOrd) -> Bool

Checks whether $a$ lies in $\mathcal O$.
"""
function in(a::NumFieldElem{T}, O::NfRelOrd{T, S}) where {T, S}
  return _check_elem_in_order(a, O, Val{true})
end

################################################################################
#
#  Construction
#
################################################################################

@doc Markdown.doc"""
      Order(K::NumField{T}, M::Generic.Mat{T}) -> NfRelOrd

Returns the order which has basis matrix $M$ with respect to the power basis
of $K$.
"""
function Order(L::NumField{nf_elem}, M::Generic.Mat{nf_elem})
  # checks
  return NfRelOrd{nf_elem, NfOrdFracIdl}(L, deepcopy(M))
end

function Order(L::NumField{S}, M::Generic.Mat{S}) where S <: NumFieldElem{T} where T
  # checks
  return NfRelOrd{elem_type(base_field(L)), NfRelOrdFracIdl{T}}(L, deepcopy(M))
end

@doc Markdown.doc"""
      Order(K::NumField, M::PMat) -> NfRelOrd

Returns the order which has basis pseudo-matrix $M$ with respect to the power basis
of $K$.
"""
function Order(L::NumField{T}, M::PMat{T, S}) where {T, S}
  # checks
  return NfRelOrd{T, S}(L, deepcopy(M))
end

@doc Markdown.doc"""
      EquationOrder(L::NumField) -> NfRelOrd
      equation_order(L::NumField) -> NfRelOrd

Returns the equation order of the number field $L$.
"""
function EquationOrder(L::NumField)
  M = identity_matrix(base_field(L), degree(L))
  PM = PseudoMatrix(M)
  O = Order(L, PM)
  O.basis_mat_inv = M
  O.isequation_order = true
  return O
end

equation_order(L::NumField) = EquationOrder(L)

@doc Markdown.doc"""
      maximal_order(L::NumField) -> NfRelOrd

Returns the maximal order of $L$.
"""
function MaximalOrder(L::NumField)
  try
    O = _get_maximal_order_of_nf_rel(L)
    return O
  catch e
    if !isa(e, AccessorNotSetError)
      rethrow(e)
    end
    O = MaximalOrder(EquationOrder(L))
    _set_maximal_order_of_nf_rel(L, O)
    return O
  end
end

function maximal_order_via_absolute(L::NfRel)
  Labs, lToLabs, kToLabs = absolute_field(L)
  Oabs = maximal_order(Labs)
  return relative_order(Oabs, lToLabs)
end

function maximal_order_via_absolute(m::NfToNfRel)
  Oabs = maximal_order(domain(m))
  return relative_order(Oabs, m)
end

function maximal_order_via_simple(L::NfRelNS)
  Ls, m = simple_extension(L)
  Os = maximal_order(Ls)
  return non_simple_order(Os, m)
end

function maximal_order_via_simple(m::NfRelToNfRelNSMor)
  Os = maximal_order(domain(m))
  return non_simple_order(Os, m)
end

function maximal_order_via_relative(K::AnticNumberField, m::NfToNfRel)
  try
    O = _get_maximal_order(K)
    return O
  catch e
    if !isa(e, AccessorNotSetError)
      rethrow(e)
    end
    L = codomain(m)
    OL = maximal_order(L)
    B = absolute_basis(OL)
    OK = Order(K, [ m\b for b in B ], check = false, isbasis = true)
    OK.ismaximal = 1
    _set_maximal_order(K, OK)
    return OK
  end
end

################################################################################
#
#  Equality
#
################################################################################

function ==(R::NfRelOrd, S::NfRelOrd)
  nf(R) != nf(S) && return false
  return basis_pmatrix(R, copy = false) == basis_pmatrix(S, copy = false)
end

################################################################################
#
#  Trace matrix
#
################################################################################

@doc Markdown.doc"""
    trace_matrix(O::NfRelOrd{T, S}) -> Generic.Mat{T}

Returns the trace matrix of $\mathcal O$ with respect to $(\omega_1,\dotsc,\omega_d)$
where $(\mathfrak c_i, \omega_i)$ is the pseudo-basis of $\mathcal O$.
"""
function trace_matrix(O::NfRelOrd; copy::Bool = true)
  if isdefined(O, :trace_mat)
    if copy
      return deepcopy(O.trace_mat)
    else
      return O.trace_mat
    end
  end
  L = nf(O)
  K = base_field(L)
  b = basis_nf(O, copy = false)
  d = degree(L)
  g = zero_matrix(K, d, d)
  for i = 1:d
    t = tr(b[i]*b[i])
    g[i, i] = t
    for j = (i + 1):d
      t = tr(b[i]*b[j])
      g[i, j] = t
      g[j, i] = t
    end
  end
  O.trace_mat = g    
  if copy
    return deepcopy(O.trace_mat)
  else
    return O.trace_mat
  end
end

################################################################################
#
#  Dedekind criterion
#
################################################################################

function fq_nmod_poly_to_nf_elem_poly(R::Generic.PolyRing{nf_elem}, m::InverseMap, f::fq_nmod_poly)
  @assert codomain(m) == base_ring(R)
  @assert domain(m) == base_ring(parent(f))

  g = zero(R)
  for i = 0:degree(f)
    setcoeff!(g, i, m(coeff(f, i)))
  end
  return g
end

function fq_poly_to_nf_elem_poly(R::Generic.PolyRing{T}, m::InverseMap, f::fq_poly) where {T <: Union{nf_elem, NfRelElem}}
  return map_coeffs(m, f, parent = R)
end

# Algorithm IV.6. in "Berechnung relativer Ganzheitsbasen mit dem
# Round-2-Algorithmus" by C. Friedrichs.
function dedekind_test(O::NfRelOrd, p::Union{NfOrdIdl, NfRelOrdIdl}, compute_order::Type{Val{S}} = Val{true}) where S
  !isequation_order(O) && error("Order must be an equation order")
  !issimple(O) && error("Not implemented for non-simple extensions")

  L = nf(O)
  K = base_field(L)
  T = L.pol
  Kx = parent(T)
  OK = maximal_order(K)
  F, mF = ResidueField(OK, p)
  mmF = extend(mF, K)
  immF = pseudo_inv(mmF)
  Fy, y = PolynomialRing(F,"y", cached=false)

  Tmodp = map_coeffs(mmF, T, parent = Fy)
  fac = factor(Tmodp)
  g = Kx(1)
  for (t, e) in fac
    mul!(g, g, fq_poly_to_nf_elem_poly(Kx, immF, t))
  end
  gmodp = map_coeffs(mmF, g, parent = Fy)
  hmodp = divexact(Tmodp, gmodp)
  h = fq_poly_to_nf_elem_poly(Kx, immF, hmodp)
  a = anti_uniformizer(p)
  f = a*(g*h - T)
  fmodp = map_coeffs(mmF, f, parent = Fy)

  d = gcd(fmodp, gcd(gmodp, hmodp))

  if compute_order == Val{false}
    return isone(d)
  else
    if isone(d)
      return true, O
    end

    Umodp = divexact(Tmodp, d)
    U = fq_poly_to_nf_elem_poly(Kx, immF, Umodp)
    PM = PseudoMatrix(representation_matrix(a*U(gen(L))), [ K(1)*OK for i = 1:degree(O) ])
    PN = vcat(basis_pmatrix(O), PM)
    PN = sub(pseudo_hnf(PN, :lowerleft, true), degree(O) + 1:2*degree(O), 1:degree(O))
    OO = Order(L, PN)
    OO.isequation_order = false
    return false, OO
  end
end

dedekind_ispmaximal(O::NfRelOrd, p::Union{NfOrdIdl, NfRelOrdIdl}) = dedekind_test(O, p, Val{false})

dedekind_poverorder(O::NfRelOrd, p::Union{NfOrdIdl, NfRelOrdIdl}) = dedekind_test(O, p)[2]

################################################################################
#
#  p-overorder
#
################################################################################

@doc Markdown.doc"""
      poverorder(O::NfRelOrd, p::Union{NfOrdIdl, NfRelOrdIdl}) -> NfRelOrd

This function tries to find an order that is locally larger than $\mathcal O$
at the prime $p$.
"""
function poverorder(O::NfRelOrd, p::Union{NfOrdIdl, NfRelOrdIdl})
  if isequation_order(O) && issimple(O)
    return dedekind_poverorder(O, p)
  else
    return ring_of_multipliers(pradical(O, p))
  end
end

################################################################################
#
#  p-maximal overorder
#
################################################################################

@doc Markdown.doc"""
      pmaximal_overorder(O::NfRelOrd, p::Union{NfOrdIdl, NfRelOrdIdl}) -> NfRelOrd

This function finds a $p$-maximal order $R$ containing $\mathcal O$.
"""
function pmaximal_overorder(O::NfRelOrd, p::Union{NfOrdIdl, NfRelOrdIdl})
  d = discriminant(O)
  if valuation(d, p) < 2
    return O
  end
  OO = poverorder(O, p)
  dd = discriminant(OO)
  while d != dd
    if valuation(dd, p) < 2
      break
    end
    d = dd
    OO = poverorder(OO, p)
    dd = discriminant(OO)
  end
  return OO
end

function MaximalOrder(O::NfRelOrd)
  disc = discriminant(O)
  fac = factor(disc)
  OO = deepcopy(O)
  for (p, e) in fac
    if e == 1
      continue
    end
    OO += pmaximal_overorder(O, p)
  end
  OO.ismaximal = 1
  return OO
end

################################################################################
#
#  Addition of orders
#
################################################################################

@doc Markdown.doc"""
      +(R::NfRelOrd, S::NfRelOrd) -> NfRelOrd

Given two orders $R$, $S$ of $K$, this function returns the smallest order
containing both $R$ and $S$.
"""
function +(a::NfRelOrd{T, S}, b::NfRelOrd{T, S}) where {T, S}
  # checks
  @assert nf(a) == nf(b)
  aB = basis_pmatrix(a, copy = false)
  bB = basis_pmatrix(b, copy = false)
  d = degree(a)
  PM = sub(pseudo_hnf(vcat(aB, bB), :lowerleft, true), d + 1:2*d, 1:d)
  return NfRelOrd{T, S}(nf(a), PM)
end

################################################################################
#
#  Absolute to relative
#
################################################################################

function relative_order(O::NfOrd, m::NfToNfRel)
  L = codomain(m)
  Labs = domain(m)
  @assert nf(O) == Labs
  K = base_field(L)
  OK = maximal_order(K)
  B = basis(O, Labs, copy = false)
  if ismaximal_known_and_maximal(O)
    E = EquationOrder(L)
    els = elem_type(L)[m(x) for x in B]
    return add_to_order(E, els)
  else
    return _order(L, elem_type(L)[mp(x) for x in B])
  end
end

################################################################################
#
#  Simple to non-simple
#
################################################################################

function non_simple_order(O::NfRelOrd, m::NfRelToNfRelNSMor)
  L = domain(m)
  L_ns = codomain(m)
  @assert nf(O) == L
  K = base_field(L)
  B = basis_nf(O, copy = false)
  d = degree(L)
  M = zero_matrix(K, d, d)
  for i = 1:d
    elem_to_mat_row!(M, i, m(L(B[i])))
  end
  PM = pseudo_hnf(PseudoMatrix(M, Hecke.basis_pmatrix(O).coeffs), :lowerleft, true)
  return NfRelOrd{typeof(PM.matrix[1, 1]), typeof(PM.coeffs[1])}(L_ns, PM)
end

################################################################################
#
#  Denominator in an order
#
################################################################################

@doc Markdown.doc"""
    denominator(a::NumFieldElem, O::NfRelOrd) -> fmpz

Returns the smallest positive integer $k$ such that $k \cdot a$ is contained in
$\mathcal O$.
"""
function denominator(a::NumFieldElem, O::NfRelOrd)
  t = zero_matrix(base_field(nf(O)), 1, degree(O))
  elem_to_mat_row!(t, 1, a)
  t = t*basis_mat_inv(O, copy = false)
  d = fmpz(1)
  icv = inv_coeff_ideals(O, copy = false)
  for i = 1:degree(O)
    tt = icv[i]*t[1, i]
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

function rand(O::NfRelOrd, B::Int)
  pb = pseudo_basis(O, copy = false)
  z = nf(O)()
  for i = 1:degree(O)
    t = rand(pb[i][2], B)
    z += t*pb[i][1]
  end
  return O(z)
end

################################################################################
#
#  Order generated by a set of elements
#
################################################################################

function _order(K::NfRel{nf_elem}, elt::Array{NfRelElem{nf_elem}, 1}; check::Bool = false)
  n = degree(K)
  L = base_field(K)
  OL = maximal_order(L)
  bas = NfRelElem{nf_elem}[one(K)]

  phase = 1

  for e = elt
    if check
      fe = minpoly(e)
      for i = 1:degree(fe)
        if !(coeff(fe, i-1) in OL)
          error("data does not define an order, $e is non-integral")
        end
      end
      df = degree(fe)-1
    else
      df = n-1
    end
    f = one(K)
    for i=1:df
      f *= e
      b = NfRelElem{nf_elem}[e*x for x in bas]
      append!(bas, b)
      if length(bas) >= n
        BK = basis_matrix(bas)
        B = pseudo_hnf(PseudoMatrix(BK), :lowerleft)
        rk = nrows(BK) - n + 1
        while iszero_row(BK, rk)
          rk += 1
        end
        B = sub(B, rk:nrows(B), 1:n)
        bas = _get_gens(B)
      end
    end
  end
  if nrows(B) != degree(K)
    error("Data does not define an order")
  end

  # Make an explicit check
  @hassert :NfRelOrd 1 defines_order(K, B)[1]
  return Order(K, B)
end

function _get_gens(M::PMat)
  mat = M.matrix
  ids = M.coeffs
  gens = Vector{NfRelElem{nf_elem}}()
  for i = 1:nrows(M)
    el = elem_from_mat_row(K, B.matrix, i)
    if isone(ids[i].num)
      push!(gens, divexact(el, ids[i].den))
    else
      push!(gens, divexact(el* ids[i].num.gen_one, ids[i].den))
      push!(gens, divexact(el*ids[i].num.gen_two.elem_in_nf, ids[i].den))
    end
  end
  return gens
end

function _get_gens(O::NfRelOrd)
  B = pseudo_basis(O)
  gens = Vector{NfRelElem{nf_elem}}()
  for i = 1:length(B)
    el = B[i][1]
    I = B[i][2]
    if isone(I.num)
      push!(gens, divexact(el, I.den))
    else
      push!(gens, divexact(I.num.gen_one*el, I.den))
      push!(gens, el*divexact(I.num.gen_two.elem_in_nf, I.den))
    end
  end
  return gens
end




function add_to_order(O::NfRelOrd, elt::Vector{T}; check::Bool = false) where T
  K = nf(O)
  k = base_field(K)
  Ok = maximal_order(k)
  B = basis_pmatrix(O)
  n = degree(O)
  lelt = length(elt)
  count = 0
  for e = elt
    count += 1
    @vprint :NfRelOrd 1 "Element $count / $lelt \n"
    if e in O
      continue
    end
    if check
      fe = minpoly(e)
      for i = 1:degree(fe)
        if !(coeff(fe, i-1) in Ok)
          error("data does not define an order, $e is non-integral")
        end
      end
      df = degree(fe)-1
    else
      df = n-1
    end
    f = one(K)
    
    for i=1:df
      f *= e
      if f in O
        break
      end
      bas = _get_gens(O)
      els_to_add = Vector{NfRelElem{nf_elem}}()
      for x in bas
        el = e*x
        if el in O
          continue
        end
        push!(els_to_add, el)
      end
      if isempty(els_to_add)
        break
      end
      BK = PseudoMatrix(basis_matrix(els_to_add))
      BK = vcat(B, BK)
      B = pseudo_hnf(BK, :lowerleft, true)
      rk = nrows(BK) - n + 1
      while iszero_row(BK.matrix, rk)
        rk += 1
      end
      B = sub(B, rk:nrows(B), 1:n)
      O = Order(K, B)
    end
  end
  return O
end

################################################################################
#
#  Dedekind composite
#
################################################################################


function dedekind_test_composite(O::NfRelOrd{nf_elem, NfOrdFracIdl}, P::NfOrdIdl)
  !isequation_order(O) && error("Order must be an equation order")
  !issimple(O) && error("Not implemented for non-simple extensions")

  L = nf(O)
  K = base_field(L)::AnticNumberField
  T = L.pol::Generic.Poly{nf_elem}
  Kx = parent(T)
  OK = maximal_order(K)
  F, mF = quo(OK, P)
  Fy, y = PolynomialRing(F,"y", cached=false)

  t = map_coeffs(mF, map_coeffs(OK, T), parent = Fy)
  fail, g = gcd_with_failure(t, derivative(t))
  if !isone(fail)
    return K(fail.elem), O
  end
  h = divrem(t, g)[1]

  G = map_coeffs(K, map_coeffs(x -> x.elem, g), parent = Kx)::typeof(T)
  H = map_coeffs(K, map_coeffs(x -> x.elem, h), parent = Kx)::typeof(T)
  assure_2_normal(P)
  pi = anti_uniformizer(P)
  F = pi*(G*H - T)
  f = map_coeffs(mF, map_coeffs(OK, F), parent = Fy)

  fail, dd = gcd_with_failure(g, h)
  if !isone(fail)
    return K(fail.elem), O
  end
  fail, d = gcd_with_failure(f, dd)
  if !isone(fail)
    return K(fail.elem), O
  end

  if isone(d)
    return one(K), O
  end

  u = divrem(t, d)[1]
  U = map_coeffs(K, map_coeffs(x -> x.elem, u), parent = Kx)
  M = representation_matrix(pi*L(U))
  for i = 1:nrows(M)
    for j = 1:ncols(M)
      @assert M[i, j] in OK
    end
  end
  PM = PseudoMatrix(representation_matrix(pi*L(U)), [ K(1)*OK for i = 1:degree(O) ])
  BM = basis_pmatrix(O)::PMat{nf_elem,Hecke.NfAbsOrdFracIdl{AnticNumberField,nf_elem}}
  PN = vcat(BM, PM)::PMat{nf_elem,Hecke.NfAbsOrdFracIdl{AnticNumberField,nf_elem}}
  PN = sub(pseudo_hnf_mod(PN, P, :lowerleft), degree(O) + 1:2*degree(O), 1:degree(O))
  OO = Order(L, PN)
  OO.isequation_order = false
  return one(K), OO
end

