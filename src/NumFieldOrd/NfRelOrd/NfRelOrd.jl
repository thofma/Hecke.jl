add_verbosity_scope(:RelNumFieldOrder)

################################################################################
#
#  Is maximal order known
#
################################################################################

function is_maximal_order_known(K::T) where T <: Union{RelSimpleNumField, RelNonSimpleNumField}
  return has_attribute(K, :maximal_order)
end

################################################################################
#
#  Basic field access
#
################################################################################

parent(O::RelNumFieldOrder) = O.parent

base_ring(O::RelNumFieldOrder) = order(pseudo_basis(O, copy = false)[1][2])

base_ring_type(::Type{RelNumFieldOrder{T, S, U}}) where {T, S, U} = order_type(base_ring_type(NumField{T}))

elem_type(::Type{RelNumFieldOrder{T, S, U}}) where {T, S, U} = RelNumFieldOrderElem{T, U}

ideal_type(::RelNumFieldOrder{T, S, U}) where {T, S, U} = RelNumFieldOrderIdeal{T, S, U}

ideal_type(::Type{RelNumFieldOrder{T, S, U}}) where {T, S, U} = RelNumFieldOrderIdeal{T, S, U}

fractional_ideal_type(::RelNumFieldOrder{T, S, U}) where {T, S, U} = RelNumFieldOrderFractionalIdeal{T, S, U}

fractional_ideal_type(::Type{RelNumFieldOrder{T, S, U}}) where {T, S, U} = RelNumFieldOrderFractionalIdeal{T, S, U}

################################################################################
#
#  Modulus
#
################################################################################

# Return a small OK-ideal I such that I * OK^n \subseteq OL (with respect to
# the basis of OK)
# This is required for the modular computations with ideals.
function _modulus(O::RelNumFieldOrder)
  D = get_attribute(O, :modulus)
  if D isa Nothing
    D = reduce(lcm, coefficient_ideals(basis_pmatrix(O)))
    # Let D = N/d
    # In particular (N/d) * OK^n \subseteq OL
    # N*OK \subseteq N/d * OK \subseteq OL
    # So we take N
    M = numerator(simplify(D))
    set_attribute!(O, :modulus => M)
    return M
  else
    return D::ideal_type(base_ring(O))
  end
end

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_basis_pmatrix(O::RelNumFieldOrder{T, S, U}) where {T, S, U}
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
  O.basis_pmatrix = pseudo_matrix(M, C)
  return nothing
end

function assure_has_pseudo_basis(O::RelNumFieldOrder{T, S, U}) where {T, S, U}
  if isdefined(O, :pseudo_basis)
    return nothing
  end
  if !isdefined(O, :basis_pmatrix)
    error("No pseudo_basis and no basis_pmatrix defined.")
  end
  P = basis_pmatrix(O, copy = false)
  L = nf(O)
  pseudo_basis = Vector{Tuple{U, S}}()
  for i = 1:degree(O)
    a = elem_from_mat_row(L, P.matrix, i)
    push!(pseudo_basis, (a, deepcopy(P.coeffs[i])))
  end
  O.pseudo_basis = pseudo_basis
  return nothing
end

function assure_has_basis_nf(O::RelNumFieldOrder{T, S, U}) where {T, S, U}
  if isdefined(O, :basis_nf)
    return nothing
  end
  L = nf(O)
  pb = pseudo_basis(O)
  basis_nf = Vector{U}()
  for i = 1:degree(O)
    push!(basis_nf, pb[i][1])
  end
  O.basis_nf = basis_nf
  return nothing
end

function assure_has_basis_matrix(O::RelNumFieldOrder)
  if isdefined(O, :basis_matrix)
    return nothing
  end
  O.basis_matrix = basis_pmatrix(O).matrix
  return nothing
end

function assure_has_basis_mat_inv(O::RelNumFieldOrder)
  if isdefined(O, :basis_mat_inv)
    return nothing
  end
  O.basis_mat_inv = inv(basis_matrix(O, copy = false))
  return nothing
end

function assure_has_inv_coeff_ideals(O::RelNumFieldOrder)
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

@doc raw"""
      pseudo_basis(O::RelNumFieldOrder{T, S}) -> Vector{Tuple{NumFieldElem{T}, S}}

Returns the pseudo-basis of $\mathcal O$.
"""
function pseudo_basis(O::RelNumFieldOrder; copy::Bool = true)
  assure_has_pseudo_basis(O)
  if copy
    return deepcopy(O.pseudo_basis)
  else
    return O.pseudo_basis
  end
end

@doc raw"""
      basis_pmatrix(O::RelNumFieldOrder) -> PMat

Returns the basis pseudo-matrix of $\mathcal O$ with respect to the power basis
of the ambient number field.
"""
function basis_pmatrix(O::RelNumFieldOrder; copy::Bool = true)
  assure_has_basis_pmatrix(O)
  if copy
    return deepcopy(O.basis_pmatrix)
  else
    return O.basis_pmatrix
  end
end

@doc raw"""
      inv_coeff_ideals(O::RelNumFieldOrder{T, S}) -> Vector{S}

Returns the inverses of the coefficient ideals of the pseudo basis of $O$.
"""
function inv_coeff_ideals(O::RelNumFieldOrder; copy::Bool = true)
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

@doc raw"""
      basis_nf(O::RelNumFieldOrder) -> Vector{NumFieldElem}

Returns the elements of the pseudo-basis of $\mathcal O$ as elements of the
ambient number field.
"""
function basis_nf(O::RelNumFieldOrder{S, T, U}; copy::Bool = true) where {S, T, U}
  assure_has_basis_nf(O)
  if copy
    return deepcopy(O.basis_nf)::Vector{U}
  else
    return O.basis_nf::Vector{U}
  end
end

function basis_matrix(O::RelNumFieldOrder; copy::Bool = true)
  assure_has_basis_matrix(O)
  if copy
    return deepcopy(O.basis_matrix)
  else
    return O.basis_matrix
  end
end

function basis_mat_inv(O::RelNumFieldOrder; copy::Bool = true)
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

function show(io::IO, O::RelNumFieldOrder)
  compact = get(io, :compact, false)
  if compact
    if is_maximal_known_and_maximal(O)
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
    if is_maximal_known_and_maximal(O)
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

function assure_has_discriminant(O::RelNumFieldOrder{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal, RelSimpleNumFieldElem{AbsSimpleNumFieldElem}})
  if isdefined(O, :disc_abs)
    return nothing
  end
  if is_equation_order(O)
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

function assure_has_discriminant(O::RelNumFieldOrder{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal, RelNonSimpleNumFieldElem{AbsSimpleNumFieldElem}})
  if isdefined(O, :disc_abs)
    return nothing
  end
  if is_equation_order(O)
    K = nf(O)
    F = base_field(K)
    OF = maximal_order(F)
    pols = K.pol
    Fx, _ = polynomial_ring(F, "x", cached = false)
    pol = to_univariate(Fx, pols[1])
    d = OF(discriminant(pol))^(div(degree(K), degree(pol)))
    for i = 2:length(pols)
      pol = to_univariate(Fx, pols[i])
      d *= OF(discriminant(pol))^(div(degree(K), degree(pol)))
    end
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

function assure_has_discriminant(O::RelNumFieldOrder{T, S, U}) where {T, S, U}
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

function discriminant(O::RelNumFieldOrder{AbsSimpleNumFieldElem, S}) where S
  assure_has_discriminant(O)
  return deepcopy(O.disc_abs)
end

function discriminant(O::RelNumFieldOrder{T, S}) where {T <: NumFieldElem{U} where U, S}
  assure_has_discriminant(O)
  return deepcopy(O.disc_rel)::ideal_type(order_type(base_field(nf(O))))
end

function absolute_discriminant(O::RelNumFieldOrder{T, S}) where {T, S}
  d = norm(discriminant(O))
  d1 = absolute_discriminant(base_ring(O))
  di = abs(d1^(degree(O))*d)

  # Compute the sign using Brill's theorem
  _, s = signature(nf(O))
  if mod(s, 2) == 0
    return di
  else
    return -di
  end
end

function absolute_discriminant(O::AbsNumFieldOrder)
  return discriminant(O)
end

################################################################################
#
#  Codifferent
#
################################################################################

function codifferent(O::RelNumFieldOrder)
  T = trace_matrix(O, copy = false)
  R = base_ring(O)
  K = nf(R)
  pb = pseudo_basis(O)
  pm = pseudo_matrix(inv(change_base_ring(K, T)),
                     fractional_ideal_type(base_ring(O))[inv(y) for (_, y) in pb])
  return fractional_ideal(O, pm)
end

function different(O::RelNumFieldOrder)
  if !is_maximal_known_and_maximal(O)
    error("Order not known to be maximal")
  end
  return ideal(O, basis_pmatrix(inv(codifferent(O))))
end

################################################################################
#
#  Degree
#
################################################################################

degree(O::RelNumFieldOrder) = degree(nf(O))

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(O::RelNumFieldOrder{T, S, U}, dict::IdDict) where {T, S, U}
  z = RelNumFieldOrder{T, S, U}(O.nf)
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

function _check_elem_in_order(a::U, O::RelNumFieldOrder{T, S, U}, ::Val{short} = Val(false)) where {T, S, U, short}
  b_pmat = basis_pmatrix(O, copy = false)
  t = zero_matrix(base_field(nf(O)), 1, degree(O))
  elem_to_mat_row!(t, 1, a)
  t = t*basis_mat_inv(O, copy = false)
  if short
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

function in(a::U, O::RelNumFieldOrder{T, S, U}) where {T, S, U}
  return _check_elem_in_order(a, O, Val(true))
end

################################################################################
#
#  Construction
#
################################################################################

function Order(L::RelSimpleNumField{AbsSimpleNumFieldElem}, M::Generic.Mat{AbsSimpleNumFieldElem})
  return RelNumFieldOrder{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal, RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}(L, deepcopy(M))
end

function Order(L::RelNonSimpleNumField{AbsSimpleNumFieldElem}, M::Generic.Mat{AbsSimpleNumFieldElem})
  return RelNumFieldOrder{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal, RelNonSimpleNumFieldElem{AbsSimpleNumFieldElem}}(L, deepcopy(M))
end


function Order(L::NumField{S}, M::Generic.Mat{S}) where S <: NumFieldElem{T} where T
  return RelNumFieldOrder{S, RelNumFieldOrderFractionalIdeal{T}, elem_type(L)}(L, deepcopy(M))
end

#=
@doc raw"""
      Order(K::NumField, M::PMat) -> RelNumFieldOrder

Returns the order which has basis pseudo-matrix $M$ with respect to the power basis
of $K$.
"""
=#
function Order(L::NumField{T}, M::PMat{T, S}) where {T, S}
  # checks
  return RelNumFieldOrder{T, S, elem_type(L)}(L, deepcopy(M))
end

function EquationOrder(L::NumField)
  M = identity_matrix(base_field(L), degree(L))
  PM = pseudo_matrix(M)
  O = Order(L, PM)
  O.basis_mat_inv = M
  O.is_equation_order = true
  return O
end

function any_order(K::RelSimpleNumField)
  f = defining_polynomial(K)
  de = _integral_multiplicator(f)
  g = f * de
  if is_monic(g)
    return equation_order(K)
  else
    d = degree(g)
    M = zero_matrix(base_field(K), d, d)
    M[1, 1] = 1
    for i in 2:d
      for j in i:-1:2
        M[i, j] = coeff(g, d - (i - j))
      end
    end
    B = pseudo_hnf(pseudo_matrix(M), :lowerleft)
    return Order(K, B)
  end
end

function any_order(K::RelNonSimpleNumField)
  normalized_gens = Vector{elem_type(K)}(undef, ngens(K))
  g = gens(K)
  pols = defining_polynomials(K)
  for i in 1:ngens(K)
    f = _integral_multiplicator(K.pol[i]) * K.pol[i]
    if isone(coeff(f, 1))
      normalized_gens[i] = g[i]
    else
      normalized_gens[i] = coeff(f, 1) * g[i]
    end
  end

  b = Vector{elem_type(K)}(undef, degree(K))
  ind = 1
  it = cartesian_product_iterator([1:degrees(K)[i] for i in 1:ngens(K)], inplace = true)
  for i in it
    b[ind] = prod(normalized_gens[j]^(i[j] - 1) for j=1:length(i))
    ind += 1
  end
  return Order(K, basis_matrix(b))
end

function EquationOrder(L::RelSimpleNumField{AbsSimpleNumFieldElem})
  a = gen(L)
  @req is_integral(a) "Generator of must be integral"
  M = identity_matrix(base_field(L), degree(L))
  PM = pseudo_matrix(M)
  O = Order(L, PM)
  O.basis_mat_inv = M
  O.is_equation_order = true
  O.index = ideal(maximal_order(base_field(L)), 1)
  return O
end

equation_order(L::NumField) = EquationOrder(L)

function MaximalOrder(L::NumField)
  return get_attribute!(L, :maximal_order) do
    O = MaximalOrder(any_order(L))
    O.is_maximal = 1
    return O
  end::order_type(L)
end

function maximal_order_via_absolute(L::RelSimpleNumField)
  Labs, LabsToL = absolute_simple_field(L)
  Oabs = maximal_order(Labs)
  return relative_order(Oabs, LabsToL)
end

function maximal_order_via_absolute(m::NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}})
  Oabs = maximal_order(domain(m))
  return relative_order(Oabs, m)
end

function maximal_order_via_simple(L::RelNonSimpleNumField)
  Ls, m = simple_extension(L)
  Os = maximal_order(Ls)
  return non_simple_order(Os, m)
end

function maximal_order_via_simple(m::NumFieldHom{<:RelSimpleNumField, <:RelNonSimpleNumField})
  Os = maximal_order(domain(m))
  return non_simple_order(Os, m)
end

function maximal_order_via_relative(K::AbsSimpleNumField, m::NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}})
  return get_attribute!(K, :maximal_order) do
    L = codomain(m)
    OL = maximal_order(L)
    B = absolute_basis(OL, L)
    OK = Order(K, [ m\b for b in B ], check = false, isbasis = true)
    OK.is_maximal = 1
    return OK
  end::order_type(K)
end

function absolute_basis(O::RelNumFieldOrder{T, S, U}, K::NumField{T}) where {T, S, U}
  pb = pseudo_basis(O, copy = false)
  res = Vector{elem_type(K)}()
  for i = 1:degree(O)
    for b in absolute_basis(pb[i][2])
      push!(res, b*pb[i][1])
    end
  end
  return res
end

################################################################################
#
#  Equality
#
################################################################################

function ==(R::RelNumFieldOrder, S::RelNumFieldOrder)
  nf(R) != nf(S) && return false
  return basis_pmatrix(R, copy = false) == basis_pmatrix(S, copy = false)
end

################################################################################
#
#  Trace matrix
#
################################################################################

#=
@doc raw"""
    trace_matrix(O::RelNumFieldOrder{T, S}) -> Generic.Mat{T}

Returns the trace matrix of $\mathcal O$ with respect to $(\omega_1,\dotsc,\omega_d)$
where $(\mathfrak c_i, \omega_i)$ is the pseudo-basis of $\mathcal O$.
"""
=#
function trace_matrix(O::RelNumFieldOrder; copy::Bool = true)
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

function fq_nmod_poly_to_nf_elem_poly(R::Generic.PolyRing{AbsSimpleNumFieldElem}, m::InverseMap, f::fqPolyRepPolyRingElem)
  @assert codomain(m) == base_ring(R)
  @assert domain(m) == base_ring(parent(f))

  g = zero(R)
  for i = 0:degree(f)
    setcoeff!(g, i, m(coeff(f, i)))
  end
  return g
end

function fq_poly_to_nf_elem_poly(R::Generic.PolyRing{T}, m::InverseMap, f) where {T <: Union{AbsSimpleNumFieldElem, RelSimpleNumFieldElem}}
  return map_coefficients(m, f, parent = R)
end

# Algorithm IV.6. in "Berechnung relativer Ganzheitsbasen mit dem
# Round-2-Algorithmus" by C. Friedrichs.
function dedekind_test(O::RelNumFieldOrder{U1, V, Z}, p::Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal}, ::Val{compute_order} = Val(true)) where {compute_order, U1, V, Z <: RelSimpleNumFieldElem}
  !is_equation_order(O) && error("Order must be an equation order")

  L = nf(O)
  K = base_field(L)
  T = L.pol
  Kx = parent(T)
  OK = maximal_order(K)
  F, mF = residue_field(OK, p)
  mmF = extend(mF, K)
  immF = pseudo_inv(mmF)
  Fy, y = polynomial_ring(F,"y", cached=false)

  Tmodp = map_coefficients(mmF, T, parent = Fy)
  fac = factor(Tmodp)
  g = Kx(1)
  for (t, e) in fac
    mul!(g, g, fq_poly_to_nf_elem_poly(Kx, immF, t))
  end
  gmodp = map_coefficients(mmF, g, parent = Fy)
  hmodp = divexact(Tmodp, gmodp)
  h = fq_poly_to_nf_elem_poly(Kx, immF, hmodp)
  a = anti_uniformizer(p)
  f = a*(g*h - T)
  fmodp = map_coefficients(mmF, f, parent = Fy)

  d = gcd(fmodp, gcd(gmodp, hmodp))

  if !compute_order
    return isone(d)
  else
    if isone(d)
      return true, O
    end

    Umodp = divexact(Tmodp, d)
    U = fq_poly_to_nf_elem_poly(Kx, immF, Umodp)
    PM = pseudo_matrix(representation_matrix(a*U(gen(L))), [ K(1)*OK for i = 1:degree(O) ])
    PN = vcat(basis_pmatrix(O), PM)
    PN = sub(pseudo_hnf_full_rank_with_modulus(PN, p, :lowerleft), degree(O) + 1:2*degree(O), 1:degree(O))
    OO = typeof(O)(L, PN)
    OO.is_equation_order = false
    return false, OO
  end
end

dedekind_ispmaximal(O::RelNumFieldOrder, p::Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal}) = dedekind_test(O, p, Val(false))

dedekind_poverorder(O::RelNumFieldOrder, p::Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal}) = dedekind_test(O, p)[2]

################################################################################
#
#  p-overorder
#
################################################################################

#=
@doc raw"""
      poverorder(O::RelNumFieldOrder, p::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal}) -> RelNumFieldOrder

This function tries to find an order that is locally larger than $\mathcal O$
at the prime $p$.
"""
=#
function poverorder(O::RelNumFieldOrder, p::Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal})
  if is_equation_order(O) && is_simple(O)
    @vprintln :RelNumFieldOrder 3 "Applying Dedekind criterion"
    return dedekind_poverorder(O, p)
  else
    @vprintln :RelNumFieldOrder 3 "Computing pradical"
    @vtime :RelNumFieldOrder 4 Ip = pradical(O, p)
    @vprintln :RelNumFieldOrder 3 "Computing ring of multipliers"
    @vtime :RelNumFieldOrder 4 Op = ring_of_multipliers(Ip)
    return Op
  end
end

function poverorder(O::RelNumFieldOrder{S, T, RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) where {S, T}
  if is_equation_order(O)
    return overorder_polygons(O, p)
  end
  @vprintln :RelNumFieldOrder 3 "Computing pradical"
  @vtime :RelNumFieldOrder 4 Ip = pradical(O, p)
  @vprintln :RelNumFieldOrder 3 "Computing ring of multipliers"
  @vtime :RelNumFieldOrder 4 Op = ring_of_multipliers(Ip)
  return Op
end

################################################################################
#
#  p-maximal overorder
#
################################################################################
#=
@doc raw"""
      pmaximal_overorder(O::RelNumFieldOrder, p::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal}) -> RelNumFieldOrder

This function finds a $p$-maximal order $R$ containing $\mathcal O$.
"""
=#
function pmaximal_overorder(O::RelNumFieldOrder, p::Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal})
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

function _maximal_order_round2(O::RelNumFieldOrder)
  disc = discriminant(O)
  fac = factor(disc)
  OO = O
  for (p, e) in fac
    if e == 1
      continue
    end
    OO = sum_as_OK_modules(OO, pmaximal_overorder(O, p))
  end
  OO.is_maximal = 1
  return OO
end

function MaximalOrder(O::RelNumFieldOrder{S, T, U}) where {S, T, U <: NonSimpleNumFieldElem}
  L = nf(O)
  K = base_field(L)
  Obase_K = maximal_order(K)
  fields = Vector{Tuple{RelSimpleNumField{S}, morphism_type(RelSimpleNumField{S}, RelNonSimpleNumField{S})}}(undef, length(L.pol))
  for i = 1:length(L.pol)
    fields[i] = component(L, i)
  end
  #Now, bring the maximal order of every component in L
  discs = Vector{ideal_type(Obase_K)}(undef, ngens(L))
  B = Vector{Vector{Tuple{elem_type(L), fractional_ideal_type(Obase_K)}}}(undef, length(fields))
  for i = 1:length(fields)
    OK = maximal_order(fields[i][1])
    discs[i] = discriminant(OK)
    BOK = pseudo_basis(OK, copy = false)
    BK = Vector{Tuple{elem_type(L), fractional_ideal_type(Obase_K)}}(undef, degree(OK))
    for j = 1:length(BK)
      BK[j] = (fields[i][2](BOK[j][1]), BOK[j][2])
    end
    B[i] = BK
  end
  Bp = product_pseudobasis(B)
  MOstart = pseudo_matrix(basis_matrix(U[x[1] for x in Bp]), fractional_ideal_type(Obase_K)[x[2] for x in Bp])
  Ostart = Order(L, MOstart)
  lp = ideal_type(Obase_K)[]
  for i = 1:length(fields)
    for j = i+1:length(fields)
      push!(lp, gcd(discs[i], discs[j]))
    end
  end
  cp = coprime_base(lp)
  for I in cp
    lP = factor(I)
    for P in keys(lP)
      Ostart = pmaximal_overorder(Ostart, P)
    end
  end
  return Ostart
end

function product_pseudobasis(l::Vector{Vector{Tuple{T, S}}}) where {S, T <: Union{AbsNumFieldOrderElem, RelNumFieldOrderElem, NumFieldElem}}
  nelems = 1
  for i = 1:length(l)
    nelems *= length(l[i])
  end
  B = typeof(l[1])(undef, nelems)
  ind = length(l[1])
  for i = 1:ind
    B[i] = l[1][i]
  end
  for jj = 2:length(l)
    new_deg = length(l[jj])
    for i = 2:new_deg
      for j = 1:ind
        B[(i-1)* ind + j] = (B[j][1] * l[jj][i][1], B[j][2] * l[jj][i][2])
      end
    end
    ind *= new_deg
  end
  return B
end

################################################################################
#
#  Addition of orders
#
################################################################################
#TODO: this is wrong unless the indices are coprime
function +(a::RelNumFieldOrder{T, S, U}, b::RelNumFieldOrder{T, S, U}) where {T, S, U}
  # checks
  @assert nf(a) == nf(b)
  d = degree(a)
  aB = basis_pmatrix(a, copy = false)
  bB = basis_pmatrix(b, copy = false)
  M = vcat(aB, bB)
  PM = sub(pseudo_hnf(M, :lowerleft, true), d + 1:2*d, 1:d)
  return RelNumFieldOrder{T, S, U}(nf(a), PM)
end

function +(a::RelNumFieldOrder{T, S, U}, b::RelNumFieldOrder{T, S, U}) where {T, S, U <: Union{RelSimpleNumFieldElem{AbsSimpleNumFieldElem}, RelNonSimpleNumFieldElem{AbsSimpleNumFieldElem}}}
  # checks
  @assert nf(a) == nf(b)
  K = base_field(nf(a))
  d = degree(a)
  aB = basis_pmatrix(a)
  bB = basis_pmatrix(b)
  M = vcat(aB, bB)
  z = _make_integral!(M)
  d1 = numerator(det(sub(M, 1:d, 1:d)))
  d2 = numerator(det(sub(M, d+1:2*d, 1:d)))
  m = d1 + d2
  M = sub(pseudo_hnf_mod(M, m, :lowerleft), d + 1:2*d, 1:d)
  for i in 1:nrows(M)
    M.coeffs[i] = M.coeffs[i]*inv(K(z))
    simplify(M.coeffs[i])
  end
  return RelNumFieldOrder{T, S, U}(nf(a), M)
end

function sum_as_OK_modules(a::RelNumFieldOrder{T, S, U}, b::RelNumFieldOrder{T, S, U}) where {T, S, U <: RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}
  if !isdefined(a, :index) || !isdefined(b, :index)
    return a+b
  end
  K = base_field(nf(a))
  d = degree(a)
  aB = basis_pmatrix(a)
  bB = basis_pmatrix(b)
  M = vcat(aB, bB)
  new_index = a.index * b.index
  M = sub(pseudo_hnf_full_rank_with_modulus(M, new_index, :lowerleft), d+1:2*d, 1:d)
  res = RelNumFieldOrder{T, S, U}(nf(a), M)
  res.index = new_index
  res.disc_abs = simplify(gcd(discriminant(a), discriminant(b)))
  return res
end


function sum_as_OK_modules(a::RelNumFieldOrder{T, S, U}, b::RelNumFieldOrder{T, S, U}) where {T, S, U}
  return a+b
end

################################################################################
#
#  Absolute to relative
#
################################################################################

function relative_order(O::AbsSimpleNumFieldOrder, m::NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}})
  L = codomain(m)
  Labs = domain(m)
  @assert nf(O) == Labs
  K = base_field(L)
  OK = maximal_order(K)
  B = basis(O, Labs, copy = false)
  if is_maximal_known_and_maximal(O)
    E = EquationOrder(L)
    els = elem_type(L)[m(x) for x in B]
    return add_to_order(E, els)
  else
    return _order(elem_type(L)[mp(x) for x in B])
  end
end

################################################################################
#
#  Simple to non-simple
#
################################################################################

function non_simple_order(O::RelNumFieldOrder, m::NumFieldHom{<:RelSimpleNumField, <:RelNonSimpleNumField})
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
  PM = pseudo_hnf(pseudo_matrix(M, Hecke.basis_pmatrix(O).coeffs), :lowerleft, true)
  return RelNumFieldOrder{typeof(PM.matrix[1, 1]), typeof(PM.coeffs[1]), elem_type(L_ns)}(L_ns, PM)
end

################################################################################
#
#  Denominator in an order
#
################################################################################

@doc raw"""
    denominator(a::NumFieldElem, O::AbsSimpleNumFieldOrder) -> ZZRingElem

Returns the smallest positive integer $k$ such that $k \cdot a$ is contained in
$\mathcal O$.
"""
function denominator(a::NumFieldElem, O::RelNumFieldOrder)
  t = zero_matrix(base_field(nf(O)), 1, degree(O))
  elem_to_mat_row!(t, 1, a)
  t = t*basis_mat_inv(O, copy = false)
  d = ZZRingElem(1)
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

RandomExtensions.maketype(O::RelNumFieldOrder, ::Int) = elem_type(O)

function rand(rng::AbstractRNG, sp::SamplerTrivial{<:Make2{<:RelNumFieldOrderElem,<:RelNumFieldOrder,Int}})
  O, B = sp[][1:2]
  pb = pseudo_basis(O, copy = false)
  z = nf(O)()
  for i = 1:degree(O)
    t = rand(rng, pb[i][2], B)
    z += t*pb[i][1]
  end
  return O(z)
end

rand(O::RelNumFieldOrder, B::Int) = rand(GLOBAL_RNG, O, B)
rand(rng::AbstractRNG, O::RelNumFieldOrder, B::Int) = rand(rng, make(O, B))

################################################################################
#
#  Order generated by a set of elements
#
################################################################################

Order(elt::Vector{S}; check::Bool = false, cached::Bool = false) where {S <: Union{RelSimpleNumFieldElem, RelNonSimpleNumFieldElem}} = _order(elt, check = check)

function _order(elt::Vector{S}; check::Bool = false) where {S <: Union{RelSimpleNumFieldElem, RelNonSimpleNumFieldElem}}
  @assert length(elt) > 0
  K = parent(elt[1])
  n = degree(K)
  L = base_field(K)
  OL = maximal_order(L)
  bas = S[one(K)]

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
      b = S[e*x for x in bas]
      append!(bas, b)
      if length(bas) >= n
        BK = basis_matrix(bas)
        B = pseudo_hnf(pseudo_matrix(BK), :lowerleft)
        rk = nrows(BK) - n + 1
        while is_zero_row(BK, rk)
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
  @hassert :RelNumFieldOrder 1 defines_order(K, B)[1]
  return Order(K, B)
end

function _get_gens(M::PMat)
  mat = M.matrix
  ids = M.coeffs
  gens = Vector{RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}()
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

function _get_gens(O::RelNumFieldOrder)
  B = pseudo_basis(O)
  gens = Vector{RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}()
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


function add_to_order(O::RelNumFieldOrder, elt::Vector{T}; check::Bool = false) where T
  K = nf(O)
  k = base_field(K)
  Ok = maximal_order(k)
  B = basis_pmatrix(O)
  n = degree(O)
  lelt = length(elt)
  count = 0
  for e = elt
    count += 1
    @vprintln :RelNumFieldOrder 1 "Element $count / $lelt"
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
      els_to_add = Vector{RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}()
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
      BK = pseudo_matrix(basis_matrix(els_to_add))
      BK = vcat(B, BK)
      B = pseudo_hnf(BK, :lowerleft, true)
      rk = nrows(BK) - n + 1
      while is_zero_row(BK.matrix, rk)
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


function dedekind_test_composite(O::RelNumFieldOrder{U1, V, Z}, P::Union{RelNumFieldOrderIdeal, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}) where {U1, V, Z <: RelSimpleNumFieldElem}
  !is_equation_order(O) && error("Order must be an equation order")

  L = nf(O)
  K = base_field(L)
  T = L.pol
  Kx = parent(T)
  OK = maximal_order(K)
  F, mF = quo(OK, P)
  Fy, y = polynomial_ring(F,"y", cached=false)

  t = map_coefficients(mF, map_coefficients(OK, T, cached = false), parent = Fy)
  fail, g = gcd_with_failure(t, derivative(t))
  if !isone(fail)
    return K(fail.elem), O
  end
  h = divrem(t, g)[1]

  G = map_coefficients(K, map_coefficients(x -> x.elem, g), parent = Kx)::typeof(T)
  H = map_coefficients(K, map_coefficients(x -> x.elem, h), parent = Kx)::typeof(T)
  assure_2_normal(P)
  pi = anti_uniformizer(P)
  F = pi*(G*H - T)
  f = map_coefficients(mF, map_coefficients(OK, F, cached = false), parent = Fy)

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
  U = map_coefficients(K, map_coefficients(x -> x.elem, u, cached = false), parent = Kx)
  M = representation_matrix(pi*L(U))
  PM = pseudo_matrix(representation_matrix(pi*L(U)), [ K(1)*OK for i = 1:degree(O) ])
  BM = basis_pmatrix(O)
  PN = vcat(BM, PM)
  PN = sub(pseudo_hnf_full_rank_with_modulus(PN, P, :lowerleft), degree(O) + 1:2*degree(O), 1:degree(O))
  OO = typeof(O)(L, PN)
  OO.index = P
  OO.is_equation_order = false
  return one(K), OO
end

function prefactorization_discriminant(K::RelSimpleNumField, d::Union{RelNumFieldOrderIdeal, AbsNumFieldOrderIdeal})
  OK = order(d)
  @assert nf(OK) == base_field(K)
  f = K.pol
  factors = typeof(d)[]
  moduli = prefactorization(d)
  while !isempty(moduli)
    I = pop!(moduli)
    I = is_power(I)[2]
    if is_prime(absolute_minimum(I))
      push!(factors, I)
      continue
    end
    Q, mQ = quo(OK, I)
    Qx = polynomial_ring(Q, cached = false)[1]
    fQ = map_coefficients(mQ, map_coefficients(OK, f, cached = false) , parent = Qx)
    fQ1 = derivative(fQ)
    fail = gcd_with_failure(fQ, fQ1)[1]
    if isone(fail)
      push!(factors, I)
      continue
    end
    J = ideal(OK, fail.elem)
    cp = coprime_base(typeof(d)[J, I])
    append!(moduli, typeof(I)[Inew for Inew in cp if !is_coprime(I, Inew)])
  end
  return factors
end

function prefactorization(I::RelNumFieldOrderIdeal)
  OK = order(I)
  m = absolute_minimum(I)
  ideals = typeof(I)[]
  pp, r = _factors_trial_division(m)
  for p in pp
    push!(ideals, I + ideal(OK, p))
  end
  r = is_power(r)[2]
  if !isone(r)
    push!(ideals, I + ideal(OK, r))
  end
  return ideals
end

function MaximalOrder(O::RelNumFieldOrder{S, T, U}) where {S, T, U <: RelSimpleNumFieldElem}
  # If O contains OK[a] with a the generator of nf(O), then we do something
  # clever as in the absolute case (composite Dedekind test and prefactorization)
  #
  # Otherwise, do the Round 2
  if is_integral(gen(nf(O)))
    return _maximal_order_rel_nice(O)::typeof(O)
  else
    return _maximal_order_round2(O)::typeof(O)
  end
end

function _maximal_order_rel_nice(O::RelNumFieldOrder{S, T, U}) where {S, T, U <: RelSimpleNumFieldElem}
  K = nf(O)
  L = base_field(K)
  OL = maximal_order(L)
  d = discriminant(O)
  facts = prefactorization_discriminant(K, d)
  sort!(facts, by = x -> absolute_minimum(x), rev = true)
  @vprintln :RelNumFieldOrder 1 "Factors of the discriminant lying over $([minimum(x) for x in facts])"
  E = EquationOrder(K)
  OO = O
  while !isempty(facts)
    p = pop!(facts)
    pm = absolute_minimum(p)
    if is_prime_power(pm)
      @vprintln :RelNumFieldOrder 1 "Factoring ideal over $(pm)"
      @vtime :RelNumFieldOrder 1 lf = factor(p)
      for q in keys(lf)
        @vprintln :RelNumFieldOrder 1 "Computing pmaximal order for $(q)"
        @vtime :RelNumFieldOrder 1 Oq = pmaximal_overorder(O, q)
        @vtime :RelNumFieldOrder 1 OO = sum_as_OK_modules(OO, Oq)
      end
    else
      @vprintln :RelNumFieldOrder 1 "Dedekind test for ideal lying over $(pm)"
      @vtime :RelNumFieldOrder 1 fail, E1 = Hecke.dedekind_test_composite(E, p)
      if !isone(fail)
        J = ideal(OL, OL(fail))
        cp = coprime_base(typeof(p)[J, p])
        for q in cp
          if !is_coprime(q, p)
            push!(facts, q)
          end
        end
        continue
      end
      if discriminant(E) != discriminant(E1)
        @vtime :RelNumFieldOrder 1 OO = sum_as_OK_modules(OO, E1)
      end
      g = gcd(discriminant(OO), p)
      if !isone(g)
        @vprintln :RelNumFieldOrder 1 "Factoring ideal over $(absolute_minimum(g))"
        @vtime :RelNumFieldOrder 1 lf = factor(g)
        for q in keys(lf)
          @vprintln :RelNumFieldOrder 1 "Computing pmaximal order for $(q)"
          @vtime :RelNumFieldOrder 1 Oq = pmaximal_overorder(O, q)
          @vtime :RelNumFieldOrder 1 OO = sum_as_OK_modules(OO, Oq)
        end
      end
    end
  end
  OO.is_maximal = 1
  return OO
end

function overorder_polygons(O::RelNumFieldOrder{S, T, RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) where {S, T}
  @assert is_equation_order(O)
  K = nf(O)
  f = K.pol
  k = base_field(K)
  kt = parent(f)
  Ok = maximal_order(k)
  F, mF = residue_field(Ok, p)
  mF1 = extend(mF, k)
  f1 = map_coefficients(mF1, f, cached = false)
  sqf = factor_squarefree(f1)
  l = powers(gen(K), degree(K)-1)
  maxv = 0
  regular = true
  vdisc = 0
  for (gg, m) in sqf
    isone(m) && continue
    fac = factor(gg)
    for (g, m1) in fac
      phi = map_coefficients(pseudo_inv(mF1), g, parent = kt)
      dev, quos = phi_development_with_quos(f, phi)
      N = _newton_polygon(dev, p)
      for i = 1:m
        v = _floor_newton_polygon(N, i)
        maxv = max(v, maxv)
        if v > 0
          vdisc += v*degree(phi)
          pow_anti = anti_uniformizer(p)^v
          for j = 1:degree(phi)
            q1 = shift_left(quos[i], j-1)
            push!(l, mod(K(q1)*pow_anti, minimum(p, copy = false)))
          end
        end
      end
    end
  end
  B = basis_matrix(l)
  M = pseudo_matrix(B)
  index = p^maxv
  M = sub(pseudo_hnf_full_rank_with_modulus(M, index, :lowerleft), length(l)-degree(K)+1:length(l), 1:degree(K))
  O1 = typeof(O)(K, M)
  O1.index = index
  O1.disc_abs = divexact(O.disc_abs, p^(2*vdisc))
  return O1
end

################################################################################
#
#   Is ramified
#
################################################################################

function is_ramified(R::RelNumFieldOrder, p::T) where T <: Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal, ZZRingElem, Int}
  @assert is_prime(p)
  D = prime_decomposition(R, p)
  for (_, e) in D
    if e > 1
      return true
    end
  end
  return false
end
