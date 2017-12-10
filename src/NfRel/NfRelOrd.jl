# I don't like that we have to drag S around
# Still hoping for julia/#18466

mutable struct NfRelOrdSet{T}
  nf::RelativeExtension{T}

  function NfRelOrdSet{T}(K::RelativeExtension{T}) where {T}
    a = new(K)
    return a
  end
end

mutable struct NfRelOrd{T, S} <: Ring
  nf::RelativeExtension{T}
  basis_nf::Vector{RelativeElement{T}}
  basis_mat::Generic.Mat{T}
  basis_mat_inv::Generic.Mat{T}
  basis_pmat::PMat{T, S}
  pseudo_basis::Vector{Tuple{RelativeElement{T}, S}}

  disc_abs::NfOrdIdl # used if T == nf_elem
  disc_rel#::NfRelOrdIdl{T} # used otherwise; is a forward declaration
  parent::NfRelOrdSet{T}

  isequation_order::Bool

  ismaximal::Int                   # 0 Not known
                                   # 1 Known to be maximal
                                   # 2 Known to not be maximal

  trace_mat::Generic.Mat{T}

  inv_coeff_ideals::Vector{S}

  function NfRelOrd{T, S}(K::RelativeExtension{T}) where {T, S}
    z = new{T, S}()
    z.nf = K
    z.parent = NfRelOrdSet{T}(K)
    z.isequation_order = false
    z.ismaximal = 0
    return z
  end

  function NfRelOrd{T, S}(K::RelativeExtension{T}, M::PMat{T, S}) where {T, S}
    z = NfRelOrd{T, S}(K)
    z.nf = K
    z.parent = NfRelOrdSet{T}(K)
    z.basis_pmat = M
    z.basis_mat = M.matrix
    return z
  end

  function NfRelOrd{T, S}(K::RelativeExtension{T}, M::Generic.Mat{T}) where {T, S}
    z = NfRelOrd{T, S}(K)
    z.nf = K
    z.parent = NfRelOrdSet{T}(K)
    z.basis_mat = M
    z.basis_pmat = pseudo_matrix(M)
    return z
  end
end

################################################################################
#
#  Basic field access
#
################################################################################

doc"""
***
      nf(O::NfRelOrd) -> RelativeExtension

> Returns the ambient number field of $\mathcal O$.
"""
nf(O::NfRelOrd) = O.nf

doc"""
    parent(O::NfRelOrd) -> NfRelOrdSet

Returns the parent of $\mathcal O$, that is, the set of orders of the ambient
number field.
"""
parent(O::NfRelOrd) = O.parent

doc"""
    isequation_order(O::NfRelOrd) -> Bool

> Returns whether $\mathcal O$ is the equation order of the ambient number
> field.
"""
isequation_order(O::NfRelOrd) = O.isequation_order

ismaximal_known(O::NfRelOrd) = O.ismaximal != 0

ismaximal(O::NfRelOrd) = O.ismaximal == 1

issimple(O::NfRelOrd) = issimple(nf(O))

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_basis_pmat(O::NfRelOrd{T, S}) where {T, S}
  if isdefined(O, :basis_pmat)
    return nothing
  end
  if !isdefined(O, :pseudo_basis)
    error("No pseudo_basis and no basis_pmat defined.")
  end
  pb = pseudo_basis(O, Val{false})
  L = nf(O)
  M = zero_matrix(base_ring(L), degree(O), degree(O))
  C = Vector{S}()
  for i = 1:degree(O)
    elem_to_mat_row!(M, i, pb[i][1])
    push!(C, deepcopy(pb[i][2]))
  end
  O.basis_pmat = PseudoMatrix(M, C)
  return nothing
end

function assure_has_pseudo_basis(O::NfRelOrd{T, S}) where {T, S}
  if isdefined(O, :pseudo_basis)
    return nothing
  end
  if !isdefined(O, :basis_pmat)
    error("No pseudo_basis and no basis_pmat defined.")
  end
  P = basis_pmat(O, Val{false})
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

function assure_has_basis_mat(O::NfRelOrd)
  if isdefined(O, :basis_mat)
    return nothing
  end
  O.basis_mat = basis_pmat(O).matrix
  return nothing
end

function assure_has_basis_mat_inv(O::NfRelOrd)
  if isdefined(O, :basis_mat_inv)
    return nothing
  end
  O.basis_mat_inv = inv(basis_mat(O, Val{false}))
  return nothing
end

function assure_has_inv_coeff_ideals(O::NfRelOrd)
  if isdefined(O, :inv_coeff_ideals)
    return nothing
  end
  pb = pseudo_basis(O, Val{false})
  O.inv_coeff_ideals = [ inv(pb[i][2]) for i in 1:degree(O) ]
  return nothing
end

################################################################################
#
#  Pseudo basis / basis pseudo-matrix
#
################################################################################

doc"""
***
      pseudo_basis(O::NfRelOrd{T, S}) -> Vector{Tuple{RelativeElement{T}{T}, S}}

> Returns the pseudo-basis of $\mathcal O$.
"""
function pseudo_basis(O::NfRelOrd, copy::Type{Val{T}} = Val{true}) where T
  assure_has_pseudo_basis(O)
  if copy == Val{true}
    return deepcopy(O.pseudo_basis)
  else
    return O.pseudo_basis
  end
end

doc"""
***
      basis_pmat(O::NfRelOrd) -> PMat

> Returns the basis pseudo-matrix of $\mathcal O$ with respect to the power basis
> of the ambient number field.
"""
function basis_pmat(O::NfRelOrd, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_pmat(O)
  if copy == Val{true}
    return deepcopy(O.basis_pmat)
  else
    return O.basis_pmat
  end
end

doc"""
***
      inv_coeff_ideals(O::NfRelOrd{T, S}) -> Vector{S}

> Returns the inverses of the coefficient ideals of the pseudo basis of $O$.
"""
function inv_coeff_ideals(O::NfRelOrd, copy::Type{Val{T}} = Val{true}) where T
  assure_has_inv_coeff_ideals(O)
  if copy == Val{true}
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

doc"""
***
      basis_nf(O::NfRelOrd) -> Array{RelativeElement, 1}

> Returns the elements of the pseudo-basis of $\mathcal O$ as elements of the
> ambient number field.
"""
function basis_nf(O::NfRelOrd, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_nf(O)
  if copy == Val{true}
    return deepcopy(O.basis_nf)
  else
    return O.basis_nf
  end
end

doc"""
***
      basis_mat(O::NfRelOrd{T, S}) -> Generic.Mat{T}

> Returns the basis matrix of $\mathcal O$ with respect to the power basis
> of the ambient number field.
"""
function basis_mat(O::NfRelOrd, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat(O)
  if copy == Val{true}
    return deepcopy(O.basis_mat)
  else
    return O.basis_mat
  end
end

doc"""
***
      basis_mat_inv(O::NfRelOrd{T, S}) -> Generic.Mat{T}

> Returns the inverse of the basis matrix of $\mathcal O$.
"""
function basis_mat_inv(O::NfRelOrd, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat_inv(O)
  if copy == Val{true}
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
  if ismaximal_known(O) && ismaximal(O)
    print(io, "Relative maximal order of ")
  else
    print(io, "Relative order of ")
  end
  println(io, nf(O))
  print(io, "with pseudo-basis ")
  pb = pseudo_basis(O, Val{false})
  for i = 1:degree(O)
    print(io, "\n(")
    print(io, pb[i][1])
    print(io, ", ")
    showcompact(io, pb[i][2])
    print(io, ")")
  end
end

################################################################################
#
#  Discriminant
#
################################################################################

function assure_has_discriminant(O::NfRelOrd{nf_elem, S}) where S
  if isdefined(O, :disc_abs)
    return nothing
  end
  d = det(trace_matrix(O))
  pb = pseudo_basis(O, Val{false})
  a = pb[1][2]^2
  for i = 2:degree(O)
    a *= pb[i][2]^2
  end
  disc = d*a
  simplify(disc)
  O.disc_abs = numerator(disc)
  return nothing
end

function discriminant(O::NfRelOrd{nf_elem, S}) where S
  assure_has_discriminant(O)
  return deepcopy(O.disc_abs)
end

function assure_has_discriminant(O::NfRelOrd{RelativeElement{T}, S}) where {T, S}
  if isdefined(O, :disc_rel)
    return nothing
  end
  d = det(trace_matrix(O))
  pb = pseudo_basis(O, Val{false})
  a = pb[1][2]^2
  for i = 2:degree(O)
    a *= pb[i][2]^2
  end
  disc = d*a
  simplify(disc)
  O.disc_rel = numerator(disc)
  return nothing
end

function discriminant(O::NfRelOrd{RelativeElement{T}, S}) where {T, S}
  assure_has_discriminant(O)
  return deepcopy(O.disc_rel)
end

################################################################################
#
#  Degree
#
################################################################################

doc"""
***
      degree(O::NfRelOrd) -> Int

> Returns the degree of $\mathcal O$.
"""
degree(O::NfRelOrd) = degree(nf(O))

################################################################################
#
#  Deepcopy
#
################################################################################

doc"""
***
      deepcopy(O::NfRelOrd) -> NfRelOrd

> Makes a copy of $\mathcal O$.
"""
function Base.deepcopy_internal(O::NfRelOrd{T, S}, dict::ObjectIdDict) where {T, S}
  z = NfRelOrd{T, S}(O.nf)
  for x in fieldnames(O)
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

function _check_elem_in_order(a::RelativeElement{T}, O::NfRelOrd{T, S}, short::Type{Val{V}} = Val{false}) where {T, S, V}
  b_pmat = basis_pmat(O, Val{false})
  t = zero_matrix(base_ring(nf(O)), 1, degree(O))
  elem_to_mat_row!(t, 1, a)
  t = t*basis_mat_inv(O, Val{false})
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
    v = Vector{T}(degree(O))
    for i in 1:degree(O)
      v[i] = deepcopy(t[1, i])
    end
    return true, v
  end
end

doc"""
***
      in(a::RelativeElement, O::NfRelOrd) -> Bool

> Checks whether $a$ lies in $\mathcal O$.
"""
function in(a::RelativeElement{T}, O::NfRelOrd{T, S}) where {T, S}
  return _check_elem_in_order(a, O, Val{true})
end

################################################################################
#
#  Construction
#
################################################################################

doc"""
***
      Order(K::RelativeExtension{T}, M::Generic.Mat{T}) -> NfRelOrd

> Returns the order which has basis matrix $M$ with respect to the power basis
> of $K$.
"""
function Order(L::RelativeExtension{nf_elem}, M::Generic.Mat{nf_elem})
  # checks
  return NfRelOrd{nf_elem, NfOrdFracIdl}(L, deepcopy(M))
end

function Order(L::RelativeExtension{S}, M::Generic.Mat{S}) where S <: RelativeElement{T} where T
  # checks
  return NfRelOrd{elem_type(base_ring(L)), NfRelOrdFracIdl{T}}(L, deepcopy(M))
end

doc"""
***
      Order(K::RelativeExtension, M::PMat) -> NfRelOrd

> Returns the order which has basis pseudo-matrix $M$ with respect to the power basis
> of $K$.
"""
function Order(L::RelativeExtension{T}, M::PMat{T, S}) where {T, S}
  # checks
  return NfRelOrd{T, S}(L, deepcopy(M))
end

doc"""
***
      EquationOrder(L::RelativeExtension) -> NfRelOrd

> Returns the equation order of the number field $L$.
"""
function EquationOrder(L::RelativeExtension)
  M = identity_matrix(base_ring(L), degree(L))
  O = Order(L, M)
  O.basis_mat_inv = M
  O.isequation_order = true
  return O
end

doc"""
***
      MaximalOrder(L::RelativeExtension) -> NfRelOrd

> Returns the maximal order of $L$.
"""
function MaximalOrder(L::RelativeExtension)
  O = EquationOrder(L)
  return MaximalOrder(O)
end

maximal_order(L::RelativeExtension) = MaximalOrder(L)

function maximal_order_via_absolute(L::NfRel)
  Labs, lToLabs, kToLabs = absolute_field(L)
  Oabs = MaximalOrder(Labs)
  return relative_order(Oabs, lToLabs)
end

function maximal_order_via_absolute(m::NfRelToNf)
  Oabs = MaximalOrder(codomain(m))
  return relative_order(Oabs, m)
end

################################################################################
#
#  Equality
#
################################################################################

function ==(R::NfRelOrd, S::NfRelOrd)
  nf(R) != nf(S) && return false
  return basis_pmat(R, Val{false}) == basis_pmat(S, Val{false})
end

################################################################################
#
#  Trace matrix
#
################################################################################

doc"""
***
      trace_matrix(O::NfRelOrd{T, S}) -> Generic.Mat{T}

> Returns the trace matrix of $\mathcal O$.
"""
function trace_matrix(O::NfRelOrd)
  if isdefined(O, :trace_mat)
    return deepcopy(O.trace_mat)
  end
  L = nf(O)
  K = base_ring(L)
  b = basis_nf(O, Val{false})
  d = degree(L)
  g = zero_matrix(K, d, d)
  for i = 1:d
    t = trace(b[i]*b[i])
    g[i, i] = t
    for j = (i + 1):d
      t = trace(b[i]*b[j])
      g[i, j] = t
      g[j, i] = t
    end
  end
  O.trace_mat = g
  return deepcopy(g)
end

################################################################################
#
#  Dedekind criterion
#
################################################################################

function nf_elem_poly_to_fq_nmod_poly(R::FqNmodPolyRing, m::NfToFqNmodMor, f::Generic.Poly{nf_elem})
  @assert codomain(m) == base_ring(R)
  @assert domain(m) == base_ring(parent(f))

  g = zero(R)
  for i = 0:degree(f)
    setcoeff!(g, i, m(coeff(f, i)))
  end
  return g
end

function fq_nmod_poly_to_nf_elem_poly(R::Generic.PolyRing{nf_elem}, m::InverseMap, f::fq_nmod_poly)
  @assert codomain(m) == base_ring(R)
  @assert domain(m) == base_ring(parent(f))

  g = zero(R)
  for i = 0:degree(f)
    setcoeff!(g, i, m(coeff(f, i)))
  end
  return g
end

# Algorithm IV.6. in "Berechnung relativer Ganzheitsbasen mit dem
# Round-2-Algorithmus" by C. Friedrichs.
function dedekind_test(O::NfRelOrd, p::NfOrdIdl, compute_order::Type{Val{S}} = Val{true}) where S
  !isequation_order(O) && error("Order must be an equation order")
  !issimple(O) && error("Not implemented for non-simple extensions")

  L = nf(O)
  K = base_ring(L)
  T = L.pol
  Kx = parent(T)
  OK = maximal_order(K)
  F, mF = ResidueField(OK, p)
  mmF = extend(mF, K)
  immF = inv(mmF)
  Fy, y = F["y"]

  Tmodp = nf_elem_poly_to_fq_nmod_poly(Fy, mmF, T)
  fac = factor(Tmodp)
  g = Kx(1)
  for (t, e) in fac
    mul!(g, g, fq_nmod_poly_to_nf_elem_poly(Kx, immF, t))
  end
  gmodp = nf_elem_poly_to_fq_nmod_poly(Fy, mmF, g)
  hmodp = divexact(Tmodp, gmodp)
  h = fq_nmod_poly_to_nf_elem_poly(Kx, immF, hmodp)
  a = anti_uniformizer(p)
  f = a*(g*h - T)
  fmodp = nf_elem_poly_to_fq_nmod_poly(Fy, mmF, f)

  d = gcd(fmodp, gcd(gmodp, hmodp))

  if compute_order == Val{false}
    return isone(d)
  else
    if isone(d)
      return true, O
    end

    Umodp = divexact(Tmodp, d)
    U = fq_nmod_poly_to_nf_elem_poly(Kx, immF, Umodp)
    PM = PseudoMatrix(representation_mat(a*U(gen(L))), [ frac_ideal(OK, OK(1)) for i = 1:degree(O) ])
    PN = vcat(basis_pmat(O), PM)
    PN = sub(pseudo_hnf(PN, :lowerleft, true), degree(O) + 1:2*degree(O), 1:degree(O))
    OO = Order(L, PN)
    OO.isequation_order = false
    return false, OO
  end
end

dedekind_ispmaximal(O::NfRelOrd, p::NfOrdIdl) = dedekind_test(O, p, Val{false})

dedekind_poverorder(O::NfRelOrd, p::NfOrdIdl) = dedekind_test(O, p)[2]

################################################################################
#
#  p-overorder
#
################################################################################

doc"""
***
      poverorder(O::NfRelOrd, p::NfOrdIdl) -> NfRelOrd

> This function tries to find an order that is locally larger than $\mathcal O$
> at the prime $p$.
"""
function poverorder(O::NfRelOrd, p::NfOrdIdl)
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

doc"""
***
    pmaximal_overorder(O::NfRelOrd, p::NfOrdIdl) -> NfRelOrd

> This function finds a $p$-maximal order $R$ containing $\mathcal O$.
"""
function pmaximal_overorder(O::NfRelOrd, p::NfOrdIdl)
  d = discriminant(O)
  OO = poverorder(O, p)
  dd = discriminant(OO)
  while d != dd
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

doc"""
***
      +(R::NfRelOrd, S::NfRelOrd) -> NfRelOrd

> Given two orders $R$, $S$ of $K$, this function returns the smallest order
> containing both $R$ and $S$.
"""
function +(a::NfRelOrd{T, S}, b::NfRelOrd{T, S}) where {T, S}
  # checks
  @assert nf(a) == nf(b)
  aB = basis_pmat(a)
  bB = basis_pmat(b)
  d = degree(a)
  PM = sub(pseudo_hnf(vcat(aB, bB), :lowerleft, true), d + 1:2*d, 1:d)
  return NfRelOrd{T, S}(nf(a), PM)
end

################################################################################
#
#  Absolute to relative
#
################################################################################

function relative_order(O::NfOrd, m::NfRelToNf)
  L = domain(m)
  Labs = codomain(m)
  @assert nf(O) == Labs
  K = base_ring(L)
  OK = MaximalOrder(K)
  mm = inv(m)
  B = basis(O, Val{false})
  d = degree(L)
  dabs = degree(Labs)
  M = zero_matrix(K, dabs, d)
  for i = 1:dabs
    elem_to_mat_row!(M, i, mm(Labs(B[i])))
  end
  PM = sub(pseudo_hnf(PseudoMatrix(M), :lowerleft, true), (dabs - d + 1):dabs, 1:d)
  return NfRelOrd{typeof(PM.matrix[1, 1]), typeof(PM.coeffs[1])}(L, PM)
end
