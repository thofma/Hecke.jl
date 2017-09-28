mutable struct NfRelOrdIdlSet{T, S}
  order::NfRelOrd{T, S}

  function NfRelOrdIdlSet{T, S}(O::NfRelOrd{T, S}) where {T, S}
    a = new(O)
    return a
  end
end

mutable struct NfRelOrdIdl{T, S}
  order::NfRelOrd{T, S}
  parent::NfRelOrdIdlSet{T, S}
  basis_pmat::PMat{T, S}
  pseudo_basis::Vector{Tuple{NfRelElem{T}, S}}
  basis_mat::Generic.Mat{T}
  basis_mat_inv::Generic.Mat{T}

  norm
  has_norm::Bool

  function NfRelOrdIdl{T, S}(O::NfRelOrd{T, S}) where {T, S}
    z = new{T, S}()
    z.order = O
    z.parent = NfRelOrdIdlSet{T, S}(O)
    z.has_norm = false
    return z
  end

  function NfRelOrdIdl{T, S}(O::NfRelOrd{T, S}, M::PMat{T, S}) where {T, S}
    z = new{T, S}()
    z.order = O
    z.parent = NfRelOrdIdlSet{T, S}(O)
    z.basis_pmat = M
    z.basis_mat = M.matrix
    z.has_norm = false
    return z
  end

  function NfRelOrdIdl{T, S}(O::NfRelOrd{T, S}, M::Generic.Mat{T}) where {T, S}
    z = new{T, S}()
    z.order = O
    z.parent = NfRelOrdIdlSet{T, S}(O)
    z.basis_pmat = pseudo_matrix(M)
    z.basis_mat = M
    z.has_norm = false
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
    order(a::NfRelOrdIdl) -> NfRelOrd

> Returns the order of $a$.
"""
order(a::NfRelOrdIdl) = a.order

doc"""
***
    nf(a::NfRelOrdIdl) -> NfRel

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

function assure_has_basis_pmat(a::NfRelOrdIdl{T, S}) where {T, S}
  if isdefined(a, :basis_pmat)
    return nothing
  end
  if !isdefined(a, :pseudo_basis)
    error("No pseudo_basis and no basis_pmat defined.")
  end
  pb = pseudo_basis(a, Val{false})
  L = nf(order(a))
  M = MatrixSpace(base_ring(L), degree(L), degree(L))()
  C = Vector{S}()
  for i = 1:degree(L)
    elem_to_mat_row!(M, i, pb[i][1])
    push!(C, deepcopy(pb[i][2]))
  end
  M = M*basis_mat_inv(order(a), Val{false})
  a.basis_pmat = pseudo_hnf(PseudoMatrix(M, C), :lowerleft)
  return nothing
end

function assure_has_pseudo_basis(a::NfRelOrdIdl{T, S}) where {T, S}
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
  pseudo_basis = Vector{Tuple{NfRelElem{T}, S}}()
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

function assure_has_basis_mat(a::NfRelOrdIdl)
  if isdefined(a, :basis_mat)
    return nothing
  end
  a.basis_mat = basis_pmat(a).matrix
  return nothing
end

function assure_has_basis_mat_inv(a::NfRelOrdIdl)
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
      pseudo_basis(a::NfRelOrdIdl{T, S}) -> Vector{Tuple{NfRelElem{T}, S}}

> Returns the pseudo-basis of $a$.
"""
function pseudo_basis(a::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
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

> Returns the basis pseudo-matrix of $a$.
"""
function basis_pmat(a::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
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

> Returns the basis matrix of $a$.
"""
function basis_mat(a::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
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

> Returns the inverse of the basis matrix of $a$.
"""
function basis_mat_inv(a::NfRelOrdIdl, copy::Type{Val{T}} = Val{true}) where T
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
  print(io, "Ideal of (")
  print(io, order(a), ")\n")
  print(io, "with basis pseudo-matrix\n")
  print(io, basis_pmat(a, Val{false}))
end

################################################################################
#
#  Parent object overloading and user friendly constructors
#
################################################################################

doc"""
***
    ideal(O::NfRelOrd, M::PMat) -> NfRelOrdIdl

> Creates the ideal of $\mathcal O$ with basis pseudo-matrix $M$.
"""
function ideal(O::NfRelOrd{T, S}, M::PMat{T, S}) where {T, S}
  # checks
  H = pseudo_hnf(M, :lowerleft)
  return NfRelOrdIdl{T, S}(O, H)
end

doc"""
***
    ideal(O::NfRelOrd, M::Generic.Mat) -> NfRelOrdIdl

> Creates the ideal of $\mathcal O$ with basis matrix $M$.
"""
ideal(O::NfRelOrd{T, S}, M::Generic.Mat{T}) where {T, S} = ideal(O, PseudoMatrix(M))

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

function assure_has_norm(a::NfRelOrdIdl)
  if a.has_norm
    return nothing
  end
  c = basis_pmat(a, Val{false}).coeffs
  d = basis_pmat(order(a), Val{false}).coeffs
  n = c[1]*inv(d[1])
  for i = 2:degree(order(a))
    n *= c[i]*inv(d[i])
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

> Returns $a + b$.
"""
function +(a::NfRelOrdIdl{T, S}, b::NfRelOrdIdl{T, S}) where {T, S}
  d = degree(order(a))
  H = vcat(basis_pmat(a), basis_pmat(b))
  m = norm(a) + norm(b)
  H = sub(pseudo_hnf_mod(H, m, :lowerleft), (d + 1):2*d, 1:d)
  return NfRelOrdIdl{T, S}(order(a), H)
end

################################################################################
#
#  Ideal multiplication
#
################################################################################

doc"""
    *(a::NfRelOrdIdl, b::NfRelOrdIdl)

> Returns $a \cdot b$.
"""
function *(a::NfRelOrdIdl{T, S}, b::NfRelOrdIdl{T, S}) where {T, S}
  pba = pseudo_basis(a, Val{false})
  pbb = pseudo_basis(b, Val{false})
  L = nf(order(a))
  K = base_ring(L)
  d = degree(order(a))
  M = MatrixSpace(K, d^2, d)()
  C = Array{S, 1}(d^2)
  t = L()
  for i = 1:d
    for j = 1:d
      mul!(t, pba[i][1], pbb[i][1])
      elem_to_mat_row!(M, (i - 1)*d + j, t)
      C[(i - 1)*d + j] = pba[i][2]*pbb[i][2]
    end
  end
  m = norm(a)*norm(b)
  H = sub(pseudo_hnf_mod(PseudoMatrix(M, C), m, :lowerleft), (d*(d - 1) + 1):d^2, 1:d)
  return NfRelOrdIdl{T, S}(order(a), H)
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

> Returns $a \cap b$.
"""
function intersection(a::NfRelOrdIdl{T, S}, b::NfRelOrdIdl{T, S}) where {T, S}
  d = degree(order(a))
  Ma = basis_pmat(a)
  Mb = basis_pmat(b)
  M1 = hcat(Ma, deepcopy(Ma))
  z = zero(MatrixSpace(base_ring(Ma.matrix), d, d))
  M2 = hcat(PseudoMatrix(z, Mb.coeffs), Mb)
  M = vcat(M1, M2)
  m = intersection(norm(a), norm(b))
  H = sub(pseudo_hnf_mod(M, m, :lowerleft), 1:d, 1:d)
  return NfRelOrdIdl{T, S}(order(a), H)
end

################################################################################
#
#  P-radical
#
################################################################################

function pradical(O::NfRelOrd{nf_elem, NfOrdFracIdl}, p::NfOrdIdl)
  d = degree(O)
  L = nf(O)
  K = base_ring(L)
  OK = maximal_order(K)
  pb = pseudo_basis(O, Val{false})
  basis_mat_int = MatrixSpace(K, d, d)()
  pbint = Vector{Tuple{NfRelElem{nf_elem}, NfOrdIdl}}()
  for i = 1:d
    t = divexact(pb[i][1], den(pb[i][2]))
    push!(pbint, (t, deepcopy(num(pb[i][2]))))
    elem_to_mat_row!(basis_mat_int, i, t)
  end
  Oint = NfRelOrd{nf_elem, NfOrdFracIdl}(L, PseudoMatrix(basis_mat_int, [ frac_ideal(OK, pbint[i][2], fmpz(1)) for i = 1:d ]))
  pOK = ideal(OK, OK(minimum(p)))
  prime_ideals = factor(pOK)
  elts_max_val = Vector{NfOrdElem}(d)
  for i = 1:d
    products = Vector{NfOrdIdl}()
    for (prime, e) in prime_ideals
      push!(products, pbint[i][2]*prime)
    end
    while true
      a = rand(pbint[i][2], 2^61) # magic number
      foundOne = true
      for pp in products
        if a in pp
          foundOne = false
          break
        end
      end
      if foundOne
        elts_max_val[i] = a
        break
      end
    end
  end
  F, mF = ResidueField(OK, p)
  mmF = extend(mF, K)
  A = MatrixSpace(F, d, d)()
  if minimum(p) <= d
    q = norm(p)
    k = clog(fmpz(degree(Oint)), q)
    for i = 1:d
      t = Oint((L(K(elts_max_val[i]))*pbint[i][1])^(q^k))
      ar = elem_in_basis(t)
      for j = 1:d
        A[j, i] = mmF(divexact(ar[j], K(elts_max_val[j])))
      end
    end
  else
    for i = 1:d
      for j = i:d
        t = L(K(elts_max_val[i]))*pbint[i][1]*L(K(elts_max_val[j]))*pbint[j][1]
        A[i, j] = mF(OK(trace(t)))
        A[j, i] = deepcopy(A[i, j])
      end
    end
  end
  B = nullspace(A)[2]
  M1 = zero(MatrixSpace(OK, d, d))
  imF = inv(mF)
  for i = 1:cols(B)
    for j = 1:rows(B)
      M1[i, j] = imF(B[j, i])*elts_max_val[j]
    end
  end
  M2 = eye(M1)
  PM1 = PseudoMatrix(M1)
  PM2 = PseudoMatrix(M2, [ deepcopy(p) for i = 1:d ])
  PM = sub(pseudo_hnf(vcat(PM1, PM2), :lowerleft), (d + 1):2*d, 1:d) 
  return NfRelOrdIdl{nf_elem, NfOrdFracIdl}(Oint, PM)
end

################################################################################
#
#  Ring of multipliers
#
################################################################################

function ring_of_multipliers(a::NfRelOrdIdl{nf_elem, NfOrdFracIdl})
  O = order(a)
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
      C[(i - 1)*d + j] = simplify(pb[i][2]*invcoeffs[j])
    end
  end
  PM = PseudoMatrix(transpose(M), C)
  PM = try sub(pseudo_hnf(PM), 1:d, 1:d)
    catch sub(pseudo_hnf_kb(PM), 1:d, 1:d)
    end
  N = inv(transpose(PM.matrix))*basis_mat(O, Val{false})
  PN = PseudoMatrix(N, [ simplify(inv(I)) for I in PM.coeffs ])
  return NfRelOrd{nf_elem, NfOrdFracIdl}(nf(O), PN)
end
