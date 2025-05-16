
################################################################################
#
#  Parent
#
################################################################################

parent(a::RelNumFieldOrderIdeal) = a.parent

function check_parent(x::RelNumFieldOrderIdeal, y::RelNumFieldOrderIdeal)
   if order(x) !== order(y)
     error("Ideals do not have the same order.")
   end
end

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_pseudo_basis(a::Union{RelNumFieldOrderIdeal, RelNumFieldOrderFractionalIdeal})
  if isdefined(a, :pseudo_basis)
    return nothing
  end
  if !isdefined(a, :basis_pmatrix)
    error("No pseudo_basis and no basis_pmatrix defined.")
  end
  P = basis_pmatrix(a, copy = false)
  B = basis_nf(order(a), copy = false)
  L = nf(order(a))
  K = base_field(L)
  pseudo_basis = Vector{Tuple{elem_type(L), fractional_ideal_type(order_type(K))}}()
  for i = 1:nrows(P)
    t = L()
    for j = 1:degree(L)
      t += P.matrix[i, j]*B[j]
    end
    push!(pseudo_basis, (t, deepcopy(P.coeffs[i])))
  end
  a.pseudo_basis = pseudo_basis
  return nothing
end

function assure_has_basis_matrix(a::Union{RelNumFieldOrderIdeal, RelNumFieldOrderFractionalIdeal})
  if isdefined(a, :basis_matrix)
    return nothing
  end
  a.basis_matrix = basis_pmatrix(a).matrix
  return nothing
end

function assure_has_basis_mat_inv(a::Union{RelNumFieldOrderIdeal, RelNumFieldOrderFractionalIdeal})
  if isdefined(a, :basis_mat_inv)
    return nothing
  end
  a.basis_mat_inv = inv(basis_matrix(a, copy = false))
  return nothing
end

################################################################################
#
#  Pseudo basis / basis pseudo-matrix
#
################################################################################

@doc raw"""
      pseudo_basis(a::RelNumFieldOrderIdeal{T, S}) -> Vector{Tuple{NumFieldElem{T}, S}}
      pseudo_basis(a::RelNumFieldOrderFractionalIdeal{T, S}) -> Vector{Tuple{NumFieldElem{T}, S}}

Returns the pseudo-basis of $a$.
"""
function pseudo_basis(a::Union{RelNumFieldOrderIdeal, RelNumFieldOrderFractionalIdeal}; copy::Bool = true)
  assure_has_pseudo_basis(a)
  if copy
    return deepcopy(a.pseudo_basis)
  else
    return a.pseudo_basis
  end
end

@doc raw"""
      basis_pmatrix(a::RelNumFieldOrderIdeal) -> PMat
      basis_pmatrix(a::RelNumFieldOrderFractionalIdeal) -> PMat

Returns the basis pseudo-matrix of $a$.
"""
function basis_pmatrix(a::Union{RelNumFieldOrderIdeal, RelNumFieldOrderFractionalIdeal}; copy::Bool = true)
  if copy
    return deepcopy(a.basis_pmatrix)
  else
    return a.basis_pmatrix
  end
end

# For compatibility with AlgAssRelOrdIdl
function basis_pmatrix_wrt(a::Union{ RelNumFieldOrderIdeal, RelNumFieldOrderFractionalIdeal }, O::RelNumFieldOrder; copy::Bool = true)
  @assert O === order(a)
  return basis_pmatrix(a, copy = copy)
end

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

@doc raw"""
      basis_matrix(a::RelNumFieldOrderIdeal{T, S}) -> Generic.Mat{T}
      basis_matrix(a::RelNumFieldOrderFractionalIdeal{T, S}) -> Generic.Mat{T}

Returns the basis matrix of $a$.
"""
function basis_matrix(a::Union{RelNumFieldOrderIdeal, RelNumFieldOrderFractionalIdeal}; copy::Bool = true)
  assure_has_basis_matrix(a)
  if copy
    return deepcopy(a.basis_matrix)
  else
    return a.basis_matrix
  end
end

@doc raw"""
      basis_mat_inv(a::RelNumFieldOrderIdeal{T, S}) -> Generic.Mat{T}
      basis_mat_inv(a::RelNumFieldOrderFractionalIdeal{T, S}) -> Generic.Mat{T}

Returns the inverse of the basis matrix of $a$.
"""
function basis_mat_inv(a::Union{RelNumFieldOrderIdeal, RelNumFieldOrderFractionalIdeal}; copy::Bool = true)
  assure_has_basis_mat_inv(a)
  if copy
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

function show(io::IO, a::RelNumFieldOrderIdeal)
  compact = get(io, :compact, false)
  if compact
    print(io, "Ideal with basis pseudo-matrix\n")
    show(IOContext(io, :compact => true), basis_pmatrix(a, copy = false))
  else
    print(io, "Ideal of\n")
    show(IOContext(io, :compact => true), order(a))
    print(io, "\nwith basis pseudo-matrix\n")
    show(IOContext(io, :compact => true), basis_pmatrix(a, copy = false))
  end
end

################################################################################
#
#  Parent object overloading and user friendly constructors
#
################################################################################

function defines_ideal(O::RelNumFieldOrder{T, S}, M::PMat{T, S}) where {T, S}
  K = base_field(nf(O))
  coeffs = basis_pmatrix(O, copy = false).coeffs
  I = pseudo_matrix(identity_matrix(K, degree(O)), deepcopy(coeffs))
  return _spans_subset_of_pseudohnf(M, I, shape = :lowerleft)
end

@doc raw"""
    ideal(O::RelNumFieldOrder, M::PMat; check::Bool = true, M_in_hnf::Bool = false) -> RelNumFieldOrderIdeal

Creates the ideal of $\mathcal O$ with basis pseudo-matrix $M$. If `check` is set,
then it is checked whether $M$ defines an ideal. If `M_in_hnf` is set, then it is
assumed that $M$ is already in lower left pseudo HNF.
"""
function ideal(O::RelNumFieldOrder{T, S, U}, M::PMat{T, S}; check::Bool = true, M_in_hnf::Bool = false) where {T, S, U}
  if check
    !defines_ideal(O, M) && error("The pseudo-matrix does not define an ideal.")
  end
  !M_in_hnf ? M = pseudo_hnf(M, :lowerleft, true) : nothing
  return RelNumFieldOrderIdeal{T, S, U}(O, M)
end

@doc raw"""
    ideal(O::RelNumFieldOrder, M::Generic.Mat; check::Bool = true) -> RelNumFieldOrderIdeal

Creates the ideal of $\mathcal O$ with basis matrix $M$. If `check` is set,
then it is checked whether $M$ defines an ideal.
"""
function ideal(O::RelNumFieldOrder{T, S}, M::Generic.Mat{T}; check::Bool = true) where {T, S}
  coeffs = deepcopy(basis_pmatrix(O, copy = false).coeffs)
  return ideal(O, pseudo_matrix(M, coeffs), check)
end

@doc raw"""
    ideal(O::RelNumFieldOrder{T, S}, x::RelSimpleNumFieldElem{T}, y::RelSimpleNumFieldElem{T}, a::S, b::S; check::Bool = true) -> RelNumFieldOrderIdeal{T, S}

Creates the ideal $x\cdot a + y\cdot b$ of $\mathcal O$. If `check` is set,
then it is checked whether these elements define an ideal.
"""
function ideal(O::RelNumFieldOrder{T, S, U}, x::U, y::U, a::S, b::S; check::Bool = true) where {T, S, U}
  d = degree(O)
  pb = pseudo_basis(O, copy = false)
  M = zero_matrix(base_field(nf(O)), 2*d, d)
  C = Array{S}(undef, 2*d)
  for i = 1:d
    elem_to_mat_row!(M, i, pb[i][1]*x)
    C[i] = pb[i][2]*a
  end
  for i = (d + 1):2*d
    elem_to_mat_row!(M, i, pb[i - d][1]*y)
    C[i] = pb[i - d][2]*b
  end
  M = M*basis_mat_inv(O, copy = false)
  PM = pseudo_matrix(M, C)
  if check
    !defines_ideal(O, PM) && error("The elements do not define an ideal.")
  end
  PM = sub(pseudo_hnf(PM, :lowerleft), (d + 1):2*d, 1:d)
  return RelNumFieldOrderIdeal{T, S, U}(O, PM)
end

function ideal(O::RelNumFieldOrder{T, S}, x::NumFieldElem{T}, y::NumFieldElem{T}, a::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, b::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}; check::Bool = true) where {T, S}
  aa = fractional_ideal(order(a), a, ZZRingElem(1))
  bb = fractional_ideal(order(b), b, ZZRingElem(1))
  return ideal(O, x, y, aa, bb; check)
end

function ideal(O::RelNumFieldOrder{T, S}, x::NumFieldElem{T}, y::NumFieldElem{T}, a::RelNumFieldOrderIdeal, b::RelNumFieldOrderIdeal; check::Bool = true) where {T, S}
  aa = fractional_ideal(order(a), basis_pmatrix(a); M_in_hnf=true)
  bb = fractional_ideal(order(b), basis_pmatrix(b); M_in_hnf=true)
  return ideal(O, x, y, aa, bb; check)
end

@doc raw"""
    ideal(O::RelNumFieldOrder{T, S}, x::RelNumFieldOrderElem{T}) -> RelNumFieldOrderIdeal{T, S}
    *(O::RelNumFieldOrder{T, S}, x::RelNumFieldOrderElem{T}) -> RelNumFieldOrderIdeal{T, S}
    *(x::RelNumFieldOrderElem{T}, O::RelNumFieldOrder{T, S}) -> RelNumFieldOrderIdeal{T, S}

Creates the ideal $x\cdot \mathcal O$ of $\mathcal O$.
"""
function ideal(O::RelNumFieldOrder{T, S, U}, x::RelNumFieldOrderElem{T, U}) where {T, S, U}
  x = O(x)
  K = base_field(nf(O))
  d = degree(O)
  pb = pseudo_basis(O, copy = false)
  if iszero(x)
    return RelNumFieldOrderIdeal{T, S, U}(O, pseudo_matrix(zero_matrix(K, 0, d), S[]))
  end
  M = zero_matrix(K, d, d)
  for i = 1:d
    elem_to_mat_row!(M, i, pb[i][1]*nf(O)(x))
  end
  M = M*basis_mat_inv(O, copy = false)
  PM = pseudo_matrix(M, S[ pb[i][2] for i = 1:d ])
  PM = pseudo_hnf(PM, :lowerleft)
  return RelNumFieldOrderIdeal{T, S, U}(O, PM)
end

function ideal(O::RelNumFieldOrder, x::Union{ Int, ZZRingElem, AbsSimpleNumFieldOrderElem})
  return ideal(O, O(x))
end

*(O::RelNumFieldOrder, x::T) where { T <: Union{ Int, ZZRingElem, AbsSimpleNumFieldOrderElem, RelNumFieldOrderElem } } = ideal(O, x)

*(x::T, O::RelNumFieldOrder) where { T <: Union{ Int, ZZRingElem, AbsSimpleNumFieldOrderElem, RelNumFieldOrderElem } } = ideal(O, x)

@doc raw"""
    ideal(O::RelNumFieldOrder{T, S}, a::S; check::Bool = true) -> RelNumFieldOrderIdeal{T, S}

Creates the ideal $a \cdot \mathcal O$ of $\mathcal O$. If `check` is set,
then it is checked whether $a$ defines an (integral) ideal.
"""
function ideal(O::RelNumFieldOrder{T, S, U}, a::S; check::Bool = true) where {T, S, U}
  d = degree(O)
  pb = pseudo_basis(O, copy = false)
  if iszero(a)
    M = zero_matrix(base_field(nf(O)), d, d)
    PM = pseudo_matrix(M, S[ a*pb[i][2] for i = 1:d ])
    return RelNumFieldOrderIdeal{T, S, U}(O, PM)
  end

  M = identity_matrix(base_field(nf(O)), d)
  PM = pseudo_matrix(M, S[ a*pb[i][2] for i = 1:d ])
  if check
    !defines_ideal(O, PM) && error("The coefficient ideal does not define an ideal.")
  end
  PM = pseudo_hnf(PM, :lowerleft)
  return RelNumFieldOrderIdeal{T, S, U}(O, PM)
end

function ideal(O::RelNumFieldOrder{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal}, a::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}; check::Bool = true)
  aa = fractional_ideal(order(a), a, ZZRingElem(1))
  return ideal(O, aa; check)
end

function ideal(O::RelNumFieldOrder, a::RelNumFieldOrderIdeal; check::Bool = true)
  @assert order(a) == order(pseudo_basis(O, copy = false)[1][2])

  aa = fractional_ideal(order(a), basis_pmatrix(a); M_in_hnf=true)
  return ideal(O, aa; check)
end

*(O::RelNumFieldOrder{T, S, U}, a::S) where {T, S <: Union{AbsSimpleNumFieldOrderFractionalIdeal, RelNumFieldOrderFractionalIdeal}, U} = fractional_ideal(O, a)

*(a::S, O::RelNumFieldOrder{T, S}) where {T, S <: Union{AbsSimpleNumFieldOrderFractionalIdeal, RelNumFieldOrderFractionalIdeal}} = fractional_ideal(O, a)

*(O::RelNumFieldOrder, a::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal}) = ideal(O, a)

*(a::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal}, O::RelNumFieldOrder) = ideal(O, a)

function fractional_ideal(O::RelNumFieldOrder{T, S, U}, a::S) where {T, S, U}
  d = degree(O)
  pb = pseudo_basis(O, copy = false)
  if iszero(a)
    M = zero_matrix(base_field(nf(O)), 0, d)
    PM = pseudo_matrix(M, S[])
    return RelNumFieldOrderFractionalIdeal{T, S, U}(O, PM)
  end

  M = identity_matrix(base_field(nf(O)), d)
  PM = pseudo_matrix(M, S[ a*pb[i][2] for i = 1:d ])
  PM = pseudo_hnf(PM, :lowerleft)
  return RelNumFieldOrderFractionalIdeal{T, S, U}(O, PM)
end

################################################################################
#
#  Powering
#
################################################################################

function ^(A::RelNumFieldOrderIdeal, a::Int)
  if a == 0
    B = one(order(A)) * order(A)
    return B
  end

  if a == 1
    return A # copy?
  end

  if a < 0
    error("Exponent must be positive")
  end

  if a == 2
    return A*A
  end

  if mod(a, 2) == 0
    return (A^div(a, 2))^2
  else
    return A * A^(a - 1)
  end
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::RelNumFieldOrderIdeal{T, S, U}, dict::IdDict) where {T, S, U}
  z = RelNumFieldOrderIdeal{T, S, U}(a.order)
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

function copy(a::RelNumFieldOrderIdeal)
  return a
end

################################################################################
#
#  Equality
#
################################################################################

function ==(a::RelNumFieldOrderIdeal, b::RelNumFieldOrderIdeal)
  order(a) !== order(b) && return false
  return basis_pmatrix(a, copy = false) == basis_pmatrix(b, copy = false)
end

################################################################################
#
#  Is prime
#
################################################################################

function is_prime(P::RelNumFieldOrderIdeal)
  if isone(P.is_prime)
    return true
  elseif P.is_prime == 2
    return false
  end
  p = minimum(P)
  if !is_prime(p)
    P.is_prime = 2
    return false
  end
  OK = order(P)
  lP = prime_decomposition(OK, p)
  for (Q, v) in lP
    if Q == P
      P.is_prime = 1
      P.splitting_type = Q.splitting_type
      return true
    end
  end
  P.is_prime = 2
  return false
end


################################################################################
#
#  iszero/isone
#
################################################################################

iszero(a::RelNumFieldOrderIdeal) = nrows(basis_matrix(a, copy = false)) == 0

isone(a::RelNumFieldOrderIdeal) = isone(minimum(a))

################################################################################
#
#  Norm
#
################################################################################

# Assumes, that det(basis_matrix(a)) == 1
function assure_has_norm(a::RelNumFieldOrderIdeal{T, S}) where {T, S}
  if a.has_norm
    return nothing
  end
  if iszero(a)
    O = base_ring(order(a))
    a.norm = O()*O
    a.has_norm = true
    return nothing
  end
  c = basis_pmatrix(a, copy = false).coeffs
  d = inv_coeff_ideals(order(a), copy = false)
  n = c[1]*d[1]
  for i = 2:degree(order(a))
    n *= c[i]*d[i]
  end
  if T == AbsSimpleNumFieldElem
    simplify(n)
    @assert n.den == 1
    a.norm = n.num
  else
    @assert denominator(n) == 1
    a.norm = ideal_type(order(n))(order(n), basis_pmatrix(n, copy = false))
  end
  a.has_norm = true
  return nothing
end

@doc raw"""
    norm(a::RelNumFieldOrderIdeal) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

Returns the norm of $a$.
"""
function norm(a::RelNumFieldOrderIdeal{T, S, U}; copy::Bool = true) where {T, S, U}
  assure_has_norm(a)
  if copy
    return deepcopy(a.norm)::ideal_type(order_type(parent_type(T)))
  else
    return a.norm::ideal_type(order_type(parent_type(T)))
  end
end

function norm(a::RelNumFieldOrderIdeal, k::NumField)
  n = norm(a)
  if nf(order(n)) != k
    return norm(n, k)::elem_type(k)
  end
  return n::elem_type(k)
end

function norm(a::RelNumFieldOrderIdeal, k::QQField)
  return norm(norm(a), k)
end

################################################################################
#
#  Ideal addition / GCD
#
################################################################################

function +(a::RelNumFieldOrderIdeal{T, S}, b::RelNumFieldOrderIdeal{T, S}) where {T, S}
  check_parent(a, b)

  if is_zero(a)
    return b
  end

  if is_zero(b)
    return a
  end

  d = degree(order(a))
  H = vcat(basis_pmatrix(a, copy = false), basis_pmatrix(b, copy = false))

  if T === AbsSimpleNumFieldElem
    m = (norm(a) + norm(b)) * _modulus(order(a))
    H = sub(pseudo_hnf_full_rank_with_modulus!(H, m, :lowerleft), (d + 1):2*d, 1:d)
  else
    H = sub(pseudo_hnf(H, :lowerleft), (d + 1):2*d, 1:d)
  end
  return ideal(order(a), H; check=false, M_in_hnf=true)
end

gcd(a::RelNumFieldOrderIdeal{T, S}, b::RelNumFieldOrderIdeal{T, S}) where {T, S} = a + b

################################################################################
#
#  Ideal multiplication
#
################################################################################

function *(a::RelNumFieldOrderIdeal{T, S}, b::RelNumFieldOrderIdeal{T, S}) where {T, S}
  check_parent(a, b)
  if iszero(a) || iszero(b)
    return order(a)()*order(a)
  end
  pba = pseudo_basis(a, copy = false)
  pbb = pseudo_basis(b, copy = false)
  ma = basis_matrix(a, copy = false)
  mb = basis_matrix(b, copy = false)
  L = nf(order(a))
  K = base_field(L)
  d = degree(order(a))
  M = zero_matrix(K, d^2, d)
  C = Vector{fractional_ideal_type(order_type(K))}(undef, d^2)
  t = L()
  for i = 1:d
    for j = 1:d
      t = mul!(t, pba[i][1], pbb[j][1])
      elem_to_mat_row!(M, (i - 1)*d + j, t)
      C[(i - 1)*d + j] = simplify(pba[i][2]*pbb[j][2])
    end
  end
  PM = pseudo_matrix(M, C)
  PM.matrix = PM.matrix*basis_mat_inv(order(a), copy = false)
  if T == AbsSimpleNumFieldElem
    m = norm(a)*norm(b) * _modulus(order(a))
    H = sub(pseudo_hnf_full_rank_with_modulus!(PM, m, :lowerleft), (d*(d - 1) + 1):d^2, 1:d)
  else
    H = sub(pseudo_hnf(PM, :lowerleft), (d*(d - 1) + 1):d^2, 1:d)
  end
  return ideal(order(a), H; check=false, M_in_hnf=true)
end

################################################################################
#
#  Ad hoc multiplication
#
################################################################################

function *(a::RelNumFieldOrderIdeal{T, S, U}, x::T) where {T <: NumFieldElem, S, U <: NumFieldElem}
  if iszero(x)
    return ideal(order(a), 0)
  end

  return ideal(order(a), x*basis_pmatrix(a); M_in_hnf=true)
end

*(x::T, a::RelNumFieldOrderIdeal{T, S, U}) where {T <: NumFieldElem, S, U <: NumFieldElem} = a*x

function *(a::Union{RelNumFieldOrderIdeal, RelNumFieldOrderFractionalIdeal}, x::Union{ Int, ZZRingElem })
  if iszero(x)
    return ideal(order(a), 0)
  end

  return typeof(a)(order(a), x*basis_pmatrix(a))
end

*(x::Union{ Int, ZZRingElem}, a::Union{RelNumFieldOrderIdeal, RelNumFieldOrderFractionalIdeal}) = a*x

################################################################################
#
#  Intersection / LCM
#
################################################################################

function intersect(a::RelNumFieldOrderIdeal{T, S}, b::RelNumFieldOrderIdeal{T, S}) where {T, S}
  check_parent(a, b)
  d = degree(order(a))
  Ma = basis_pmatrix(a)
  Mb = basis_pmatrix(b)
  M1 = hcat(Ma, deepcopy(Ma))
  z = zero_matrix(base_ring(Ma.matrix), d, d)
  M2 = hcat(pseudo_matrix(z, Mb.coeffs), Mb)
  M = vcat(M1, M2)
  if T === AbsSimpleNumFieldElem
    m = intersect(norm(a), norm(b)) * _modulus(order(a))
    H = sub(pseudo_hnf_full_rank_with_modulus!(M, m, :lowerleft), 1:d, 1:d)
  else
    H = sub(pseudo_hnf(M, :lowerleft), 1:d, 1:d)
  end
  return ideal(order(a), H; check=false, M_in_hnf=true)
end

################################################################################
#
#  Inverse
#
################################################################################

function inv(a::Union{RelNumFieldOrderIdeal{T, S}, RelNumFieldOrderFractionalIdeal{T, S}}) where {T, S}
  if !is_maximal(order(a))
    error("Not implemented (yet).")
  end
  @assert !iszero(a)
  O = order(a)
  d = degree(O)
  pb = pseudo_basis(a, copy = false)
  bmO = basis_matrix(O, copy = false)
  bmOinv = basis_mat_inv(O, copy = false)
  M = bmO*representation_matrix(pb[1][1])*bmOinv
  for i = 2:d
    M = hcat(M, bmO*representation_matrix(pb[i][1])*bmOinv)
  end
  invcoeffs = inv_coeff_ideals(O, copy = false)
  C = Array{S}(undef, d^2)
  for i = 1:d
    for j = 1:d
      C[(i - 1)*d + j] = simplify(pb[i][2]*invcoeffs[j])
    end
  end
  PM = pseudo_matrix(transpose(M), C)
  PM = sub(pseudo_hnf(PM, :upperright, true), 1:d, 1:d)
  N = inv(transpose(PM.matrix))
  PN = pseudo_matrix(N, [ simplify(inv(I)) for I in PM.coeffs ])
  PN = pseudo_hnf(PN, :lowerleft, true)
  return fractional_ideal(O, PN; M_in_hnf=true)
end

################################################################################
#
#  Division
#
################################################################################

function divexact(a::RelNumFieldOrderIdeal{T, S}, b::RelNumFieldOrderIdeal{T, S}; check::Bool=true) where {T, S}
  O = order(a)
  return fractional_ideal(O, basis_pmatrix(a, copy = false); M_in_hnf=true)*inv(b)
end

//(a::RelNumFieldOrderIdeal{T, S}, b::RelNumFieldOrderIdeal{T, S}) where {T, S} = divexact(a, b)


//(a::RelNumFieldOrderIdeal{T,S}, z::ZZRingElem) where {T, S} = a//(z*order(a))

//(a::RelNumFieldOrderIdeal{T,S}, n::Integer) where {T, S} = a//(ZZ(n)*order(a))

################################################################################
#
#  IsPower function
#
################################################################################


function is_power(I::RelNumFieldOrderIdeal)
  m = minimum(I)
  if isone(m)
    return 0, I
  end
  OL = order(I)
  d = discriminant(OL)
  b, a = ppio(m, d) # hopefully: gcd(a, d) = 1 = gcd(a, b) and ab = m

  e, JJ = is_power_unram(gcd(I, ideal(OL, a)))

  if isone(e)
    return 1, I
  end

  g = e
  J = ideal(OL, 1)
  lp = factor(b)
  for p = keys(lp)
    lP = prime_decomposition(order(I), p)
    for i=1:length(lP)
      P = lP[i][1]
      v = valuation(I, P)
      gn = gcd(v, g)
      if gn == 1
        return gn, I
      end
      if g != gn
        J = J^div(g, gn)
      end
      if v != 0
        J *= P^div(v, gn)
      end
      g = gn
    end
  end
  return g, JJ^div(e, g)*J
end

function is_power_unram(I::RelNumFieldOrderIdeal{S, T, U})::Tuple{Int, RelNumFieldOrderIdeal{S, T, U}} where {S, T, U}
  m = minimum(I)
  if isone(m)
    return (0, I)
  end
  OL = order(I)

  e, ra = is_power(m)
  J = gcd(I, ideal(OL, ra))

  II = J^e//I
  II = simplify(II)
  @assert isone(denominator(II))

  f, s = is_power_unram(numerator(II)::RelNumFieldOrderIdeal{S, T, U})
  g = gcd(f, e)
  if isone(g)
    return 1, I
  end

  II = inv(s)^div(f, g) * J^div(e, g)
  II = simplify(II)
  @assert isone(denominator(II))
  JJ = numerator(II)
  e = g

  return e, JJ
end

################################################################################
#
#  P-radical
#
################################################################################

# Returns an element x of a with v_p(x) = v_p(a) for all p in primes.
function element_with_valuation(a::T, primes::Vector{T}) where {T <: Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal}}
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




#computes a^e mod the integer p. Assumes that the base field of parent(a)
# has a nice defining equation
function _powermod(a::S, e::T, p::ZZRingElem) where {S <: Union{RelSimpleNumFieldElem, RelNonSimpleNumFieldElem}, T <: IntegerUnion}
  @assert e >= 0
  K = parent(a)
  if iszero(e)
    return one(K)
  end
  b = mod(a, p)
  if isone(e)
    return b
  end
  if iseven(e)
    c = _powermod(b, div(e, 2), p)
    mul!(c, c, c)
    c = mod(c, p)
    return c
  else
    c = _powermod(b, e-1, p)
    mul!(c, c, b)
    c = mod(c, p)
    return c
  end
end

# Algorithm V.8. and VI.8. in "Berechnung relativer Ganzheitsbasen mit dem
# Round-2-Algorithmus" by C. Friedrichs.
@doc raw"""
      pradical(O::RelNumFieldOrder, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> RelNumFieldOrderIdeal

Given a prime ideal $P$, this function returns the $P$-radical
$\sqrt{P\mathcal O}$ of $\mathcal O$, which is
just $\{ x \in \mathcal O \mid \exists k \in \mathbf Z_{\geq 0} \colon x^k
\in P\mathcal O \}$. It is not checked that $P$ is prime.
"""
function pradical(O::RelNumFieldOrder, P::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal})
  d = degree(O)
  L = nf(O)
  K = base_field(L)
  OK = maximal_order(K)
  pb = pseudo_basis(O, copy = false)

  is_absolute = (typeof(K) == AbsSimpleNumField)

  # Compute a pseudo basis of O with integral ideals:
  basis_mat_int = zero_matrix(K, d, d)
  pbint = Vector{Tuple{elem_type(L), typeof(P)}}()
  for i = 1:d
    t = divexact(pb[i][1], denominator(pb[i][2]))
    if is_absolute
      push!(pbint, (t, numerator(pb[i][2], copy = false)))
    else
      push!(pbint, (t, numerator(pb[i][2])))
    end
    elem_to_mat_row!(basis_mat_int, i, t)
  end
  if is_absolute
    Oint = typeof(O)(L, pseudo_matrix(basis_mat_int, [ fractional_ideal(OK, pbint[i][2], ZZRingElem(1)) for i = 1:d ]))
  else
    Oint = typeof(O)(L, pseudo_matrix(basis_mat_int, [ fractional_ideal(OK, basis_pmatrix(pbint[i][2], copy = false)) for i = 1:d ]))
  end

  pOK = minimum(P, copy = false)*OK
  prime_ideals = factor(pOK)

  elts_with_val = Vector{elem_type(OK)}(undef, d)
  for i = 1:d
    elts_with_val[i] = element_with_valuation(pbint[i][2], [ p for (p, e) in prime_ideals ])
  end
  F, mF = residue_field(OK, P)
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
    k = clog(ZZRingElem(degree(Oint)), q)
    for i = 1:d
      t = Oint((L(K(elts_with_val[i]))*pbint[i][1])^(q^k))
      ar = coordinates(t, copy = false)
      for j = 1:d
        A[j, i] = mmF(divexact(ar[j], K(elts_with_val[j])))
      end
    end
  else
    for i = 1:d
      for j = i:d
        t = L(K(elts_with_val[i]))*pbint[i][1]*L(K(elts_with_val[j]))*pbint[j][1]
        A[i, j] = mF(OK(tr(t)))
        A[j, i] = A[i, j]
      end
    end
  end

  B = kernel(A, side = :right)
  M1 = zero_matrix(K, d, d)
  imF = pseudo_inv(mF)
  # Write a basis of the kernel of A in the rows of M1.
  for j = 1:nrows(B)
    t = K(denominator(pb[j][2], copy = false))
    for i = 1:ncols(B)
      M1[i, j] = divexact(K(imF(B[j, i])*elts_with_val[j]), t)
    end
  end
  PM1 = pseudo_matrix(M1)
  PM2 = pseudo_matrix(identity_matrix(K, d), [ pb[i][2]*P for i = 1:d ])
  PM = sub(pseudo_hnf(vcat(PM1, PM2), :lowerleft, true), (d + 1):2*d, 1:d)

  return ideal(O, PM; check=false, M_in_hnf=true)
end

function pradical(O::RelNumFieldOrder{S, T, U}, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) where {S, T, U <: Union{RelNonSimpleNumFieldElem{AbsSimpleNumFieldElem}, RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}}
  d = degree(O)
  L = nf(O)
  K = base_field(L)
  OK = maximal_order(K)
  pb = pseudo_basis(O, copy = false)
  @vprintln :RelNumFieldOrder 4 "Computing a pseudo basis of O with integral ideals"
  basis_mat_int = zero_matrix(K, d, d)
  pbint = Vector{Tuple{elem_type(L), AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}}()
  for i = 1:d
    t = divexact(pb[i][1], denominator(pb[i][2]))
    push!(pbint, (t, numerator(pb[i][2])))
    elem_to_mat_row!(basis_mat_int, i, t)
  end
  Oint = typeof(O)(L, pseudo_matrix(basis_mat_int, [ fractional_ideal(OK, pbint[i][2], ZZRingElem(1)) for i = 1:d ]))

  pOK = ideal(OK, OK(minimum(P)))
  prime_ideals = factor(pOK)
  kprimes = collect(keys(prime_ideals))

  elts_with_val = Vector{AbsSimpleNumFieldElem}(undef, d)
  for i = 1:d
    elts_with_val[i] = element_with_valuation(pbint[i][2], kprimes).elem_in_nf
  end
  F, mF = residue_field(OK, P)
  mmF = extend(mF, K)
  A = zero_matrix(F, d, d)

  # If the prime number in P is too small one can't use the trace.
  p = minimum(P)
  if p <= d
    @vprintln :RelNumFieldOrder 4 "Frobenius method"
    q = order(F)
    k = clog(ZZRingElem(degree(Oint)), q)
    for i = 1:d
      if is_defining_polynomial_nice(K)
        t = Oint(_powermod(elts_with_val[i]*pbint[i][1], q^k, p))
      else
        t = Oint((elts_with_val[i]*pbint[i][1])^(q^k))
      end
      ar = coordinates(t, copy = false)
      for j = 1:d
        A[j, i] = mmF(divexact(ar[j], elts_with_val[j]))
      end
    end
  else
    @vprintln :RelNumFieldOrder 4 "Trace method"
    for i = 1:d
      for j = i:d
        t = elts_with_val[i]*pbint[i][1]*elts_with_val[j]*pbint[j][1]
        A[i, j] = mF(OK(tr(t)))
        A[j, i] = A[i, j]
      end
    end
  end
  @vprintln :RelNumFieldOrder 4 "Computing nullspace"
  B = kernel(A, side = :right)
  @vprintln :RelNumFieldOrder 4 "Lifting nullspace"
  M1 = zero_matrix(K, nrows(B), d)
  imF = pseudo_inv(mF)
  # Write a basis of the kernel of A in the rows of M1.
  for j = 1:nrows(B)
    t = denominator(pb[j][2], copy = false)
    for i = 1:ncols(B)
      if !iszero(B[j, i])
        elM1 = imF(B[j, i]).elem_in_nf
        mul!(elM1, elM1, elts_with_val[j])
        divexact!(elM1, elM1, t)
        M1[i, j] = mod(elM1, p)
      end
    end
  end
  @vprintln :RelNumFieldOrder 4 "Final hnf"
  PM1 = pseudo_matrix(M1)
  PM2 = pseudo_matrix(identity_matrix(K, d), [ pb[i][2]*P for i = 1:d ])
  PM = vcat(PM2, PM1)
  if isdefined(O, :index)
    PM = sub(pseudo_hnf_full_rank_with_modulus!(PM, O.index*P, :lowerleft), (d + 1):2*d, 1:d)
  else
    PM = sub(pseudo_hnf_full_rank(PM, :lowerleft), (d + 1):2*d, 1:d)
  end

  return ideal(O, PM; check=false, M_in_hnf=true)

end

################################################################################
#
#  Ring of multipliers
#
################################################################################

# Algorithm VII.1. in "Berechnung relativer Ganzheitsbasen mit dem
# Round-2-Algorithmus" by C. Friedrichs.
function ring_of_multipliers(a::RelNumFieldOrderIdeal{T1, T2, T3}) where {T1, T2, T3}
  O = order(a)
  K = base_field(nf(O))
  d = degree(O)
  pb = pseudo_basis(a, copy = false)
  S = basis_mat_inv(O, copy = false)*basis_mat_inv(a, copy = false)
  M = representation_matrix(pb[1][1])*S
  for i = 2:d
    M = hcat(M, representation_matrix(pb[i][1])*S)
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
  PM = pseudo_matrix(transpose(M), C)
  if T1 == AbsSimpleNumFieldElem && isdefined(O, :index)
    PM = sub(pseudo_hnf_full_rank_with_modulus!(PM, O.index*minimum(a, copy = false), :upperright), 1:d, 1:d)
  else
    PM = sub(pseudo_hnf(PM, :upperright, true), 1:d, 1:d)
  end

  N = inv(transpose(PM.matrix))
  PN = pseudo_matrix(N, [ simplify(inv(I)) for I in PM.coeffs ])
  res = typeof(O)(nf(O), PN)
  if T1 == AbsSimpleNumFieldElem && isdefined(O, :index)
    res.index = O.index*minimum(a, copy = false)
  end
  return res
end




################################################################################
#
#  Absolute to relative
#
################################################################################

function relative_ideal(a::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, m::NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}})
  L = codomain(m)
  Labs = domain(m)
  @assert nf(order(a)) == Labs
  K = base_field(L)
  O = relative_order(order(a), m)
  B = basis(a, copy = false)
  d = degree(L)
  dabs = degree(Labs)
  M = zero_matrix(K, dabs, d)
  for i = 1:dabs
    elem_to_mat_row!(M, i, m(Labs(B[i])))
  end
  M = M*basis_mat_inv(O, copy = false)
  PM = sub(pseudo_hnf(pseudo_matrix(M), :lowerleft, true), (dabs - d + 1):dabs, 1:d)
  return ideal(O, PM; check=false, M_in_hnf=true)
end

################################################################################
#
#  Index divisors
#
################################################################################

function is_index_divisor(O::RelNumFieldOrder{S, T, U}, p::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal}) where {S, T, U <: RelSimpleNumFieldElem}
  f = nf(O).pol
  return valuation(discriminant(f), p) != valuation(discriminant(O), p)
end

function is_index_divisor(O::RelNumFieldOrder{S, T, U}, p::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal}) where {S, T, U <: RelNonSimpleNumFieldElem}
  I = discriminant(O)
  J = discriminant(equation_order(nf(O)))
  return valuation(I, p) != valuation(J, p)
end

################################################################################
#
#  Prime decomposition
#
################################################################################

function prime_decomposition(O::RelNumFieldOrder, p::T) where T <: IntegerUnion
  lP = prime_decomposition(base_ring(O), p)
  res = Vector{Tuple{ideal_type(O), Int}}()
  for (P, e) in lP
    lPP = prime_decomposition(O, P)
    for (Q, e1) in lPP
      push!(res, (Q, e*e1))
    end
  end
  return res
end


function prime_decomposition(O::RelNumFieldOrder, p::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal}; compute_uniformizer::Bool = true, compute_anti_uniformizer::Bool = true)
  if !is_simple(nf(O)) || is_index_divisor(O, p)
    ls = prime_dec_index(O, p)
  else
    ls = prime_dec_nonindex(O, p, compute_uniformizer = compute_uniformizer)
  end

  #if compute_anti_uniformizer
  #  for (P,_) in ls
  #    anti_uniformizer(P)
  #  end
  #end

  return ls
end

function prime_dec_nonindex(O::RelNumFieldOrder, p::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal}; compute_uniformizer::Bool = true)
  L = nf(O)
  OK = order(p)
  @assert OK == O.basis_pmatrix.coeffs[1].order
  @assert OK.is_maximal == 1
  a = gen(L)
  K = base_field(L)
  f = L.pol

  Kx = parent(f)
  Fp, mF = residue_field(OK, p)
  mmF = extend(mF, K)
  immF = pseudo_inv(mmF)
  Fy, y = polynomial_ring(Fp,"y", cached=false)
  fmodp = map_coefficients(mmF, f, parent = Fy)
  fac = factor(fmodp)
  result = Vector{Tuple{ideal_type(O), Int}}()
  for (q, e) in fac
    g = Hecke.fq_poly_to_nf_elem_poly(Kx, immF, q)
    ga = g(a)
    P = ideal(O, L(1), ga, p, OK(1)*OK)
    P.is_prime = 1
    P.splitting_type = (e, degree(q))
    P.minimum = deepcopy(p)
    P.non_index_div_poly = q
    Oga = O(ga)
    if compute_uniformizer
      # TODO: Warum funktioniert das? Muss uniformizer(p) ein p-uniformizer sein?
      if iszero(Oga)
        @assert e == 1
        P.p_uniformizer = O(uniformizer(p))
      else
        if e != 1
          P.p_uniformizer = Oga
        else
          if !(Oga in P^2) # Otherwise we have a recursion. valuation(Oga, P) == 1
            @assert Oga in P
            P.p_uniformizer = Oga
          else
            P.p_uniformizer = Oga + O(uniformizer(p))
          end
        end
      end
    end
    push!(result, (P, e))
  end
  return result
end

function prime_dec_index(O::RelNumFieldOrder, p::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal})
  if haskey(O.index_div, p)
    return O.index_div[p]::Vector{Tuple{ideal_type(O), Int}}
  end

  L = nf(O)
  K = base_field(L)
  pbasisO = pseudo_basis(O, copy = false)
  pO = p*O

  Ip = pradical(O, p)
  A, OtoA = StructureConstantAlgebra(O, Ip, p)
  AtoO = pseudo_inv(OtoA)
  AA = decompose(A)

  result = Vector{Tuple{ideal_type(O), Int}}()
  m = pseudo_matrix(zero_matrix(K, 1, degree(O)))
  for (B, BtoA) in AA
    f = dim(B)
    idem = BtoA(B[1]) # Assumes that B == idem*A
    M = representation_matrix(idem)
    ker = kernel(M, side = :left)
    N = basis_pmatrix(Ip)
    for i = 1:nrows(ker)
      b = coordinates(AtoO(A(ker[i, :])))
      for j = 1:degree(O)
        m.matrix[1, j] = b[j]
      end
      N = vcat(N, deepcopy(m))
    end
    N = sub(pseudo_hnf(N, :lowerleft), nrows(N) - degree(O) + 1:nrows(N), 1:degree(O))
    P = ideal(O, N; check=false, M_in_hnf=true)
    P.is_prime = 1
    e = _valuation_for_prime_decomposition(pO, P)
    P.splitting_type = (e, f)
    P.minimum = deepcopy(p)
    push!(result, (P, e))
  end

  O.index_div[p] = result
  return result
end

# Returns all prime ideals in O containing the prime number p
function prime_ideals_over(O::RelNumFieldOrder, p::Union{ Int, ZZRingElem })
  pdec = prime_ideals_over(base_ring(O), p)

  primes = Vector{ideal_type(O)}()
  for q in pdec
    qdec = prime_decomposition(O, q)
    append!(primes, ideal_type(O)[ qdec[i][1] for i = 1:length(qdec) ])
  end

  return primes
end

################################################################################
#
#  Reduction of element modulo ideal
#
################################################################################

function mod!(a::RelNumFieldOrderElem, I::RelNumFieldOrderIdeal)
  O = order(I)
  b = coordinates(a, copy = false)
  PM = basis_pmatrix(I, copy = false) # PM is assumed to be in lower left pseudo hnf
  t = parent(b[1])()
  t1 = parent(b[1])()
  for i = degree(O):-1:1
    t = add!(t, mod(b[i], PM.coeffs[i]), -b[i])
    for j = 1:i
      t1 = mul!(t1, t, PM.matrix[i, j])
      b[j] = add!(b[j], b[j], t1)
    end
  end

  t = nf(O)()
  B = basis_nf(O, copy = false)
  zero!(a.elem_in_nf)
  for i = 1:degree(O)
    t = mul!(t, B[i], nf(O)(b[i]))
    a.elem_in_nf = add!(a.elem_in_nf, a.elem_in_nf, t)
  end

  return a
end

function mod(a::RelNumFieldOrderElem, I::RelNumFieldOrderIdeal)
  return mod!(deepcopy(a), I)
end

function mod!(a::RelNumFieldOrderElem, Q::RelOrdQuoRing)
  return mod!(a, ideal(Q))
end

function mod(a::RelNumFieldOrderElem, Q::RelOrdQuoRing)
  return mod(a, ideal(Q))
end

################################################################################
#
#  Valuation
#
################################################################################

function _valuation_for_prime_decomposition(A::RelNumFieldOrderIdeal{T, S}, B::RelNumFieldOrderIdeal{T, S}) where {T, S}
  O = order(A)
  Afrac = fractional_ideal(O, basis_pmatrix(A); M_in_hnf=true)
  Bi = inv(B)
  i = 0
  C = Afrac*Bi
  @assert C != Afrac
  while is_integral(C)
    C = C*Bi
    i += 1
  end
  return i
end

function _valuation_for_prime_decomposition(A::RelNumFieldOrderElem, B::RelNumFieldOrderIdeal)
  return _valuation_for_prime_decomposition(A * order(B), B)
end

function valuation_naive(A::RelNumFieldOrderIdeal{T, S}, B::RelNumFieldOrderIdeal{T, S}) where {T, S}
  @assert order(A.basis_pmatrix.coeffs[1]) == order(B.basis_pmatrix.coeffs[1])
  @assert !iszero(A) && !iszero(B)
  p = minimum(B)
  if valuation(minimum(A), p) == 0
    return 0
  end
  # The strategy is as follows:
  # Let pi be a anti-uniformizer of B
  # We determine v with A_p * pi^v \subseteq O_p, where p is the minimum of B.
  # This is the valuation
  p = minimum(B)
  pbA = pseudo_basis(A, copy = false)
  adjusted_basis = elem_type(nf(order(A)))[]
  puni = elem_in_nf(uniformizer(p))
  panti = anti_uniformizer(p)
  for (a, c) in pbA
    v = valuation(c, p)
    if v < 0
      push!(adjusted_basis, puni^v * a)
      #@assert valuation(uniformizer(p)^-v * c, p) == 0
    elseif v > 0
      push!(adjusted_basis, panti^-v * a)
      #@assert valuation(anti_uniformizer(p)^v * c, p) == 0
    else
      push!(adjusted_basis, deepcopy(a))
    end
  end
  pi = anti_uniformizer(B)
  ii = -1
  #@show adjusted_basis
  found = false
  O = order(A)
  b_pmat = basis_pmatrix(O, copy = false)
  vals = Int[valuation(b_pmat.coeffs[i], p) for i in 1:length(adjusted_basis)]
  t = zero_matrix(base_field(nf(O)), 1, degree(O))
  bmatinv = basis_mat_inv(O, copy = false)
  while !found
    ii += 1
    for i in 1:length(adjusted_basis)
      newa = mul!(adjusted_basis[i], adjusted_basis[i], pi)
      elem_to_mat_row!(t, 1, newa)
      t = mul!(t, t, bmatinv)
      for i = 1:degree(O)
        if iszero(t[1, i])
          continue
        end
        if !(valuation(t[1, i], p) >= vals[i])
          return ii
        end
      end
    end
  end
  #else
  #  O = order(A)
  #  Afrac = fractional_ideal(O, basis_pmatrix(A); M_in_hnf=true)
  #  Bi = inv(B)
  #  i = 0
  #  C = Afrac*Bi
  #  @assert C != Afrac
  #  while is_integral(C)
  #    C = C*Bi
  #    i += 1
  #  end
  #  return i
  #end
end

valuation(A::RelNumFieldOrderIdeal{T, S}, B::RelNumFieldOrderIdeal{T, S}) where {T, S} = valuation_naive(A, B)

function valuation_naive(a::RelNumFieldOrderElem{T}, B::RelNumFieldOrderIdeal{T, S}) where {T, S}
  @assert !iszero(a)
  @assert order(parent(a).basis_pmatrix.coeffs[1]) == order(B.basis_pmatrix.coeffs[1])
  #@assert order((a * parent(a)).basis_pmatrix.coeffs[1]) == order(B.basis_pmatrix.coeffs[1])
  pi = anti_uniformizer(B)
  i = 0
  b = elem_in_nf(a)
  O = parent(a)
  while true
    b = b * pi
    if !(b in O)
      return i
    end
    i += 1
  end
  #return valuation(a * order(B), B)
end

valuation(a::RelNumFieldOrderElem{T}, B::RelNumFieldOrderIdeal{T, S}) where {T, S} = valuation_naive(a, B)

function valuation(a::IntegerUnion, B::RelNumFieldOrderIdeal)
  e = ramification_index(B)
  return valuation(a, minimum(B)) * e
end

################################################################################
#
#  Factorization into prime ideals
#
################################################################################

function factor(A::RelNumFieldOrderIdeal{T, S, U}) where {T, S, U}
  nn = norm(A)
  normFactors = factor(nn)
  n = fractional_ideal(order(nn), nn)
  result = Dict{RelNumFieldOrderIdeal{T, S, U}, Int}()
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

@doc raw"""
      minimum(A::RelNumFieldOrderIdeal) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
      minimum(A::RelNumFieldOrderIdeal) -> RelNumFieldOrderIdeal

Returns the ideal $A \cap O$ where $O$ is the maximal order of the coefficient
ideals of $A$.
"""
function minimum(A::RelNumFieldOrderIdeal{T, S, U}; copy::Bool = true) where {T, S, U}
  assure_has_minimum(A)
  if copy
    return deepcopy(A.minimum)::ideal_type(order_type(parent_type(T)))
  else
    return A.minimum::ideal_type(order_type(parent_type(T)))
  end
end

function assure_has_minimum(A::RelNumFieldOrderIdeal)
  if isdefined(A, :minimum)
    return nothing
  end
  if is_zero(A)
    O = base_ring(order(A))
    A.minimum = zero(O) * O
    return nothing
  end
  @assert isone(basis_pmatrix(A, copy = false).matrix[1, 1])
  @assert isone(basis_pmatrix(order(A), copy = false).matrix[1, 1])

  M = deepcopy(basis_pmatrix(A, copy = false).coeffs[1])
  M = simplify(M)
  A.minimum = numerator(M)
  return nothing
end

################################################################################
#
#  Order modulo prime ideal
#
################################################################################

function residue_field(O::RelNumFieldOrder{T, S, U}, P::RelNumFieldOrderIdeal{T, S, U}) where {T, S, U}
  @assert order(P) == O
  @assert P.is_prime == 1
  mF = NfRelOrdToFqMor(O, P)
  return codomain(mF), mF
end

################################################################################
#
#  Idempotents
#
################################################################################

function idempotents(x::RelNumFieldOrderIdeal{T, S}, y::RelNumFieldOrderIdeal{T, S}) where {T, S}
  check_parent(x, y)

  O = order(x)
  mx = minimum(x, copy = false)
  my = minimum(y, copy = false)
  g = mx + my
  if isone(g)
    u, v = idempotents(mx, my)
    return O(u), O(v)
  end

  d = degree(O)
  L = nf(O)
  K = base_field(L)
  OK = maximal_order(K)
  M = zero_matrix(K, 2*d + 1, 2*d + 1)

  M[1, 1] = K(1)
  z = coordinates(one(O))
  for i = 1:d
    M[1, i + 1] = z[i]
  end
  for i = 1:d
    for j = 1:d
      M[i + 1, j + 1] = deepcopy(basis_matrix(x, copy = false)[i, j])
      M[i + 1 + d, j + 1] = deepcopy(basis_matrix(y, copy = false)[i, j])
    end
    M[i + 1, i + d + 1] = K(1)
  end

  #=
    M is now
    ( 1 |  1  |  0  )
    ( 0 | M_x | I_d )
    ( 0 | M_y |  0  )
  =#

  coeffsx = deepcopy(basis_pmatrix(x, copy = false).coeffs)
  coeffsy = deepcopy(basis_pmatrix(y, copy = false).coeffs)
  C = [ K(1)*OK, coeffsx..., coeffsy... ]
  PM = pseudo_matrix(M, C)
  PM = pseudo_hnf(PM, :upperright)

  for i = 2:(d + 1)
    if !iszero(PM.matrix[1, i])
      error("Ideals are not coprime")
    end
  end

  pbx = pseudo_basis(x, copy = false)
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
#=
@doc raw"""
    in(x::RelNumFieldOrderElem, y::RelNumFieldOrderIdeal)
    in(x::NumFieldElem, y::RelNumFieldOrderIdeal)
    in(x::ZZRingElem, y::RelNumFieldOrderIdeal)

Returns whether $x$ is contained in $y$.
"""
=#
function in(x::RelNumFieldOrderElem, y::RelNumFieldOrderIdeal)
  parent(x) !== order(y) && error("Order of element and ideal must be equal")
  O = order(y)
  b_pmat = basis_pmatrix(y, copy = false)
  t = matrix(base_field(nf(O)), 1, degree(O), coordinates(x))
  t = t*basis_mat_inv(y, copy = false)
  for i = 1:degree(O)
    if !(t[1, i] in b_pmat.coeffs[i])
      return false
    end
  end
  return true
end

function in(x::NumFieldElem, y::RelNumFieldOrderIdeal)
  parent(x) !== nf(order(y)) && error("Number field of element and ideal must be equal")
  !_check_elem_in_order(x, order(y), Val(true)) && return false
  return in(order(y)(x, false),y)
end

in(x::ZZRingElem, y::RelNumFieldOrderIdeal) = in(order(y)(x),y)

################################################################################
#
#  (Anti-)Uniformizer
#
################################################################################

function _is_p_uniformizer(z::RelNumFieldOrderElem, P::T, P2::T, primes::Vector{T}) where {T <: RelNumFieldOrderIdeal}
  if iszero(z)
    return false
  end
  if !(z in P) || z in P^2# z valuation(z, P) != 1
    return false
  end
  for PP in primes
    if z in PP #if valuation(z, PP) != 0
      return false
    end
  end
  return true
end

function anti_uniformizer(P::RelNumFieldOrderIdeal{T, S}) where {T, S}
  @assert P.is_prime == 1

  if isdefined(P, :anti_uniformizer)
    return P.anti_uniformizer
  end

  p = minimum(P, copy = false)
  # We need a pseudo basis of O, where the coefficient ideals have valuation
  # 0 at p, so that we can work in the order(p)/p-vector space O/p*O.
  O = order(P)
  N = basis_matrix(O)
  NN = basis_mat_inv(O)
  d = Vector{T}(undef, degree(O))
  a = elem_in_nf(uniformizer(p))
  for i = 1:degree(O)
    v = valuation(pseudo_basis(O, copy = false)[i][2], p)
    if !iszero(v)
      d[i] = a^v
      mul_row!(N, i, d[i])
      mul_col!(NN, i, inv(d[i]))
    else
      d[i] = one(base_field(nf(O)))
    end
  end

  u = elem_in_nf(p_uniformizer(P))
  M = representation_matrix(u)
  M = N*M*NN

  F, mF = residue_field(order(p), p)
  mmF = extend(mF, nf(order(p)))
  immF = pseudo_inv(mmF)
  Mp = zero_matrix(F, nrows(M), ncols(M))
  for i = 1:nrows(M)
    for j = 1:ncols(M)
      Mp[i, j] = mmF(M[i, j])
    end
  end
  K = kernel(Mp, side = :left)
  @assert nrows(K) > 0
  x = nf(O)()
  pbO = pseudo_basis(O, copy = false)
  for i = 1:degree(O)
    # Construct a preimage of the i-th basis vector of O/p*O
    c = coprime_to(pbO[i][2]*inv(d[i]), p)
    b = immF(inv(mmF(c)))*c*pbO[i][1]*d[i]

    x += immF(K[1, i])*b
  end
  P.anti_uniformizer = x*anti_uniformizer(p)
  return P.anti_uniformizer
end

################################################################################
#
#  Random elements
#
################################################################################

function rand(a::RelNumFieldOrderIdeal, B::Int)
  pb = pseudo_basis(a, copy = false)
  z = nf(order(a))()
  for i = 1:degree(order(a))
    t = rand(pb[i][2], B)
    z += t*pb[i][1]
  end
  return order(a)(z)
end

################################################################################
#
#  Something with coprime
#
################################################################################

function coprime_to(I::RelNumFieldOrderFractionalIdeal, p::RelNumFieldOrderIdeal)
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

################################################################################
#
#  Hashing
#
################################################################################

function Base.hash(A::RelNumFieldOrderIdeal, h::UInt)
  return Base.hash(basis_pmatrix(A, copy = false), h)
end

################################################################################
#
#  Approximation
#
################################################################################

# See also approximate_nonnegative and approximate_simple in AbsSimpleNumFieldOrder/Ideal/Prime.jl

# Returns x in K such that v_p(x) = v[i] for p = primes[i] and v_p(x) \geq 0 for all other primes p.
# Algorithm 1.7.8 in Hoppe: Normal forms over Dedekind domains
function approximate(v::Vector{Int}, primes::Vector{ <: RelNumFieldOrderIdeal })
  @assert length(v) == length(primes)
  @assert length(primes) > 0

  O = order(primes[1])

  # Make the set primes complete: add all prime ideals lying over the same prime numbers
  prime_numbers = Set{ZZRingElem}()
  for p in primes
    push!(prime_numbers, prime_number(p))
  end

  primes2 = Vector{ideal_type(O)}()
  for p in prime_numbers
    pdec = prime_ideals_over(O, p)
    append!(primes2, pdec)
  end

  v2 = zeros(Int, length(primes2))

  D = Dict([ (primes[i], v[i]) for i = 1:length(primes) ])

  for i = 1:length(primes2)
    if haskey(D, primes2[i])
      v2[i] = D[primes2[i]]
    end
  end

  a_pos, a_neg = _approximate_simple(v2, primes2)

  # Take care of the additional negative valuations coming from a_neg^(-1)
  c = QQFieldElem(absolute_norm(a_neg))
  for i = 1:length(primes)
    if v[i] >= 0
      continue
    end

    c *= QQFieldElem(absolute_norm(primes[i]))^v[i]
  end

  return divexact(c*elem_in_nf(a_pos), elem_in_nf(a_neg))
end

################################################################################
#
#  Prime ideals up to
#
################################################################################

function prime_ideals_up_to(O::RelNumFieldOrder, n::Union{Int, ZZRingElem})
  p = 2
  z = ideal_type(O)[]
  while p <= n
    lp = prime_decomposition(base_ring(O), p)
    for q in lp
      if norm(q[1]) > n
        continue
      else
        lq = prime_decomposition(O, q[1])
        for Q in lq
          if absolute_norm(Q[1]) <= n
            push!(z, Q[1])
          end
        end
      end
    end
    p = next_prime(p)
  end
  return sort!(z, by = a -> absolute_norm(a))
end
