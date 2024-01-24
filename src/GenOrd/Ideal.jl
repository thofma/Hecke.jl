################################################################################
#
#  Constructors
#
################################################################################

ideal(O::GenOrd, a::RingElement, b::RingElement) = GenOrdIdl(O, a, b)

ideal(O::GenOrd, a::RingElement) = GenOrdIdl(O, a)

ideal(O::GenOrd, a::MatElem) = GenOrdIdl(O, a)

function AbstractAlgebra.zero(a::GenOrdIdl)
  O = a.order
  return GenOrdIdl(O,O(0))
end

# TODO: fix me
AbstractAlgebra.iszero(I::GenOrdIdl) = (I.is_zero == 1)

has_2_elem(A::GenOrdIdl) = isdefined(A, :gen_two)

@doc raw"""
    isone(A::GenOrdIdl) -> Bool
    is_unit(A::GenOrdIdl) -> Bool

Tests if $A$ is the trivial ideal generated by $1$.
"""
function isone(I::GenOrdIdl)
  if isdefined(I, :norm)
    return isone(norm(I, copy = false))
  end
  return isone(minimum(I, copy = false))
end


################################################################################
#
#  Basic field access
#
################################################################################

@doc raw"""
    order(x::GenOrdIdl) -> GenOrd

Return the order, of which $x$ is an ideal.
"""
Hecke.order(a::GenOrdIdl) = a.order

################################################################################
#
#  Hash
#
################################################################################

function Base.hash(I::GenOrdIdl, h::UInt)
  b = 0x11ba13ff011affd1%UInt
  return xor(b, hash(basis_matrix(I, copy = false), h))
end

################################################################################
#
#  IO
#
################################################################################


function show(io::IO, id::GenOrdIdl)
  print(io, "Ideal of ", id.order)
  if has_2_elem(id)
    print(io, "\nGenerators: <", id.gen_one, ", ", id.gen_two, ">" )
  else
    print(io, "\nGenerators: <no 2-elts present>");
  end
  if has_norm(id)
    print(io, "\nNorm: ", id.norm);
  end
  if has_minimum(id)
    print(io, "\nMinimum: ", id.minimum);
  end
  if isdefined(id, :princ_gen)
    print(io, "\nPrincipal generator ", id.princ_gen)
  end
   if isdefined(id, :basis_matrix)
     print(io, "\nBasis_matrix \n", id.basis_matrix)
   end
end


###########################################################################################
#
#   Basis
#
###########################################################################################

@doc raw"""
    has_basis(A::GenOrdIdl) -> Bool

Return whether $A$ has a basis already computed.
"""
has_basis(A::GenOrdIdl) = isdefined(A, :basis)

function assure_has_basis(A::GenOrdIdl)
  if isdefined(A, :basis)
    return nothing
  else
    assure_has_basis_matrix(A)
    O = order(A)
    M = A.basis_matrix
    Ob = basis(O)
    B = Vector{elem_type(O)}(undef, degree(O))
    y = O()
    for i in 1:degree(O)
      z = O()
      for k in 1:degree(O)
        mul!(y,O(M[i, k]), Ob[k])
        add!(z, z, y)
      end
      B[i] = z
    end
    A.basis = B
    return nothing
  end
end

@doc raw"""
    basis(A::GenOrdIdl) -> Vector{GenOrdElem}

Return the basis of $A$.
"""
function Hecke.basis(A::GenOrdIdl; copy::Bool = true)
  assure_has_basis(A)
  if copy
    return deepcopy(A.basis)
  else
    return A.basis
  end
end


###########################################################################################
#
#   Basis Matrix
#
###########################################################################################

@doc raw"""
    basis_matrix(A::GenOrdIdl) -> Mat

Return the basis matrix of $A$.
"""
function Hecke.basis_matrix(A::GenOrdIdl; copy::Bool = true)
  assure_has_basis_matrix(A)
  if copy
    B = deepcopy(A.basis_matrix)
    return B
  else
    return A.basis_matrix
  end
end

function assure_has_basis_matrix(A::GenOrdIdl)
  if isdefined(A, :basis_matrix)
    return nothing
  end
  O = order(A)
  n = degree(O.F)

  if iszero(A)
    A.basis_matrix = zero_matrix(base_ring(O), n, n)
    return nothing
  end

  if has_princ_gen(A)
    A.basis_matrix = representation_matrix(A.princ_gen)
    return nothing
  end

  @hassert :NfOrd 1 has_2_elem(A)

  V = hnf(reduce(vcat, [representation_matrix(x) for x in [O(A.gen_one),A.gen_two]]),:lowerleft)
  d = ncols(V)
  A.basis_matrix = V[d+1:2*d,1:d]
  return nothing
end

################################################################################
#
#  Basis matrix inverse
#
################################################################################

@doc raw"""
    has_basis_mat_inv(A::GenOrdIdl) -> Bool

Return whether $A$ knows its inverse basis matrix.
"""
has_basis_mat_inv(A::GenOrdIdl) = isdefined(A, :basis_mat_inv)

@doc raw"""
    basis_mat_inv(A::GenOrdIdl) -> FakeFracFldMat

Return the inverse of the basis matrix of $A$.
"""
function Hecke.basis_mat_inv(A::GenOrdIdl{S, T}; copy::Bool = true) where {S, T}
  assure_has_basis_mat_inv(A)
  if copy
    return deepcopy(A.basis_mat_inv)::dense_matrix_type(elem_type(base_field(field(order(A)))))
  else
    return A.basis_mat_inv::dense_matrix_type(elem_type(base_field(field(order(A)))))
  end
end

function assure_has_basis_mat_inv(A::GenOrdIdl)
  if isdefined(A, :basis_mat_inv)
    return nothing
  else
    A.basis_mat_inv = inv(change_base_ring(base_field(field(order(A))), basis_matrix(A)))
    return nothing
  end
end

###########################################################################################
#
#   Misc
#
###########################################################################################


(O::GenOrd)(p::PolyRingElem) = O(O.F(p))
Hecke.is_commutative(O::GenOrd) = true

Nemo.elem_type(::Type{GenOrd}) = GenOrdElem

function Hecke.hnf(x::T, shape::Symbol =:upperright) where {T <: MatElem}
  if shape == :lowerleft
    h = hnf(reverse_cols(x))
    reverse_cols!(h)
    reverse_rows!(h)
    return h::T
  end
  return hnf(x)::T
end


################################################################################
#
#  Binary Operations
#
################################################################################


function Base.:(+)(a::GenOrdIdl, b::GenOrdIdl)
  @req order(a) === order(b) "Ideals must have same order"

  if iszero(a)
    return b
  end
  if iszero(b)
    return a
  end

  V = hnf(vcat(basis_matrix(a),basis_matrix(b)),:lowerleft)
  d = ncols(V)
  return GenOrdIdl(a.order, V[d+1:2*d,1:d])
end

Base.:(==)(a::GenOrdIdl, b::GenOrdIdl) = hnf(basis_matrix(a),:lowerleft) == hnf(basis_matrix(b),:lowerleft)
Base.isequal(a::GenOrdIdl, b::GenOrdIdl) = a == b

function Base.:(*)(a::GenOrdIdl, b::GenOrdIdl)
  O = order(a)
  Ma = basis_matrix(a)
  Mb = basis_matrix(b)
  V = hnf(reduce(vcat, [Mb*representation_matrix(O([Ma[i,o] for o in 1:ncols(Ma)])) for i in 1:ncols(Ma)]),:lowerleft)
  d = ncols(V)
  return GenOrdIdl(O, V[d*(d-1)+1:d^2,1:d])
end

@doc raw"""
    intersect(x::GenOrdIdl, y::GenOrdIdl) -> GenOrdIdl

Returns $x \cap y$.
"""
function Base.intersect(a::GenOrdIdl, b::GenOrdIdl)
#TODO: Check for new hnf
  M1 = hcat(basis_matrix(a), basis_matrix(a))
  d = nrows(M1)
  M2 = hcat(basis_matrix(b), zero_matrix(M1.base_ring,d,d))
  M = vcat(M1, M2)
  H = sub(hnf(M), d+1:2*d, d+1:2*d)
  return GenOrdIdl(a.order, H)
end

################################################################################
#
#  Powering
#
################################################################################

function Base.:(^)(A::GenOrdIdl, e::Int)
  O = order(A)
  if e == 0
    return GenOrdIdl(O, one(O))
  elseif e == 1
    return A
  elseif e < 0
    return inv(A)^(-e)
  end
  return Base.power_by_squaring(A, e)
end


################################################################################
#
#  Ad hoc multiplication
#
################################################################################

function Base.:*(x::GenOrdElem, O::GenOrd)
  return ideal(O, x)
end

function Base.:*(x::GenOrdElem, y::GenOrdIdl)
  parent(x) !== order(y) && error("GenOrds of element and ideal must be equal")
  return GenOrdIdl(parent(x), x) * y
end

Base.:*(x::GenOrdIdl, y::GenOrdElem) = y * x


function Hecke.colon(a::GenOrdIdl, b::GenOrdIdl)

  O = order(a)
  n = degree(O)
  if isdefined(b, :gens)
    B = b.gens
  else
    B = basis(b)
  end

  bmatinv = basis_mat_inv(a, copy = false)

  R = base_ring(bmatinv)

  n = change_base_ring(R, representation_matrix(B[1]))*bmatinv
  m, d = integral_split(n, coefficient_ring(O))
  for i in 2:length(B)
    n = change_base_ring(R, representation_matrix(B[i]))*bmatinv
    mm, dd = integral_split(n, coefficient_ring(O))
    l = lcm(dd, d)
    if l == d && l == dd
      m = hcat(m, mm)
    elseif l == d
      m = hcat(m, div(d, dd)*mm)
    elseif l == dd
      m = hcat(div(dd, d)*m, mm)
      d = dd
    else
      m = hcat(m*div(l, d), mm*div(l, dd))
      d = l
    end
  end
  m = transpose(m)
  m = hnf(m)
  # m is upper right HNF
  m = transpose(sub(m, 1:degree(O), 1:degree(O)))
  b = inv(divexact(change_base_ring(base_ring(field(O)), m), base_field(field(O))(d)))
  return GenOrdFracIdl(O, b)
end

# If I is not coprime to the conductor of O in the maximal order, then this might
# not be an inverse.
function inv(A::GenOrdIdl)
  O = order(A)
  return colon(O(1)*O, A)
end


################################################################################
#
#  Exact Division
#
################################################################################


function Hecke.divexact(A::GenOrdIdl, b::RingElem)
  if iszero(A)
    return A
  end
  O = order(A)
  if isa(b, KInftyElem)
    b = O.R(Hecke.AbstractAlgebra.MPolyFactor.make_monic(numerator(b))//denominator(b))
  elseif isa(b, PolyRingElem)
    b = Hecke.AbstractAlgebra.MPolyFactor.make_monic(b)
  end
  bm = divexact(basis_matrix(A), b)
  B = GenOrdIdl(O, bm)
  if false && has_basis_mat_inv(A)
    error("not defined at all")
    B.basis_mat_inv = b*A.basis_mat_inv
  end
  if has_princ_gen(A)
    B.princ_gen = O(divexact(O.F(A.princ_gen), b))
  end

  return B
end


function has_minimum(A::GenOrdIdl)
  return isdefined(A, :minimum)
end

function Hecke.minimum(A::GenOrdIdl; copy::Bool = true)
  assure_has_minimum(A)
  if copy
    return deepcopy(A.minimum)
  else
    return A.minimum
  end
end

function assure_has_minimum(A::GenOrdIdl)
  if has_minimum(A)
    return nothing
  end

  O = order(A)
  M = basis_matrix(A, copy = false)
  d = prod([M[i, i] for i = 1:nrows(M)])
  v = transpose(matrix(map(base_ring(O), coordinates(O(d)))))
  fl, s = can_solve_with_solution(M, v, side = :left)
  @assert fl
  den = denominator(s[1]//d)
  for i = 2:ncols(s)
    den = lcm(den, denominator(s[i]//d))
  end

  if isa(den, KInftyElem)
    A.minimum = O.R(Hecke.AbstractAlgebra.MPolyFactor.make_monic(numerator(den))//denominator(den))
  elseif isa(den, PolyRingElem)
    A.minimum = Hecke.AbstractAlgebra.MPolyFactor.make_monic(den)
  end

  return nothing
end

################################################################################
#
#  Norm
#
################################################################################

@doc raw"""
    has_norm(A::GenOrdIdl) -> Bool

Return whether $A$ knows its norm.
"""
function has_norm(A::GenOrdIdl)
  return isdefined(A, :norm)
end

function assure_has_norm(A::GenOrdIdl)
  if has_norm(A)
    return nothing
  end

  O = order(A)

  if isdefined(A, :basis_matrix)
    b = det(basis_matrix(A))
    if isa(b, KInftyElem)
      A.norm = O.R(Hecke.AbstractAlgebra.MPolyFactor.make_monic(numerator(b))//denominator(b))
    elseif isa(b, PolyRingElem)
      A.norm = Hecke.AbstractAlgebra.MPolyFactor.make_monic(b)
    end
    return nothing
  end

  if has_princ_gen(A)
    b = det(basis_matrix(A))
    if isa(b, KInftyElem)
      A.norm = O.R(Hecke.AbstractAlgebra.MPolyFactor.make_monic(numerator(b))//denominator(b))
    elseif isa(b, PolyRingElem)
      A.norm = Hecke.AbstractAlgebra.MPolyFactor.make_monic(b)
    end
    return nothing
  end

  assure_has_basis_matrix(A)
  b = det(basis_matrix(A))
  if isa(b, KInftyElem)
    A.norm = O.R(Hecke.AbstractAlgebra.MPolyFactor.make_monic(numerator(b))//denominator(b))
  elseif isa(b, PolyRingElem)
    A.norm = Hecke.AbstractAlgebra.MPolyFactor.make_monic(b)
  end
  return nothing
end

@doc raw"""
    norm(A::GenOrdIdl) -> RingElem

Return the norm of $A$, that is, the cardinality of $\mathcal O/A$, where
$\mathcal O$ is the order of $A$.
"""
function Hecke.norm(A::GenOrdIdl; copy::Bool = true)
  assure_has_norm(A)
  if copy
    return deepcopy(A.norm)
  else
    return A.norm
  end
end

################################################################################
#
#  Numerator and Denominator
#
################################################################################

function Hecke.numerator(a::Generic.FunctionFieldElem, O::GenOrd)
  return integral_split(a,O)[1]
end

function Hecke.denominator(a::Generic.FunctionFieldElem, O::GenOrd)
  return integral_split(a,O)[2]
end

################################################################################
#
#  Principal Generator
#
################################################################################

@doc raw"""
    has_princ_gen(A::GenOrdIdl) -> Bool

Returns whether $A$ knows if it is generated by one element.
"""
function has_princ_gen(A::GenOrdIdl)
  return isdefined(A, :princ_gen)
end

################################################################################
#
#  Reduction of element modulo ideal
#
################################################################################

function Hecke.mod(x::GenOrdElem, y::GenOrdIdl)
  parent(x) !== order(y) && error("GenOrds of element and ideal must be equal")
  # this function assumes that HNF is lower left
  # !!! This must be changed as soon as HNF has a different shape

  O = order(y)
  d = degree(O)
  a = base_ring(O).(coordinates(x))

  c = basis_matrix(y)
  t = O.R(0)
  for i in 1:d
    t = div(a[i], c[i,i])
    for j in 1:i
      a[j] = a[j] - t*c[i,j]
    end
  end
  z = O([a[i] for i in 1:length(a)])
  return z
end

################################################################################
#
#  Residue field
#
################################################################################

function Hecke.residue_field(R::fpPolyRing, p::fpPolyRingElem)
  K, _ = finite_field(p,"o")
  return K, MapFromFunc(R, K, x->K(x), y->R(y))
end

function Hecke.residue_field(R::FqPolyRing, p::FqPolyRingElem)
  return Nemo._residue_field(p, absolute = true)
end

################################################################################
#
#  Factorization
#
################################################################################

function Hecke.index(O::GenOrd)
  index = O.R(1)
  if isdefined(O, :itrans)
    index = O.R(det(O.itrans))
  end
  return index
end

function prime_dec_nonindex(O::GenOrd, p::PolyRingElem, degree_limit::Int = 0, lower_limit::Int = 0)
  K, mK = residue_field(parent(p),p)
  fact = factor(poly_to_residue(K, O.F.pol))
  result = []
  F = function_field(O)
  a = gen(F)
  for (fac, e) in fact
    facnew = map_coefficients(y -> preimage(mK, y), fac)
    I = GenOrdIdl(O, p, O(facnew(a)))
    I.is_prime = 1
    f = degree(fac)
    I.splitting_type = e, f
    I.norm = p^f
    I.minimum = p
    push!(result,(I,e))
  end
  return result
end


function poly_to_residue(K::AbstractAlgebra.Field, poly:: AbstractAlgebra.Generic.Poly{<:AbstractAlgebra.Generic.RationalFunctionFieldElem{T}}) where T
  if iszero(poly)
    return zero(K)
  else
    P, y = polynomial_ring(K,"y")
    coeffs = coefficients(poly)
    return sum([K(numerator(coeffs[i]))//K(denominator(coeffs[i]))*y^i for i in (0:length(poly)-1)])
  end
end


function Hecke.valuation(p::GenOrdIdl,A::GenOrdIdl)
  O = order(A)
  e = 0
  if has_2_elem(p)
    beta = Hecke.numerator(inv(O.F(p.gen_two)),O)
    newA = GenOrdFracIdl(beta*A,p.gen_one)
    while is_integral(newA)
      e += 1
      newA = GenOrdFracIdl(numerator(beta*newA),p.gen_one)
    end
  else
    newA = Hecke.colon(A,p)
    while is_integral(newA)
      e+=1
      newA = Hecke.colon(newA,GenOrdFracIdl(p))
    end
  end
  return e
end


function Hecke.factor(A::GenOrdIdl)
  O = A.order
  N = norm(A)
  factors = factor(N)
  primes = Dict{GenOrdIdl,Int}()
  for (f,e) in factors
    for (p,r) in prime_decomposition(O,f)
      p_val = valuation(p,A)
      if p_val != 0
        primes[p] = p_val
      end
    end
  end
  return primes
end

function prime_decomposition(O::GenOrd, p::RingElem, degree_limit::Int = degree(O), lower_limit::Int = 0; cached::Bool = true)
  #Index not well-defined for infinite maximal order
  if !isa(base_ring(O), KInftyRing) && !(divides(index(O), p)[1])
    return prime_dec_nonindex(O, p, degree_limit, lower_limit)
  else
    return prime_dec_gen(O, p, degree_limit, lower_limit)
  end
end

function prime_dec_gen(O::GenOrd, p::RingElem, degree_limit::Int = degree(O), lower_limit::Int = 0)
  Ip = pradical(O, p)
  lp = _decomposition(O, GenOrdIdl(O, p), Ip, GenOrdIdl(O, one(O)), p)
  #=z = Tuple{ideal_type(O), Int}[]
  for (Q, e) in lp
    if degree(Q) <= degree_limit && degree(Q) >= lower_limit
      push!(z, (Q, e))
    end
  end
  return z
  =#
  return lp
end

function Hecke.pradical(O::GenOrd, p::RingElem)
  t = residue_field(parent(p), p)

  if isa(t, Tuple)
    R, mR = t
  else
    R = t
    mR = MapFromFunc(parent(p), R, x->R(x), y->lift(y))
  end
#  @assert characteristic(F) == 0 || (isfinite(F) && characteristic(F) > degree(O))
  if characteristic(R) == 0 || characteristic(R) > degree(O)
    @vprintln :NfOrd 1 "using trace-radical for $p"
    rad = radical_basis_trace
  elseif isa(R, Generic.RationalFunctionField)
    @vprintln :NfOrd 1 "non-perfect case for radical for $p"
    rad = radical_basis_power_non_perfect
  else
    @vprintln :NfOrd 1 "using radical-by-power for $p"
    rad = radical_basis_power
  end
  return GenOrdIdl(O,rad(O,p))
end

function _decomposition(O::GenOrd, I::GenOrdIdl, Ip::GenOrdIdl, T::GenOrdIdl, p::RingElem)
  #I is an ideal lying over p
  #T is contained in the product of all the prime ideals lying over p that do not appear in the factorization of I
  #Ip is the p-radical
  Ip1 = Ip + I
  A, OtoA = AlgAss(O, Ip1, p)
  AtoO = pseudo_inv(OtoA)
  ideals , AA = _from_algs_to_ideals(A, OtoA, AtoO, Ip1, p)
  for j in 1:length(ideals)
    P = ideals[j][1]
    f = P.splitting_type[2]
    e = valuation(P,GenOrdIdl(O,p))
    P.splitting_type = e, f
    ideals[j] = (P,e)
  end
  return ideals
end

function Hecke.AlgAss(O::GenOrd, I::GenOrdIdl, p::RingElem)
  @assert order(I) === O

  n = degree(O)
  bmatI = basis_matrix(I)

  basis_elts = Vector{Int}()
  for i = 1:n
    if is_coprime(bmatI[i, i], p)
      continue
    end

    push!(basis_elts, i)
  end

  r = length(basis_elts)
  FQ, phi = residue_field(O.R,p)
  phi_inv = inv(phi)


  if r == 0
    A = _zero_algebra(FQ)

    local _image_zero

    let A = A
      function _image_zero(a::GenOrdElem)
        return A()
      end
    end

    local _preimage_zero

    let O = O
      function _preimage_zero(a::AlgAssElem)
        return O()
      end
    end

    OtoA = Hecke.AbsOrdToAlgAssMor{typeof(O), elem_type(FQ)}(O, A, _image_zero, _preimage_zero)
    return A, OtoA
  end

  BO = basis(O)
  mult_table = Array{elem_type(FQ), 3}(undef, r, r, r)
  for i = 1:r
    M = representation_matrix(BO[basis_elts[i]])
    #TODO: write version of reduce rows mod hnf
    if r != degree(O)
      M = reduce_rows_mod_hnf!(M, bmatI, basis_elts)
    end
    for j = 1:r
      for k = 1:r
        mult_table[i, j, k] = phi(M[basis_elts[j], basis_elts[k]])
      end
    end
  end

  if isone(BO[1])
    one = zeros(FQ, r)
    one[1] = FQ(1)
    A = AlgAss(FQ, mult_table, one)
  else
    A = AlgAss(FQ, mult_table)
  end
  if is_commutative(O)
    A.is_commutative = 1
  end

  local _image

  let I = I, A = A, basis_elts = basis_elts, FQ = FQ
    function _image(a::GenOrdElem)
      c = coordinates(mod(a, I))
      return A([phi(O.R(c[i])) for i in basis_elts ])
    end
  end

  local _preimage

  let BO = BO, basis_elts = basis_elts, r = r
    function _preimage(a::AlgAssElem)
      ca = coefficients(a)
      return sum(phi_inv(ca[i]) * BO[basis_elts[i]] for i in 1:length(ca))
    end
  end

  OtoA = GenOrdToAlgAssMor{typeof(O), elem_type(FQ)}(O, A, _image, _preimage)

  return A, OtoA
end

# Reduces the rows of M in `rows` modulo N in place.
# Assumes that N is in lowerleft HNF.
function reduce_rows_mod_hnf!(M::MatElem, N::MatElem, rows::Vector{Int})
  for i in rows
    for j = ncols(M):-1:1
      if iszero(M[i, j])
        continue
      end

      t = div(M[i, j], N[j, j])
      for k = 1:j
        M[i, k] = M[i, k] - t*N[j, k]
      end
    end
  end
  return M
end

################################################################################
#
#   Degree and ramification index
#
################################################################################

function degree(P::GenOrdIdl)
  @assert is_prime(P)
  @assert P.splitting_type != [-1,-1]
  deg_min = degree(minimum(P))
  O = order(P)
  if O == infinite_maximal_order(function_field(O))
    deg_min = -deg_min
  end
  return P.splitting_type[2]*deg_min
end

function ramification_index(P::GenOrdIdl)
  @assert is_prime(P)
  return P.splitting_type[1]
end


################################################################################
#
#  Primality testing
#
################################################################################

@doc raw"""
    is_prime_known(A::GenOrdIdl) -> Bool

Returns whether $A$ knows if it is prime.
"""
function is_prime_known(A::GenOrdIdl)
  return A.is_prime != 0
end

@doc raw"""
    is_prime(A::GenOrdIdl) -> Bool

Returns whether $A$ is a prime ideal.
"""
function is_prime(A::GenOrdIdl)
  if is_prime_known(A)
    return A.is_prime == 1
  elseif minimum(A) == 0
    A.is_prime = 1
    return true
  end

  lp = factor(A)
  for (P, e) in lp
    if norm(A) != norm(P)
      continue
    end
    if P.gen_two in A
      A.is_prime = 1
      A.splitting_type = P.splitting_type
      return true
    end
  end
  A.is_prime = 2
  return false
end

################################################################################
#
#  Inclusion of elements in ideals
#
################################################################################

@doc raw"""
    in(x::GenOrdElem, y::GenOrdIdl)

Returns whether $x$ is contained in $y$.
"""
function in(x::GenOrdElem, y::GenOrdIdl)
  O = order(y)
  parent(x) !== order(y) && error("Order of element and ideal must be equal")
  return containment_by_matrices(x, y)
end

function containment_by_matrices(x::GenOrdElem, y::GenOrdIdl)
  A = basis_mat_inv(y)
  den = lcm(collect(map(denominator, A)))
  kx = base_ring(order(y))
  num = map_entries(kx,A*den)
  R = residue_ring(kx, den, cached = false)[1]
  M = map_entries(R, num)
  v = matrix(R, 1, degree(parent(x)), coordinates(x))
  #mul!(v, v, M) This didn't work
  v = v*M
  return iszero(v)
end

###############################################################################
#
#  Decomposition type using polygons
#
###############################################################################

function _from_algs_to_ideals(A::AlgAss{T}, OtoA::Map, AtoO::Map, Ip1, p::RingElem) where {T}

  O = order(Ip1)
  n = degree(O)
  R = O.R
  @vprintln :NfOrd 1 "Splitting the algebra"
  AA = Hecke.decompose(A)
  @vprintln :NfOrd 1 "Done"
  ideals = Vector{Tuple{typeof(Ip1), Int}}(undef, length(AA))
  N = basis_matrix(Ip1, copy = false)
  list_bases = Vector{Vector{Vector{elem_type(R)}}}(undef, length(AA))
  for i = 1:length(AA)
    l = Vector{Vector{elem_type(R)}}(undef, dim(AA[i][1]))
    for j = 1:length(l)
      v = map(O.R,coordinates(AtoO(AA[i][2](AA[i][1][j]))))
      l[j] = [v[o] for o in 1:length(v)]
    end
    list_bases[i] = l
  end
  for i = 1:length(AA)
    B = AA[i][1]
    BtoA = AA[i][2]
    #we need the kernel of the projection map from A to B.
    #This is given by the basis of all the other components.
    f = dim(B)
    N1 = vcat(N, zero_matrix(R, dim(A) - f, n))
    t = 1
    for j = 1:length(AA)
      if j == i
        continue
      end
      for s = 1:length(list_bases[j])
        b = list_bases[j][s]
        for j = 1:degree(O)
          N1[n + t, j] = b[j]
        end
        t += 1
      end
    end
    N1 = view(hnf(N1, :lowerleft), nrows(N1) - degree(O) + 1:nrows(N1), 1:degree(O))
    P = GenOrdIdl(O, N1)
    P.minimum = p
    P.norm = p^f
    P.splitting_type = (0, f)
    P.is_prime = 1
    fromOtosimplealgebra = compose(OtoA, pseudo_inv(BtoA))
    #compute_residue_field_data!(P, fromOtosimplealgebra)
    ideals[i] = (P, 0)
  end
  return ideals, AA
end


################################################################################
#
#  GenOrdToAlgAssMor type
#
################################################################################

mutable struct GenOrdToAlgAssMor{S, T} <: Map{S, AlgAss{T}, Hecke.HeckeMap, GenOrdToAlgAssMor}
  header::Hecke.MapHeader

  function GenOrdToAlgAssMor{S, T}(O::S, A::AlgAss{T}, _image::Function, _preimage::Function) where {S <: GenOrd, T}
    z = new{S, T}()
    z.header = Hecke.MapHeader(O, A, _image, _preimage)
    return z
  end
end

function GenOrdToAlgAssMor(O::GenOrd, A::AlgAss{T}, _image, _preimage) where {T}
  return AbsOrdToAlgAssMor{typeof(O), T}(O, A, _image, _preimage)
end


################################################################################
#
#  Misc.
#
################################################################################


function Hecke.characteristic(R::EuclideanRingResidueField{Hecke.GenOrdElem{Generic.FunctionFieldElem{T}, KInftyElem{T}}}) where T<:Union{QQFieldElem, fpFieldElem}
  return characteristic(function_field(base_ring(R)))
end

function Hecke.characteristic(R::EuclideanRingResidueField{Hecke.GenOrdElem{Generic.FunctionFieldElem{QQFieldElem}, QQPolyRingElem}})
  return 0
end

function Hecke.characteristic(R::EuclideanRingResidueField{Hecke.GenOrdElem{Generic.FunctionFieldElem{fpFieldElem}, fpPolyRingElem}})
  return characteristic(function_field(base_ring(R)))
end

