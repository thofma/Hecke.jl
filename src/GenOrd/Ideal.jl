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

################################################################################
#
#  Basic field access
#
################################################################################

@doc Markdown.doc"""
    order(x::GenOrdIdl) -> GenOrd

Return the order, of which $x$ is an ideal.
"""
Hecke.order(a::GenOrdIdl) = a.order

###########################################################################################
#
#   Basis
#
###########################################################################################

@doc Markdown.doc"""
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

@doc Markdown.doc"""
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

@doc Markdown.doc"""
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

  V = hnf(vcat([representation_matrix(x) for x in [O(A.gen_one),A.gen_two]]),:lowerleft)
  d = ncols(V)
  A.basis_matrix = V[d+1:2*d,1:d]
  return nothing
end

################################################################################
#
#  Basis matrix inverse
#
################################################################################

@doc Markdown.doc"""
    has_basis_mat_inv(A::GenOrdIdl) -> Bool

Return whether $A$ knows its inverse basis matrix.
"""
has_basis_mat_inv(A::GenOrdIdl) = isdefined(A, :basis_mat_inv)

@doc Markdown.doc"""
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


(O::GenOrd)(p::PolyElem) = O(O.F(p))
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
  check_parent(a, b)
  O = order(a)

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
  V = hnf(vcat([Mb*representation_matrix(O([Ma[i,o] for o in 1:ncols(Ma)])) for i in 1:ncols(Ma)]),:lowerleft)
  d = ncols(V)
  return GenOrdIdl(O, V[d*(d-1)+1:d^2,1:d])
end

@doc Markdown.doc"""
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
  end
    return Base.power_by_squaring(A, e)
end


################################################################################
#
#  Ad hoc multiplication
#
################################################################################

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

  n = representation_matrix(B[1])*bmatinv
  m, d = integral_split(n, coefficient_ring(O))
  for i in 2:length(B)
    n = representation_matrix(B[i])*bmatinv
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
  b = Hecke.AbstractAlgebra.MPolyFactor.make_monic(b)
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
  v = change_base_ring(O.R, coordinates(O(d)))
  fl, s = can_solve_with_solution(M, v, side = :left)
  @assert fl
  den = denominator(s[1]//d)
  for i = 2:ncols(s)
    den = lcm(den, denominator(s[i]//d))
  end
  A.minimum = Hecke.AbstractAlgebra.MPolyFactor.make_monic(den)
  return nothing
end

################################################################################
#
#  Norm
#
################################################################################

@doc Markdown.doc"""
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

  if isdefined(A, :basis_matrix)
    A.norm = Hecke.AbstractAlgebra.MPolyFactor.make_monic(det(basis_matrix(A)))
    return nothing
  end

  if has_princ_gen(A)
    A.norm = Hecke.AbstractAlgebra.MPolyFactor.make_monic(norm(A.princ_gen))
    return nothing
  end

  assure_has_basis_matrix(A)
  A.norm = Hecke.AbstractAlgebra.MPolyFactor.make_monic(det(basis_matrix(A)))
  return nothing
end

@doc Markdown.doc"""
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

@doc Markdown.doc"""
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
  a = change_base_ring(O.R,coordinates(x)).entries

  c = basis_matrix(y)
  t = O.R(0)
  for i in 1:d
    t = div(a[i], c[i,i])
    for j in 1:i
      a[j] = a[j] - t*c[i,j]
    end
  end
  z = O([a[i] for i in 1:lenth(a)])
  return z
end

################################################################################
#
#  Residue field
#
################################################################################

function Hecke.ResidueField(R::GFPPolyRing, p::gfp_poly)
  K, _ = FiniteField(p,"o")
  return K, MapFromFunc(x->K(x), y->R(y), R, K)
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

function prime_dec_nonindex(O::GenOrd, p::PolyElem, degree_limit::Int = 0, lower_limit::Int = 0)
  K = ResidueField(parent(p),p)[1]
  fact = factor(poly_to_residue(K,O.F.pol))
  result = []
  for (fac,e) in fact
    facnew = change_coefficient_ring(O.F.base_ring, fac)
    I = GenOrdIdl(O,p,O(facnew))
    I.is_prime = 1
    f = degree(fac)
    I.splitting_type = e, f
    I.norm = p^f
    I.minimum = p
    push!(result,(I,e))
  end
  return result
end


function poly_to_residue(K::AbstractAlgebra.Field, poly:: AbstractAlgebra.Generic.Poly{<:AbstractAlgebra.Generic.Rat{T}}) where T
  if poly == 0
    return K(0)
  else
    P, y = PolynomialRing(K,"y")
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
      primes[p] = valuation(p,A)
    end
  end
  return primes
end

function prime_decomposition(O::GenOrd, p::RingElem, degree_limit::Int = degree(O), lower_limit::Int = 0; cached::Bool = true)
  if !(divides(index(O), p)[1])
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
  t = ResidueField(parent(p), p)

  if isa(t, Tuple)
    R, mR = t
  else
    R = t
    mR = MapFromFunc(x->R(x), y->lift(y), parent(p), R)
  end
#  @assert characteristic(F) == 0 || (isfinite(F) && characteristic(F) > degree(O))
  if characteristic(R) == 0 || characteristic(R) > degree(O)
    @vprint :NfOrd 1 "using trace-radical for $p\n"
    rad = radical_basis_trace
  elseif isa(R, Generic.RationalFunctionField)
    @vprint :NfOrd 1 "non-perfect case for radical for $p\n"
    rad = radical_basis_power_non_perfect
  else
    @vprint :NfOrd 1 "using radical-by-power for $p\n"
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
  FQ, phi = ResidueField(O.R,p)
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
      return A([ FQ(numerator(c[i]))//FQ(denominator(c[i])) for i in basis_elts ])
    end
  end

  local _preimage

  let BO = BO, basis_elts = basis_elts, r = r
    function _preimage(a::AlgAssElem)
      return O(coefficients(a))
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

###############################################################################
#
#  Decomposition type using polygons
#
###############################################################################

function _from_algs_to_ideals(A::AlgAss{T}, OtoA::Map, AtoO::Map, Ip1, p::RingElem) where {T}

  O = order(Ip1)
  n = degree(O)
  R = O.R
  @vprint :NfOrd 1 "Splitting the algebra\n"
  AA = Hecke.decompose(A)
  @vprint :NfOrd 1 "Done \n"
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
