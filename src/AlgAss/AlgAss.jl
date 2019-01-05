import Base.split

export wedderburn_decomposition

################################################################################
#
#  Basic field access
#
################################################################################

base_ring(A::AlgAss{T}) where {T} = A.base_ring::parent_type(T)

Generic.dim(A::AlgAss) = size(A.mult_table, 1)

elem_type(::Type{AlgAss{T}}) where {T} = AlgAssElem{T, AlgAss{T}}

################################################################################
#
#  Commutativity
#
################################################################################

iscommutative_known(A::AlgAss) = (A.iscommutative != 0)

function iscommutative(A::AlgAss)
  if iscommutative_known(A)
    return A.iscommutative == 1
  end
  for i = 1:dim(A)
    for j = i + 1:dim(A)
      if A.mult_table[i, j, :] != A.mult_table[j, i, :]
        A.iscommutative = 2
        return false
      end
    end
  end
  A.iscommutative = 1
  return true
end

################################################################################
#
#  Construction
#
################################################################################

# This only works if base_ring(A) is a field (probably)
function find_one(A::AlgAss)
  n = dim(A)
  M = zero_matrix(base_ring(A), n^2, n)
  c = zero_matrix(base_ring(A), n^2, 1)
  for k = 1:n
    kn = (k - 1)*n
    c[kn + k, 1] = base_ring(A)(1)
    for i = 1:n
      for j = 1:n
        M[i + kn, j] = deepcopy(A.mult_table[j, k, i])
      end
    end
  end
  Mc = hcat(M, c)
  rref!(Mc)
  @assert !iszero(Mc[n, n])
  n != 1 && @assert iszero(Mc[n + 1, n + 1])
  cc = solve_ut(sub(Mc, 1:n, 1:n), sub(Mc, 1:n, (n + 1):(n + 1)))
  one = [ cc[i, 1] for i = 1:n ]
  return one
end

function AlgAss(R::Ring, mult_table::Array{T, 3}, one::Array{T, 1}) where {T}
  # checks
  return AlgAss{T}(R, mult_table, one)
end

function AlgAss(R::Ring, mult_table::Array{T, 3}) where {T}
  # checks
  A = AlgAss{T}(R)
  A.mult_table = mult_table
  A.one = find_one(A)
  return A
end

function AlgAss(R::Ring, d::Int, arr::Array{T, 1}) where {T}
  mult_table = Array{T, 3}(undef, d, d, d)
  n = d^2
  for i in 1:d
    for j in 1:d
      for k in 1:d
        mult_table[i, j, k] = arr[(i - 1) * n + (j - 1) * d + k]
      end
    end
  end
  return AlgAss(R, mult_table)
end

# Constructs the algebra R[X]/f
function AlgAss(f::PolyElem)
  R = base_ring(parent(f))
  n = degree(f)
  Rx = parent(f)
  x = gen(Rx)
  B = Array{elem_type(Rx), 1}(undef, 2*n - 1)
  B[1] = Rx(1)
  for i = 2:2*n - 1
    B[i] = mod(B[i - 1]*x, f)
  end
  mult_table = Array{elem_type(R), 3}(undef, n, n, n)
  for i = 1:n
    for j = i:n
      for k = 1:n
        mult_table[i, j, k] = coeff(B[i + j - 1], k - 1)
        mult_table[j, i, k] = coeff(B[i + j - 1], k - 1)
      end
    end
  end
  one = map(R, zeros(Int, n))
  one[1] = R(1)
  A = AlgAss(R, mult_table, one)
  A.iscommutative = 1
  return A
end

function AlgAss(O::NfAbsOrd{S, T}, I::NfAbsOrdIdl, p::Union{Integer, fmpz}) where {S, T}
  @assert order(I) == O

  n = degree(O)
  BO = basis(O)

  Fp = GF(p, cached=false)
  BOmod = [ mod(O(v), I) for v in BO ]
  B = zero_matrix(Fp, n, n)
  for i = 1:n
    b = elem_in_basis(BOmod[i])
    for j = 1:n
      B[i, j] = Fp(b[j])
    end
  end
  r = _rref!(B)
  r == 0 && error("Cannot construct zero dimensional algebra.")
  b = Vector{fmpz}(undef, n)
  bbasis = Vector{elem_type(O)}(undef, r)
  for i = 1:r
    for j = 1:n
      b[j] = lift(B[i, j])
    end
    bbasis[i] = O(b)
  end

  _, p, L, U = _lu(transpose(B))

  mult_table = Array{elem_type(Fp), 3}(undef, r, r, r)

  d = zero_matrix(Fp, n, 1)

  for i = 1:r
    for j = i:r
      c = elem_in_basis(mod(bbasis[i]*bbasis[j], I))
      for k = 1:n
        d[p[k], 1] = c[k]
      end
      d = solve_lt(L, d)
      d = solve_ut(U, d)
      for k = 1:r
        mult_table[i, j, k] = deepcopy(d[k, 1])
        mult_table[j, i, k] = deepcopy(d[k, 1])
      end
    end
  end

  if isone(bbasis[1])
    one = zeros(Fp, r)
    one[1] = Fp(1)
    A = AlgAss(Fp, mult_table, one)
  else
    A = AlgAss(Fp, mult_table)
  end
  A.iscommutative = 1

  function _image(a::NfOrdElem)
    c = elem_in_basis(mod(a, I))
    for k = 1:n
      d[p[k], 1] = c[k]
    end
    d = solve_lt(L, d)
    d = solve_ut(U, d)
    e = A()
    for k = 1:r
      e.coeffs[k] = deepcopy(d[k, 1])
    end
    return e
  end

  function _preimage(a::AlgAssElem)
    return sum(lift(a.coeffs[i])*bbasis[i] for i = 1:r)
  end

  OtoA = NfAbsOrdToAlgAssMor{S, T, elem_type(Fp)}(O, A, _image, _preimage)

  return A, OtoA
end

function _modular_basis(pb::Vector{Tuple{T, NfOrdFracIdl}}, p::NfOrdIdl) where T <: RelativeElement{nf_elem}
  L = parent(pb[1][1])
  K = base_ring(L)
  basis = Array{elem_type(L), 1}()
  u = L(K(uniformizer(p)))
  for i = 1:degree(L)
    v = valuation(pb[i][2], p)
    push!(basis, (u^v)*pb[i][1])
  end
  return basis
end

#=
Qx, x = QQ["x"];
f = x^2 + 12*x - 92;
K, a = number_field(f, "a");
OK = maximal_order(K);
Ky, y = K["y"];
g = y^2 - 54*y - 73;
L, b = number_field(g, "b");
OL = maximal_order(L);
p = prime_decomposition(OK, 2)[1][1]
=#

# Assume that O is relative order over OK, I is an ideal of O and p is a prime
# ideal of OK with pO \subseteq I. O/I is an OK/p-algebra.
#
# The idea is to compute pseudo-basis of O and I respectively, for which the
# coefficient ideals have zero p-adic valuation. Then we can think in the
# localization at p and do as in the case of principal ideal domains.
function AlgAss(O::NfRelOrd{T, S}, I::NfRelOrdIdl{T, S}, p::Union{NfOrdIdl, NfRelOrdIdl}) where {T, S}
  basis_pmatI = basis_pmat(I, Val{false})
  basis_pmatO = basis_pmat(O, Val{false})

  new_basis_mat = deepcopy(O.basis_mat)
  new_basis_mat_I = deepcopy(I.basis_mat)

  pi = anti_uniformizer(p)

  new_basis_coeffs = S[]

  for i in 1:degree(O)
    a = pi^valuation(basis_pmat(O).coeffs[i], p)
    push!(new_basis_coeffs, a * basis_pmatO.coeffs[i])
    mul_row!(new_basis_mat, i, inv(a))
    for j in 1:degree(O)
      new_basis_mat_I[j, i] = new_basis_mat_I[j, i] * a
    end
  end

  new_coeff_I = S[]

  for i in 1:degree(O)
    a = pi^valuation(basis_pmatI.coeffs[i], p)
    push!(new_coeff_I, a * basis_pmatI.coeffs[i])
    mul_row!(new_basis_mat_I, i, inv(a))
  end

  Fp, mF = ResidueField(order(p), p)
  mmF = extend(mF, base_ring(nf(O)))
  invmmF = inv(mmF)

  basis_elts = Int[]
  reducers = Int[]

  for i in 1:degree(O)
    v = valuation(new_basis_mat_I[i, i], p)
    v2 = valuation(new_coeff_I[i], p)
    #@show (v2, v)
    @assert v >= 0
    if v == 0
    #if valuation(basis_pmatI.coeffs[i], p) + valuation(new_basis_mat_I[i, i], p) == 0
      push!(reducers, i)
    else
      push!(basis_elts, i)
    end
  end

  reverse!(reducers)

  OLL = Order(nf(O), PseudoMatrix(new_basis_mat, new_basis_coeffs))

  newI = ideal(OLL, PseudoMatrix(new_basis_mat_I, new_coeff_I))

  new_basis = pseudo_basis(OLL)

  pseudo_basis_newI = pseudo_basis(newI)

  tmp_matrix = zero_matrix(base_ring(nf(O)), 1, degree(O))

  basis_mat_inv_OLL = basis_mat_inv(OLL)

  function _coeff(c) 
    for i in 0:degree(O) - 1
      tmp_matrix[1, i + 1] = coeff(c, i)
    end
    return tmp_matrix * basis_mat_inv_OLL
  end

  r = length(basis_elts)

  mult_table = Array{elem_type(Fp), 3}(undef, r, r, r)

  for i in 1:r
    for j in 1:r
      c = new_basis[basis_elts[i]][1] * new_basis[basis_elts[j]][1]
      coeffs = _coeff(c)

      for k in reducers
        d = -coeffs[k]//new_basis_mat_I[k, k]
        c = c + d * pseudo_basis_newI[k][1]
      end
      coeffs = _coeff(c)
      for k in 1:degree(O)
        if !(k in basis_elts)
          @assert iszero(coeffs[k])
        end
      end
      for k in 1:r
        mult_table[i, j, k] = mmF(coeffs[basis_elts[k]])
      end
    end
  end

  if isone(new_basis[basis_elts[1]][1])
    one = zeros(Fp, length(basis_elts))
    one[1] = Fp(1)
    A = AlgAss(Fp, mult_table, one)
  else
    A = AlgAss(Fp, mult_table)
  end
  A.iscommutative = 1

  function _image(a::NfRelOrdElem)
    c = a.elem_in_nf
    coeffs = _coeff(c)
    for k in reducers
      d = -coeffs[k]//new_basis_mat_I[k, k]
      c = c + d*pseudo_basis_newI[k][1]
    end
    coeffs = _coeff(c)
    for k in 1:degree(O)
      if !(k in basis_elts)
        @assert iszero(coeffs[k])
      end
    end
    b = A()
    for k in 1:r
      b.coeffs[k] = mmF(coeffs[basis_elts[k]])
    end
    return b
  end

  lifted_basis_of_A = []

  for i in basis_elts
    c = coprime_to(new_basis[i][2], p)
    b = invmmF(inv(mmF(c)))*c*new_basis[i][1]
    @assert b in O
    push!(lifted_basis_of_A, b)
  end

  function _preimage(v::AlgAssElem)
    return O(sum((invmmF(v.coeffs[i])) * lifted_basis_of_A[i] for i in 1:r))
  end

  OtoA = NfRelOrdToAlgAssMor{T, S, elem_type(Fp)}(O, A, _image, _preimage)

  return A, OtoA
end

function AlgAss(A::Generic.MatAlgebra)
  n = A.n
  K = base_ring(A)
  n2 = n^2
  # We use the matrices M_{ij} with a 1 at row i and column j and zeros everywhere else as the basis for A.
  # We sort "row major", so A[(i - 1)*n + j] corresponds to the matrix M_{ij}.
  # M_{ik}*M_{lj} = 0, if k != l, and M_{ik}*M_{kj} = M_{ij}
  mult_table = zeros(K, n2, n2, n2)
  oneK = one(K)
  for i = 0:n:(n2 - n)
    for k = 1:n
      kn = (k - 1)*n
      for j = 1:n
        mult_table[i + k, kn + j, i + j] = oneK
      end
    end
  end
  oneA = zeros(K, n2)
  for i = 1:n
    oneA[(i - 1)*n + i] = oneK
  end
  A = AlgAss(K, mult_table, oneA)
  A.iscommutative = ( n == 1 ? 1 : 2 )
  return A
end

###############################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::AlgAss)
  print(io, "Associative algebra of dimension ", dim(A), " over ", base_ring(A))
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(A::AlgAss{T}, dict::IdDict) where {T}
  B = AlgAss{T}(base_ring(A))
  for x in fieldnames(typeof(A))
    if x != :base_ring && isdefined(A, x)
      setfield!(B, x, Base.deepcopy_internal(getfield(A, x), dict))
    end
  end
  B.base_ring = A.base_ring
  return B
end

################################################################################
#
#  Equality
#
################################################################################

function ==(A::AlgAss, B::AlgAss)
  base_ring(A) != base_ring(B) && return false
  return A.one == B.one && A.mult_table == B.mult_table
end


function subalgebra(A::AlgAss{T}, e::AlgAssElem{T, AlgAss{T}}, idempotent::Bool = false) where {T}
  @assert parent(e) == A
  R = base_ring(A)
  isgenres = (typeof(R) <: Generic.ResRing)
  n = dim(A)
  B = representation_matrix(e)
  r = _rref!(B)
  r == 0 && error("Cannot construct zero dimensional algebra.")
  basis = Vector{elem_type(A)}(undef, r)
  for i = 1:r
    basis[i] = elem_from_mat_row(A, B, i)
  end

  # The basis matrix of e*A with respect to A is
  basis_mat_of_eA = sub(B, 1:r, 1:n)

  if isgenres
    _, p, L, U = _lu(transpose(B))
  else
    _, p, L, U = lu(transpose(B))
  end

  mult_table = Array{elem_type(R), 3}(undef, r, r, r)
  c = A()
  d = zero_matrix(R, n, 1)
  for i = 1:r
    for j = 1:r
      if iscommutative(A) && j < i
        continue
      end
      c = mul!(c, basis[i], basis[j])
      for k = 1:n
        d[p[k], 1] = c.coeffs[k]
      end
      d = solve_lt(L, d)
      d = solve_ut(U, d)
      for k = 1:r
        mult_table[i, j, k] = deepcopy(d[k, 1])
        if iscommutative(A) && i != j
          mult_table[j, i, k] = deepcopy(d[k, 1])
        end
      end
    end
  end
  if idempotent
    for k = 1:n
      d[p[k], 1] = e.coeffs[k]
    end
    d = solve_lt(L, d)
    d = solve_ut(U, d)
    v = Vector{elem_type(R)}(undef, r)
    for i in 1:r
      v[i] = d[i, 1]
    end
    eA = AlgAss(R, mult_table, v)
  else
    eA = AlgAss(R, mult_table)
  end

  # TODO: The following is wrong. The algebra eA may be commutative
  # even if A is not commutative.
  eA.iscommutative = A.iscommutative

  if idempotent
    # We have the map eA -> A, given by the multiplying with basis_mat_of_eA.
    # But there is also the canonical projection A -> eA, a -> ea.
    # We compute the corresponding matrix.
    B = representation_matrix(e)
    C = zero_matrix(R, n, r)
    for i in 1:n
      for k = 1:n
        d[p[k], 1] = B[i, k]
      end
      d = solve_lt(L, d)
      d = solve_ut(U, d)
      for k in 1:r
        C[i, k] = d[k, 1]
      end
    end
    eAtoA = hom(eA, A, basis_mat_of_eA, C)
  else
    eAtoA = hom(eA, A, basis_mat_of_eA)
  end
  return eA, eAtoA
end

function subalgebra(A::AlgAss{T}, basis::Array{AlgAssElem{T, AlgAss{T}},1}) where {T}
  B=zero_matrix(base_ring(A), dim(A), length(basis))
  for i=1:dim(A)
    for j=1:length(basis)
      B[i,j]=basis[j].coeffs[i]
    end
  end
  M=Array{elem_type(base_ring(A)),3}(undef, length(basis), length(basis), length(basis))
  for i=1:length(basis)
    for j=1:length(basis)
      x=basis[i]*basis[j]
      N1=matrix(base_ring(A), dim(A), 1, x.coeffs)
      N=_solve_unique(N1,B)
      for k=1:length(basis)
        M[i,j,k]=N[k,1]
      end
    end
  end
  A1=AlgAss(base_ring(A), M)
  return A1, hom(A1, A, B')
end

###############################################################################
#
#  Trace Matrix
#
###############################################################################

function _assure_trace_basis(A::AlgAss{T}) where T
  if !isdefined(A, :trace_basis_elem)
    A.trace_basis_elem = Array{T, 1}(undef, dim(A))
    for i=1:length(A.trace_basis_elem)
      A.trace_basis_elem[i]=sum(A.mult_table[i,j,j] for j= 1:dim(A))
    end
  end
  return nothing
end

################################################################################
#
#  Radical
#
################################################################################

@doc Markdown.doc"""
***
    radical(A::AlgAss{fq_nmod})
            
> Given an algebra over a finite field of prime order, this function 
> returns a set of elements generating the radical of A
"""
function radical(A::AlgAss{fq_nmod})

  F=A.base_ring
  p=F.p
  l=clog(fmpz(dim(A)),p)
  #First step: kernel of the trace matrix
  I=trace_matrix(A)
  k,B=nullspace(I)
  # The columns of B give the coordinates of the elements in the order.
  if k==0
    return AlgAssElem[]
  end
  C=transpose(B)
  if l==1 && dim(A)!=p
    #In this case, we can output I: it is the standard p-trace method.
    return AlgAssElem[elem_from_mat_row(A,C,i) for i=1:rows(C)]
  end
  #Now, iterate: we need to find the kernel of tr((xy)^(p^i))/p^i mod p
  #on the subspace generated by C
  #Hard to believe, but this is linear!!!!
  for i=1:l
    M=zero_matrix(F, dim(A), rows(C))
    for t=1:rows(I)
      elm=elem_from_mat_row(A,C,t)
      for s=1:dim(A)
        a=elm*A[s]
        M1=representation_matrix(a^(p^i))
        el=sum(FlintZZ(coeff(M1[k,k],0)) for k=1:dim(A))
        M[s,t]=F(divexact(el,p^i))
      end
    end
    k,B=nullspace(M)
    if k==0
      # This is clearly wrong
      return AlgAssOrdIdl(O,MatrixSpace(FlintZZ, dim(A), dim(A), false)(p))
    end
    C=transpose(B)*C
  end
  return AlgAssElem[elem_from_mat_row(A,C,i) for i=1:rows(C)]
   
end

###############################################################################
#
#  Center
#
###############################################################################

function _rep_for_center(M::T, A::AlgAss) where T<: MatElem
  n=dim(A)
  for i=1:n
    for j = 1:n
      for k = 1:n
        M[k+(i-1)*n, j] = A.mult_table[i, j, k]-A.mult_table[j, i, k]
      end
    end
  end
  return nothing
end

function center(A::AlgAss{T}) where {T}
  if iscommutative_known(A) && A.iscommutative==1
    B, mB = AlgAss(A)
    return B, mB
  end
  if isdefined(A, :center)
    return A.center::Tuple{AlgAss{T}, morphism_type(AlgAss{T}, AlgAss{T})}
  end
  n=dim(A)
  M=zero_matrix(base_ring(A), n^2, n)
  # I concatenate the difference between the right and left representation matrices.
  _rep_for_center(M,A)
  k,B=nullspace(M)
  res=Array{elem_type(A),1}(undef, k)
  for i=1:k
    res[i]= A(T[B[j,i] for j=1:n])
  end
  C, mC = subalgebra(A, res)
  A.center = C, mC
  return C, mC
end

################################################################################
#
#  Primitive elements
#
################################################################################

function primitive_element(A::AbsAlgAss)
  a, _ = _primitive_element(A)
  return a
end

function _primitive_element(A::AbsAlgAss)
  error("Not implemented yet")
  return nothing
end

function _primitive_element(A::AbsAlgAss{T}) where T <: Union{nmod, fq, fq_nmod, Generic.Res{fmpz}, fmpq, Generic.ResF{fmpz}, gfp_elem}
  d = dim(A)
  a = rand(A)
  f = minpoly(a)
  while degree(f) < d
    a = rand(A)
    f = minpoly(a)
  end
  return a, f
end

function _as_field(A::AlgAss{T}) where T
  d = dim(A)
  a, mina = _primitive_element(A)
  b = one(A)
  M = zero_matrix(base_ring(A), d, d)
  elem_to_mat_row!(M, 1, b)
  for i in 1:(d - 1)
    b = mul!(b, b, a)
    elem_to_mat_row!(M, i + 1, b)
  end
  B = inv(M)
  N = zero_matrix(base_ring(A), 1, d)
  local f
  let N = N, B = B
    f = function(x)
      for i in 1:d
        N[1, i] = x.coeffs[i]
      end
      return N * B
    end
  end
  return a, mina, f
end

function _as_field_with_isomorphism(A::AbsAlgAss{S}) where { S <: Union{fmpq, nmod, Generic.Res{fmpz}} }
  return _as_field_with_isomorphism(A, _primitive_element(A)...)
end

# Assuming a is a primitive element of A and mina its minimal polynomial, this
# functions constructs the field base_ring(A)/mina and the isomorphism between
# A and this field.
function _as_field_with_isomorphism(A::AbsAlgAss{S}, a::AbsAlgAssElem{S}, mina::T) where { S <: Union{fmpq, nmod, Generic.Res{fmpz}}, T <: Union{fmpq_poly, nmod_poly, fmpz_mod_poly} }
  s = one(A)
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  elem_to_mat_row!(M, 1, s)
  for i = 2:dim(A)
    s = mul!(s, s, a)
    elem_to_mat_row!(M, i, s)
  end

  if base_ring(A) == FlintQQ
    K = number_field(mina, cached = false)[1]
    return K, AbsAlgAssToNfAbsMor(A, K, M, inv(M))
  elseif base_ring(A) isa NmodRing
    Fq = FqNmodFiniteField(mina, Symbol("a"), false)
    return Fq, AbsAlgAssToFqNmodMor(A, Fq, M, inv(M))
  elseif base_ring(A) isa Generic.ResRing{fmpz}
    Fq = FqFiniteField(mina, Symbol("a"), false)
    N, d = inv(M)
    return Fq, AbsAlgAssToFqMor(A, Fq, M, divexact(N, d))
  else
    error("Not implemented")
  end
end

################################################################################
#
#  Trivial conversion to AlgAss
#
################################################################################

function AlgAss(A::AlgAss)
  R = base_ring(A)
  d = dim(A)
  return A, hom(A, A, identity_matrix(R, d), identity_matrix(R, d))
end

################################################################################
#
#  Change of ring
#
################################################################################

# Top level functions to avoid "type mix-ups" (like AlgAss{fq_nmod} with FlintQQ)
function restrict_scalars(A::AlgAss{nf_elem}, Q::FlintRationalField)
  return _restrict_scalars_to_prime_field(A, Q)
end

function restrict_scalars(A::AlgAss{fq_nmod}, Fp::NmodRing)
  return _restrict_scalars_to_prime_field(A, Fp)
end

function restrict_scalars(A::AlgAss{fq}, Fp::Generic.ResRing{fmpz})
  return _restrict_scalars_to_prime_field(A, Fp)
end

function _restrict_scalars_to_prime_field(A::AlgAss{T}, prime_field::Union{FlintRationalField, NmodRing, Generic.ResRing{fmpz}}) where { T <: Union{nf_elem, fq_nmod, fq} }
  K = base_ring(A)
  n = dim(A)
  m = degree(K)
  nm = n*m
  a = gen(K)
  # We use A[1], a*A[1], ..., a^{m - 1}*A[1], ..., A[n], ..., a^{m - 1}*A[n] as
  # the basis for A over the prime field.
  # Precompute the powers a^k:
  powers_of_a = zeros(K, 2*m - 1)
  powers_of_a[1] = one(K)
  for k = 2:2*m - 1
    powers_of_a[k] = mul!(powers_of_a[k], powers_of_a[k - 1], a)
  end

  function _new_coeffs(x)
    y = Vector{elem_type(prime_field)}(undef, nm)
    yy = coeffs(x, false)
    for i = 1:n
      for j = 1:m
        if prime_field == FlintQQ
          y[(i - 1)*m + j] = coeff(yy[i], j - 1)
        else
          y[(i - 1)*m + j] = prime_field(coeff(yy[i], j - 1))
        end
      end
    end
    return y
  end

  m1 = m - 1
  mult_table = zeros(prime_field, nm, nm, nm)
  Aij = A()
  t = A()
  for i = 1:n
    for j = 1:n
      Aij = mul!(Aij, A[i], A[j])
      if iszero(Aij)
        continue
      end

      mi = m*(i - 1)
      mj = m*(j - 1)
      for s = 0:2*m1 # all possible sums of exponents for a
        t = mul!(t, powers_of_a[s + 1], Aij)
        tcoeffs = _new_coeffs(t)
        for k = max(0, s - m1):min(s, m1)
          mult_table[mi + k + 1, mj + s - k + 1, :] = tcoeffs
        end
      end
    end
  end
  B = AlgAss(prime_field, mult_table, _new_coeffs(one(A)))
  B.iscommutative = A.iscommutative

  function AtoB(x)
    @assert parent(x) == A
    return B(_new_coeffs(x))
  end

  function BtoA(x)
    @assert parent(x) == B
    if prime_field == FlintQQ
      R = parent(K.pol)
    else
      R, z = PolynomialRing(prime_field, "z", cached = false)
    end
    y = Vector{elem_type(K)}(undef, n)
    xcoeffs = coeffs(x) # a copy
    for i = 1:n
      y[i] = K(R(xcoeffs[(i - 1)*m + 1:(i - 1)*m + m]))
    end
    return A(y)
  end

  return B, AtoB, BtoA
end

function restrict_scalars(A::AlgAss{nf_elem}, KtoL::NfToNfMor)
  K = domain(KtoL)
  L = codomain(KtoL)
  @assert L == base_ring(A)
  n = dim(A)
  m = div(degree(L), degree(K))
  nm = n*m
  a = gen(L)
  powers_of_a = zeros(L, 2*m - 1)
  powers_of_a[1] = one(L)
  for k = 2:2*m - 1
    powers_of_a[k] = mul!(powers_of_a[k], powers_of_a[k - 1], a)
  end

  basisK = basis(K)
  basisKinL = map(KtoL, basisK)
  M = zero_matrix(FlintQQ, degree(L), degree(L))
  t = L()
  for i = 1:m
    for j = 1:degree(K)
      t = mul!(t, basisKinL[j], powers_of_a[i])
      for k = 1:degree(L)
        M[k, (i - 1)*m + j] = coeff(t, k - 1)
      end
    end
  end
  M = inv(M)

  function _new_coeffs(x)
    y = zeros(K, nm)
    yy = coeffs(x, false)
    for i = 1:n
      c = matrix(FlintQQ, degree(L), 1, [ coeff(yy[i], j) for j = 0:degree(L) - 1 ])
      Mc = M*c
      for j = 1:m
        for k = 1:degree(K)
          y[(i - 1)*m + j] += Mc[(j - 1)*degree(K) + k, 1]*basisK[k]
        end
      end
    end
    return y
  end

  m1 = m - 1
  mult_table = zeros(K, nm, nm, nm)
  Aij = A()
  t = A()
  for i = 1:n
    for j = 1:n
      Aij = mul!(Aij, A[i], A[j])
      if iszero(Aij)
        continue
      end

      mi = m*(i - 1)
      mj = m*(j - 1)
      for s = 0:2*m1 # all possible sums of exponents for a
        t = mul!(t, powers_of_a[s + 1], Aij)
        tcoeffs = _new_coeffs(t)
        for k = max(0, s - m1):min(s, m1)
          mult_table[mi + k + 1, mj + s - k + 1, :] = tcoeffs
        end
      end
    end
  end
  B = AlgAss(K, mult_table, _new_coeffs(one(A)))
  B.iscommutative = A.iscommutative

  function AtoB(x)
    @assert parent(x) == A
    return B(_new_coeffs(x))
  end

  function BtoA(x)
    @assert parent(x) == B
    y = zeros(L, n)
    xcoeffs = coeffs(x)
    for i = 1:n
      xx = map(KtoL, xcoeffs[(i - 1)*m + 1:(i - 1)*m + m])
      for j = 1:m
        y[i] += xx[j]*powers_of_a[j]
      end
    end
    return A(y)
  end

  return B, AtoB, BtoA
end

function _as_algebra_over_center(A::AlgAss{fmpq})
  C, CtoA = center(A)
  fields = as_number_fields(C)
  @assert length(fields) == 1
  K, CtoK = fields[1]

  basisC = basis(C)
  basisCinA = Vector{elem_type(A)}(undef, dim(C))
  basisCinK = Vector{elem_type(K)}(undef, dim(C))
  for i = 1:dim(C)
    basisCinA[i] = CtoA(basisC[i])
    basisCinK[i] = CtoK(basisC[i])
  end

  # We construct a basis of A over C (respectively K) by using the following fact:
  # A subset M of basis(A) is a C-basis of A if and only if |M| = dim(A)/dim(C)
  # and all possible products of elements of M and basisCinA form a Q-basis of A.
  AoverQ = basis(A)
  AoverC = Vector{Int}()
  M = zero_matrix(FlintQQ, dim(C), dim(A))
  MM = zero_matrix(FlintQQ, 0, dim(A))
  r = 0
  for i = 1:dim(A)
    b = AoverQ[i]

    for j = 1:dim(C)
      elem_to_mat_row!(M, j, b*basisCinA[j])
    end

    N = vcat(MM, M)
    s = rank(N)
    if s > r
      push!(AoverC, i)
      MM = N
      r = s
    end
    if r == dim(A)
      break
    end
  end

  m = div(dim(A), dim(C))

  @assert length(AoverC) == m
  @assert rows(MM) == dim(A)

  iMM = inv(MM)

  function _new_coeffs(x)
    y = zeros(K, m)
    xx = matrix(FlintQQ, 1, dim(A), coeffs(x, false))
    Mx = xx*iMM
    for i = 1:m
      for j = 1:dim(C)
        y[i] = addeq!(y[i], basisCinK[j]*Mx[1, (i - 1)*dim(C) + j])
      end
    end
    return y
  end

  mult_table = zeros(K, m, m, m)
  Aij = A()
  for i = 1:m
    for j = 1:m
      Aij = mul!(Aij, A[AoverC[i]], A[AoverC[j]])
      if iszero(Aij)
        continue
      end

      mult_table[i, j, :] = _new_coeffs(Aij)
    end
  end

  B = AlgAss(K, mult_table, _new_coeffs(one(A)))
  B.iscommutative = A.iscommutative

  function AtoB(x)
    @assert parent(x) == A
    return B(_new_coeffs(x))
  end

  function BtoA(x)
    @assert parent(x) == B
    y = zeros(FlintQQ, dim(A))
    xx = A()
    for i = 1:dim(B)
      t = CtoA(CtoK\coeffs(x, false)[i])
      xx = add!(xx, xx, t*A[AoverC[i]])
    end
    Mx = matrix(FlintQQ, 1, dim(A), coeffs(xx, false))*MM
    return A([ Mx[1, i] for i = 1:dim(A) ])
  end

  return B, AtoB, BtoA
end
