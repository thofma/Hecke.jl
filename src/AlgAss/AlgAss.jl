################################################################################
#
#  Basic field access
#
################################################################################

base_ring(A::AlgAss{T}) where {T} = A.base_ring::parent_type(T)

Generic.dim(A::AlgAss) = size(A.mult_table, 1)

elem_type(::Type{AlgAss{T}}) where {T} = AlgAssElem{T}

parent(::Type{AlgAssElem{T}}) where {T} = AlgAss{T}

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

# Constructs the algebra R[X]/f
function AlgAss(f::PolyElem)
  R = base_ring(parent(f))
  n = degree(f)
  Rx = parent(f)
  x = gen(Rx)
  B = Array{elem_type(Rx), 1}(2*n - 1)
  B[1] = Rx(1)
  for i = 2:2*n - 1
    B[i] = mod(B[i - 1]*x, f)
  end
  mult_table = Array{elem_type(R), 3}(n, n, n)
  for i = 1:n
    for j = 1:n
      for k = 1:n
        mult_table[i, j, k] = coeff(B[i + j - 1], k - 1)
      end
    end
  end
  one = map(R, zeros(Int, n))
  one[1] = R(1)
  return AlgAss(R, mult_table, one)
end

function AlgAss(O::NfOrd, I::NfOrdIdl, p::Union{Integer, fmpz})
  @assert order(I) == O

  n = degree(O)
  BO = Hecke.basis(O)

  pisfmpz = (p isa fmpz)
  Fp = ResidueRing(FlintZZ, p)
  BOmod = [ mod(v, I) for v in BO ]
  B = zero_matrix(Fp, n, n)
  for i = 1:n
    b = elem_in_basis(BOmod[i])
    for j = 1:n
      B[i, j] = Fp(b[j])
    end
  end
  if pisfmpz
    r, B = _rref(B)
  else
    r = rref!(B)
  end
  r == 0 && error("Cannot construct zero dimensional algebra.")
  b = Vector{fmpz}(n)
  basis = Vector{NfOrdElem}(r)
  for i = 1:r
    for j = 1:n
      b[j] = fmpz(B[i, j])
    end
    basis[i] = O(b)
  end

  if pisfmpz
    _, p, L, U = _lufact(transpose(B))
  else
    _, p, L, U = lufact(transpose(B))
  end
  mult_table = Array{elem_type(Fp), 3}(r, r, r)
  d = zero_matrix(Fp, n, 1)
  for i = 1:r
    for j = i:r
      c = elem_in_basis(mod(basis[i]*basis[j], I))
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

  if isone(basis[1])
    one = zeros(Fp, r)
    one[1] = Fp(1)
    A = AlgAss(Fp, mult_table, one)
  else
    A = AlgAss(Fp, mult_table)
  end
  f = (v -> sum([ fmpz(v.coeffs[i])*basis[i] for i = 1:r ]))
  return A, f
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

function AlgAss(O::NfRelOrd{nf_elem, NfOrdFracIdl}, I::NfRelOrdIdl{nf_elem, NfOrdFracIdl}, p::NfOrdIdl, already_integral::Bool = false)
  @assert order(I) == O

  n = degree(O)
  K = nf(O)
  KK = base_ring(K)
  Fp, mF = ResidueField(order(p), p)
  mmF = extend(mF, KK)
  invmmF = inv(mmF)

  if already_integral
    Oint = O
    Iint = I
    pbint = pseudo_basis(Oint, Val{false})
  else
    # Compute a pseudo basis of O with integral coefficient ideals
    pb = pseudo_basis(O, Val{false})
    bmat_Oint = zero_matrix(KK, n, n)
    bpmat_Iint = basis_pmat(I)
    pbint = Vector{Tuple{elem_type(K), NfOrdFracIdl}}()
    for i = 1:n
      t = divexact(pb[i][1], denominator(pb[i][2]))
      tt = frac_ideal(order(p), deepcopy(numerator(pb[i][2])), fmpz(1))
      push!(pbint, (t, tt))
      elem_to_mat_row!(bmat_Oint, i, t)
      denK = KK(denominator(pb[i][2]))
      for j = i:n
        bpmat_Iint.matrix[j, i] *= denK
      end
    end
    Oint = NfRelOrd{nf_elem, NfOrdFracIdl}(K, PseudoMatrix(bmat_Oint, [ pbint[i][2] for i = 1:n ]))
    Iint = NfRelOrdIdl{nf_elem, NfOrdFracIdl}(Oint, pseudo_hnf(bpmat_Iint, :lowerleft, true))
  end

  # Reduce the pseudo basis of O modulo I
  pbintModI = Vector{Tuple{elem_type(K), NfOrdFracIdl}}()
  for i = 1:n
    b = Oint(pbint[i][1])
    push!(pbintModI, (K(mod(b, Iint)), pbint[i][2]))
  end

  basisModP = _modular_basis(pbintModI, p)

  B = zero_matrix(Fp, n, n)
  for i = 1:n
    b = elem_in_basis(Oint(basisModP[i]))
    for j = 1:n
      B[i, j] = mmF(b[j])
    end
  end
  r = rref!(B)
  r == 0 && error("Cannot construct zero dimensional algebra.")
  b = Vector{nf_elem}(n)
  basis = Vector{elem_type(Oint)}(r)
  for i = 1:r
    for j = 1:n
      b[j] = invmmF(B[i, j])
    end
    basis[i] = Oint(b)
  end

  _, p, L, U = lufact(transpose(B))
  mult_table = Array{elem_type(Fp), 3}(r, r, r)
  d = zero_matrix(Fp, n, 1)
  for i = 1:r
    for j = i:r
      c = elem_in_basis(mod(basis[i]*basis[j], Iint))
      for k = 1:n
        d[p[k], 1] = mmF(c[k])
      end
      d = solve_lt(L, d)
      d = solve_ut(U, d)
      for k = 1:r
        mult_table[i, j, k] = deepcopy(d[k, 1])
        mult_table[j, i, k] = deepcopy(d[k, 1])
      end
    end
  end

  if isone(basis[1])
    one = zeros(Fp, r)
    one[1] = Fp(1)
    A = AlgAss(Fp, mult_table, one)
  else
    A = AlgAss(Fp, mult_table)
  end
  if already_integral
    f = (v -> sum([ Oint(K(invmmF(v.coeffs[i])))*basis[i] for i = 1:r ]))
  else
    function f(v::AlgAssElem)
      s = sum([ Oint(K(invmmF(v.coeffs[i])))*basis[i] for i = 1:r])
      scoeffs = elem_in_basis(s)
      t = O()
      for i = 1:degree(O)
        t += O(K(scoeffs[i])*basis_nf(O, Val{false})[i])
      end
      return t
    end
  end
  return A, f
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::AlgAss)
  print(io, "Associative algebra over ")
  print(io, A.base_ring)
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(A::AlgAss{T}, dict::ObjectIdDict) where {T}
  B = AlgAss{T}(base_ring(A))
  for x in fieldnames(A)
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

function ==(A::AlgAss{T}, B::AlgAss{T}) where {T}
  base_ring(A) != base_ring(B) && return false
  return A.one == B.one && A.mult_table == B.mult_table
end

################################################################################
#
#  Splitting
#
################################################################################

function kernel_of_frobenius(A::AlgAss)
  F = base_ring(A)
  p = characteristic(F)

  b = A()
  c = A()
  B = zero_matrix(F, dim(A), dim(A))
  for i = 1:dim(A)
    b.coeffs[i] = F(1)
    if i > 1
      b.coeffs[i - 1] = F()
    end
    c = b^p - b
    for j = 1:dim(A)
      B[j, i] = deepcopy(c.coeffs[j])
    end
  end

  V = right_kernel(B)
  return [ A(v) for v in V ]
end

# This only works if base_ring(A) is a field
# Constructs the algebra e*A
function subalgebra(A::AlgAss{T}, e::AlgAssElem{T}, idempotent::Bool = false) where {T}
  @assert parent(e) == A
  R = base_ring(A)
  isgenres = (typeof(R) <: Generic.ResRing)
  n = dim(A)
  B = representation_mat(e)
  if isgenres
    r, B = _rref(B)
  else
    r = rref!(B)
  end
  r == 0 && error("Cannot construct zero dimensional algebra.")
  basis = Vector{AlgAssElem{T}}(r)
  for i = 1:r
    basis[i] = elem_from_mat_row(A, B, i)
  end

  # The basis matrix of e*A with respect to A is
  basis_mat_of_eA = sub(B, 1:r, 1:n)

  if isgenres
    _, p, L, U = _lufact(transpose(B))
  else
    _, p, L, U = lufact(transpose(B))
  end
  mult_table = Array{elem_type(R), 3}(r, r, r)
  c = A()
  d = zero_matrix(R, n, 1)
  for i = 1:r
    for j = 1:r
      c = basis[i]*basis[j]
      for k = 1:n
        d[p[k], 1] = c.coeffs[k]
      end
      d = solve_lt(L, d)
      d = solve_ut(U, d)
      for k = 1:r
        mult_table[i, j, k] = deepcopy(d[k, 1])
      end
    end
  end
  if idempotent
    for k = 1:n
      d[p[k], 1] = e.coeffs[k]
    end
    d = solve_lt(L, d)
    d = solve_ut(U, d)
    v = Vector{elem_type(R)}(r)
    for i in 1:r
      v[i] = d[i, 1]
    end
    eA = AlgAss(R, mult_table, v)
  else
    eA = AlgAss(R, mult_table)
  end
  eAtoA = AlgAssMor(eA, A, basis_mat_of_eA)
  return eA, eAtoA
end

function issimple(A::AlgAss, compute_algebras::Type{Val{T}} = Val{true}) where T
  if dim(A) == 1
    if compute_algebras == Val{true}
      return true, [ (A, AlgAssMor(A, A, identity_matrix(base_ring(A), dim(A)))) ]
    else
      return true
    end
  end

  F = base_ring(A)
  p = characteristic(F)
  @assert !iszero(p)
  V = kernel_of_frobenius(A)
  k = length(V)

  if compute_algebras == Val{false}
    return k == 1
  end

  if k == 1
    return true, [ (A, AlgAssMor(A, A, identity_matrix(base_ring(A), dim(A)))) ]
  end

  while true
    c = map(F, rand(0:(p-1), k))
    a = dot(c, V)

    f = minpoly(a)

    if degree(f) < 2
      continue
    end

    fac = factor(f)
    f1 = first(keys(fac.fac))
    f2 = divexact(f, f1)
    g, u, v = gcdx(f1, f2)
    @assert g == 1
    f1 *= u
    idem = A()
    x = one(A)
    for i = 0:degree(f1)
      idem += coeff(f1, i)*x
      x *= a
    end

    S = [ (subalgebra(A, idem, true)...), (subalgebra(A, one(A) - idem, true)...) ]
    return false, S
  end
end

function split(A::AlgAss)
  b, algebras = issimple(A)
  if b
    return algebras
  end
  result = Vector{Tuple{AlgAss, AlgAssMor}}()
  while length(algebras) != 0
    B, BtoA = pop!(algebras)
    b, algebras2 = issimple(B)
    if b
      push!(result, (B, BtoA))
    else
      for (C, CtoB) in algebras2
        CtoA = compose_and_squash(BtoA, CtoB)
        push!(algebras, (C, CtoA))
      end
    end
  end
  return result
end
