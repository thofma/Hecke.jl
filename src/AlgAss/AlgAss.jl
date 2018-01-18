################################################################################
#
#  Basic field access
#
################################################################################

base_ring(A::AlgAss) = A.base_ring

Generic.dim(A::AlgAss) = size(A.mult_table, 1)

elem_type(::Type{AlgAss{T}}) where {T} = AlgAssElem{T}

parent(::Type{AlgAssElem{T}}) where {T} = AlgAss{T}

################################################################################
#
#  Construction
#
################################################################################

# This only works if base_ring(A) is a field (probably) and needs sub
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
  cc = solve(sub(Mc, 1:n, 1:n), sub(Mc, 1:n, (n + 1):(n + 1)))
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

function _non_pivot_cols(M::MatElem)
  # M must be upper triangular
  result = Vector{Int}()
  j = 1
  for i = 1:rows(M)
    while j <= cols(M) && iszero(M[i, j])
      push!(result, j)
      j += 1
    end
    j += 1
    if j > cols(M)
      return result
    end
  end
  return result
end

function AlgAss(O::NfOrd, I::NfOrdIdl, p::Union{Integer, fmpz})
  n = degree(O)
  BO = Hecke.basis(O)
  Rp = ResidueRing(FlintZZ, p)

  # Compute a basis of O/I (over F_p)
  M = MatrixSpace(Rp, n, n)(basis_mat(I, Val{false}))
  M = vcat(M, zero_matrix(Rp, 1, n))
  M[n + 1, 1] = Rp(1)
  r = rref!(M)
  r = r - 1
  n == r && error("Cannot construct zero dimensional algebra.")
  # We save the indices of the columns of M without a pivot
  basis = [1]
  append!(basis, _non_pivot_cols(M))
  @assert length(basis) == n - r

  # Construct the multiplication table
  mult_table = Array{elem_type(Rp), 3}(n - r, n - r, n - r)
  for i = 1:n - r
    for j = 1:n - r
      c = BO[basis[i]]*BO[basis[j]]
      d = elem_in_basis(c)
      for k = 1:n - r
        mult_table[i, j, k] = Rp(d[basis[k]])
      end
    end
  end

  one = zeros(Rp, n - r)
  one[1] = Rp(1)
  A = AlgAss(Rp, mult_table, one)
  f = (v -> sum([ fmpz(v.coeffs[i])*BO[basis[i]] for i = 1:n - r]))
  return A, f
end

# Cohen "Advanced Topics in Computational Number Theory" Algorithm 1.5.2
function _modular_basis(pb::Vector{Tuple{RelativeElement{nf_elem}, NfOrdFracIdl}}, p::NfOrdIdl)
  L = parent(pb[1][1])
  K = base_ring(L)
  basis = Array{elem_type(L), 1}()
  for i = 1:degree(L)
    a = K(numerator(pb[i][2]).gen_one)*inv(K(denominator(pb[i][2])))
    if has_2_elem(numerator(pb[i][2]))
      b = K(numerator(pb[i][2]).gen_two)*inv(K(denominator(pb[i][2])))
      if valuation(a, p) > valuation(b, p)
        a = b
      end
    end
    push!(basis, a*pb[i][1])
  end
  return basis
end

function AlgAss(O::NfRelOrd{nf_elem, NfOrdFracIdl}, I::NfRelOrdIdl{nf_elem, NfOrdFracIdl}, p::NfOrdIdl)
  n = degree(O)
  L = nf(O)
  K = base_ring(L)
  F, mF = ResidueField(order(p), p)
  mmF = extend(mF, K)

  # We need the pseudo basis of I in the basis of O
  PMI = basis_pmat(I, Val{false})
  PBI = Vector{Tuple{RelativeElement{nf_elem}, NfOrdFracIdl}}()
  for i = 1:n
    x = elem_from_mat_row(L, PMI.matrix, i)
    push!(PBI, (x, PMI.coeffs[i]))
  end
  BI = _modular_basis(PBI, p)
  M = zero_matrix(F, n + 1, n)
  M[n + 1, 1] = F(1)
  for i = 1:n
    for j = 1:n
      M[i, j] = mmF(coeff(BI[i], j - 1))
    end
  end
  r = rref!(M)
  r = r - 1
  n == r && error("Cannot construct zero dimensional algebra.")
  basis = [1]
  append!(basis, _non_pivot_cols(M))
  @assert length(basis) == n - r

  BO = _modular_basis(pseudo_basis(O, Val{false}), p)
  N = zero_matrix(K, n, n)
  for i = 1:n
    elem_to_mat_row!(N, i, BO[i])
  end
  NN = inv(N)
  c = zero_matrix(K, 1, n)
  mult_table = Array{elem_type(F), 3}(n - r, n - r, n - r)
  for i = 1:n - r
    for j = 1:n - r
      elem_to_mat_row!(c, 1, BO[basis[i]]*BO[basis[j]])
      d = c*NN
      for k = 1:n - r
        mult_table[i, j, k] = mmF(d[1, basis[k]])
      end
    end
  end

  one = zeros(F, n - r)
  one[1] = F(1)
  A = AlgAss(F, mult_table, one)
  f = (v -> sum([ fmpz(v.coeffs[i])*BO[basis[i]] for i = 1:n - r]))
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
      B[i, j] = deepcopy(c.coeffs[j])
    end
  end

  V = kernel(B)
  return [ A(V[i]) for i = 1:length(V) ]
end

function _remove_non_pivot_cols(M::MatElem, r::Int)
  if r == rows(M)
    return M
  end
  N = zero_matrix(base_ring(M), r, r)
  i = 1
  while i <= r
    for j = i:cols(M)
      if iszero(M[i, j])
        continue
      end
      for k = 1:i
        N[k, i] = deepcopy(M[k, j])
      end
      break
    end
    i += 1
  end
  return N
end

# This only works if base_ring(A) is a field
# Constructs the algebra e*A
function subalgebra(A::AlgAss, e::AlgAssElem, idempotent::Bool = false)
  @assert parent(e) == A
  R = base_ring(A)
  n = dim(A)
  B = representation_mat(e)
  r = rref!(B)
  r == 0 && error("Cannot construct zero dimensional algebra.")
  basis = Vector{AlgAssElem}(r)
  for i = 1:r
    basis[i] = elem_from_mat_row(A, B, i)
  end

  # The basis matrix of e*A with respect to A is
  basis_mat_of_eA = sub(B, 1:r, 1:n)

  _, p, L, U = lufact(transpose(B))
  inv!(p)
  U = _remove_non_pivot_cols(U, r)
  mult_table = Array{elem_type(R), 3}(r, r, r)
  c = A()
  d = zero_matrix(R, n, 1)
  dd = zero_matrix(R, r, 1)
  for i = 1:r
    for j = 1:r
      c = basis[i]*basis[j]
      for k = 1:n
        d[p[k], 1] = c.coeffs[k]
      end
      #TODO: Use that L and U are already triangular
      d = solve(L, d)
      for k = 1:r
        dd[k, 1] = d[k, 1]
      end
      @assert all([ iszero(d[k, 1]) for k = r + 1:n ])
      dd = solve(U, dd)
      for k = 1:r
        mult_table[i, j, k] = deepcopy(dd[k, 1])
      end
    end
  end
  if idempotent
    for k = 1:n
      d[p[k], 1] = e.coeffs[k]
    end
    d = solve(L, d)
    for k = 1:r
      dd[k, 1] = d[k, 1]
    end
    @assert all([ iszero(d[k, 1]) for k = r + 1:n ])
    dd = solve(U, dd)
    eA = AlgAss(R, mult_table, [ dd[i, 1] for i = 1:r ])
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
    @assert issquarefree(f)

    fac = factor(f)
    f1 = first(keys(fac.fac))
    @assert length(fac) == degree(f)
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
    return false, [ (subalgebra(A, idem, true)...), (subalgebra(A, one(A) - idem, true)...) ]
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
