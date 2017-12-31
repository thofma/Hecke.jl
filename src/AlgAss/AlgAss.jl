################################################################################
#
#  Basic field access
#
################################################################################

base_ring(A::AlgAss) = A.base_ring

dim(A::AlgAss) = size(A.mult_table, 1)

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
  @assert iszero(Mc[n + 1, n + 1])
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

function deepcopy_internal(A::AlgAss{T}, dict::ObjectIdDict) where {T}
  B = AlgAss{T}(base_ring(A))
  for x in fieldnames(A)
    if x != :base_ring && isdefined(A, x)
      setfield!(B, x, deepcopy_internal(getfield(A, x), dict))
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
  return A.mult_table == B.mult_table
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

function subalgebra(A::AlgAss, e::AlgAssElem)
  @assert parent(e) == A
  error("Not implemented. (Coming soon.)")
end

function issimple(A::AlgAss, compute_algebras::Type{Val{T}} = Val{true}) where T
  if dim(A) == 1
    if compute_algebras == Val{true}
      return true, [ A ]
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
    return true, [ A ]
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
    return false, [ subalgebra(A, idem), subalgebra(A, one(A) - idem) ]
  end
end
