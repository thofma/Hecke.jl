################################################################################
#
#  Generate random examples
#
################################################################################

function _jordan_block(R, n::Int, a)
  z = a * identity_matrix(R, n)
  for i in 1:(n - 1)
    z[i + 1, i] = 1
  end
  return z
end

function _rand_block(R, n::Int, l::Int)
  Rx, x = PolynomialRing(R, "x", cached = false)
  f = rand(Rx, n:n, -100:100)
  if !iszero(f)
    setcoeff!(f, degree(f), one(R))
  end
  while !is_irreducible(f) || degree(f) != n
    f = rand(Rx, n:n, -100:100)
    if !iszero(f)
      setcoeff!(f, degree(f), one(R))
    end
  end
  return companion_matrix(f^l)
end

function _random_elementary_operations!(a; type = :rows)
  tr = type == :columns
  @assert is_square(a)
  n = nrows(a)
  d = det(a)
  if n == 1
    return a
  end
  i = rand(1:n)
  j = rand(1:n)
  while j == i
    j = rand(1:n)
  end

  r = rand(base_ring(a), -10:10)
  for k in 1:n
    if tr
      a[k, i] = a[k, i] + r * a[k, j]
    else
      a[i, k] = a[i, k] + r * a[j, k]
    end
  end
  @assert d == det(a)
  return a
end

function _rand_poly_deg(R, n)
  Rx, x = PolynomialRing(R, "x", cached = false)
  f = rand(Rx, n:n, -100:100)
  if !iszero(f)
    setcoeff!(f, degree(f), one(R))
  end
  while !is_irreducible(f) || degree(f) != n
    f = rand(Rx, n:n, -100:100)
    if !iszero(f)
      setcoeff!(f, degree(f), one(R))
    end
  end
  return f
end

function _random_matrix_special(R, n, deg)
  z = dense_matrix_type(R)[]
  f = _rand_poly_deg(R, deg)
  for i in 1:4
    l = rand(1:2)
    for j in 1:l
      push!(z, companion_matrix(f^i))
    end
    if sum(nrows.(z)) > n
      break
    end
  end
  return diagonal_matrix(z)
end

function _random_sln(R, n; num_op = 10)
  a = identity_matrix(R, n)
  for i in 1:num_op
    _random_elementary_operations!(a; type = rand() < 0.5 ? :rows : :columns)
  end
  return a
end

function _random_matrix(R, block_shape)
  matrices = dense_matrix_type(R)[]
  for (r, l, ll) in block_shape
    B = _rand_block(R, r, l)
    for j in 1:ll
      push!(matrices, B)
    end
  end
  if length(matrices) == 0
    return zero_matrix(R, 0, 0)
  end
  return diagonal_matrix(matrices)
end

function _similarity_test_setup(R, n; max_block = 4, same = false)
  block_shape = Tuple{Int, Int, Int}[]
  nn = n

  if same
    AA = _random_matrix_special(R, div(n, 3), rand(1:max_block))
    nn = n - nrows(AA)
  end

  while nn > 0
    #@show nn
    r = min(rand(1:nn), max_block)
    #@show r
    l = max(Int(floor(nn/r)), 1)
    if same
      nbl = rand(1:l)
    else
      nbl = l
    end
    #@show nbl
    nnn = nn - r * nbl
    ll = max(Int(floor(nnn/(r * nbl))), 1)
    nbll = rand(1:ll)
    #@show nbll
    push!(block_shape, (r, nbl, nbll))
    nn = nn - r * nbl *  nbll
  end
  b = block_shape
  #@show block_shape
  A = _random_matrix(R, block_shape)
  if same
    A = diagonal_matrix([A, AA])
  end

  z = _random_sln(R, nrows(A))
  @assert isone(det(z))
  zinv = inv(z)
  B = z * A * zinv
  return A, B
end
