function _field_as_vector_space(K::NumField, Q::QQField)
  BLoverK = absolute_basis(K)
  d = absolute_degree(K)
  m = identity_matrix(Q, d)
  return BLoverK, m
end

function _field_as_vector_space(K::RelSimpleNumField{AbsSimpleNumFieldElem}, Q::AbsSimpleNumField)
  BLoverK = basis(K)
  d = degree(K)
  m = identity_matrix(Q, d)
  return BLoverK, m
end

function _field_as_vector_space(K::fqPolyRepField, Q::fpField)
  d = degree(K)
  BLoverK = powers(gen(K), d - 1)
  m = identity_matrix(Q, d)
  return BLoverK, m
end

function _field_as_vector_space(K::FqPolyRepField, Q::FpField)
  d = degree(K)
  BLoverK = powers(gen(K), d - 1)
  m = identity_matrix(Q, d)
  return BLoverK, m
end

function _field_as_vector_space(K::FqField, Q::FqField)
  @assert absolute_degree(Q) == 1
  d = absolute_degree(K)
  BLoverK = powers(Nemo._gen(K), d - 1)
  m = identity_matrix(Q, d)
  return BLoverK, m
end

function _field_as_vector_space(f)
  K = domain(f)
  L = codomain(f)
  d = div(degree(L), degree(K))
  a = absolute_primitive_element(L)
  #BLoverK = elem_type(L)[a^i for i in 0:(d- 1)]
  BLoverK = powers(a, d - 1)
  BK = absolute_basis(K)
  absB = elem_type(L)[]
  for i in 1:d
    for j in 1:length(BK)
      push!(absB, BLoverK[i] * f(BK[j]))
    end
  end

  ad = absolute_degree(L)

  absbasismat = zero_matrix(FlintQQ, ad, ad)

  for i in 1:ad
    c = absolute_coordinates(absB[i])
    for j in 1:ad
      absbasismat[i, j] = c[j]
    end
  end

  absbasismatinv = inv(absbasismat)

  m = zero_matrix(K, ad, d)
  for i in 1:d
    for j in 1:degree(K)
      m[(i - 1)*degree(K) + j, i] = BK[j]
    end
  end

  return BLoverK, change_base_ring(K, absbasismatinv) * m
end

mutable struct FldToVecMor{R, S, T, U, V}
  L::R
  K::S
  f::T
  M::U
  B::V
  isone::Bool

  function FldToVecMor(L, f::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField})
    return FldToVecMor(f)
  end

  function FldToVecMor(f::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField})
    K = domain(f)
    L = codomain(f)
    B, M = _field_as_vector_space(f)
    B = B
    M = M
    z = new{typeof(L), typeof(K), typeof(f), typeof(M), typeof(B)}(L, K, f, M, B)
    z.isone = isone(M)
    return z
  end

  function FldToVecMor(L, Q)
    K = Q
    L = L
    B, M = _field_as_vector_space(L, Q)
    B = B
    M = M
    f = identity
    z = new{typeof(L), typeof(K), typeof(f), typeof(M), typeof(B)}(L, K, f, M, B)
    z.isone = isone(M)
    return z
  end

end

function image(f::FldToVecMor{T, QQField}, a::NumFieldElem) where {T <: NumField}
  @assert parent(a) == f.L
  L = parent(a)
  d = absolute_degree(L)
  K = f.K
  entries = map(K, absolute_coordinates(a))
  z = matrix(K, 1, d, entries)
  if f.isone
    v = z
  else
    v = z * f.M
  end
  return elem_type(K)[v[1, i] for i in 1:ncols(v)]
end

function image(f::FldToVecMor{AbsSimpleNumField, AbsSimpleNumField}, a::AbsSimpleNumFieldElem)
  @assert parent(a) == f.L
  L = parent(a)
  d = absolute_degree(L)
  K = f.K
  entries = map(K, absolute_coordinates(a))
  z = matrix(K, 1, d, entries)
  if f.isone
    v = z
  else
    v = z * f.M
  end
  return elem_type(K)[v[1, i] for i in 1:ncols(v)]
end

function image(f::FldToVecMor{RelSimpleNumField{AbsSimpleNumFieldElem}, AbsSimpleNumField}, a::RelSimpleNumFieldElem{AbsSimpleNumFieldElem})
  @assert parent(a) == f.L
  L = parent(a)
  d = degree(L)
  K = f.K
  z = matrix(K, 1, d, elem_type(K)[coeff(a, i) for i in 0:(d - 1)])
  if f.isone
    v = z
  else
    v = z * f.M
  end
  return elem_type(K)[v[1, i] for i in 1:ncols(v)]
end

function image(f::FldToVecMor{T}, a) where {T <: FinField}
  @assert parent(a) == f.L
  L = parent(a)
  d = degree(L)
  K = f.K
  z = matrix(K, 1, d, elem_type(K)[K(T === FqField ? Nemo._coeff(a, i) : coeff(a, i)) for i in 0:(d - 1)])
  if f.isone
    v = z
  else
    v = z * f.M
  end
  return elem_type(K)[v[1, i] for i in 1:ncols(v)]
end

function preimage(f::FldToVecMor, v::Vector)
  @assert parent(v[1]) == f.K
  return dot(f.B, map(f.f, v))::elem_type(f.L)
end

function preimage(f::FldToVecMor{FqField}, v::Vector)
  @assert parent(v[1]) == f.K
  return dot(f.B, (f.L).(map(f.f, v)))::elem_type(f.L)
end

