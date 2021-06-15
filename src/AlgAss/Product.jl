function product_algebra(C::Vector)
  R = base_ring(C[1])
  T = elem_type(R)
  S = eltype(C)
  A = AlgProd{T, S}(R, C)
  return A
end

one(A::AlgProd) = A([one(c) for c in components(A)])

base_ring(A::AlgProd{T}) where {T} = A.base_ring::parent_type(T)

function (A::AlgProd{T, S})(C::Vector) where {T, S}
  return AlgProdElem{T, typeof(A), eltype(C)}(A, C)
end

function (A::AlgProd{T, S})(C::Vector{T}) where {T, S}
  @assert length(C) == dim(A)
  res = elem_type(S)[]
  CA = components(A)
  j = 1
  for i in 1:length(C)
    push!(res, CA[i](C[j:j + dim(CA[i]) - 1]))
    j += dim(CA[i])
  end
  return A(res)
end

(A::AlgProd{T, S})(c::T) where {T, S} = A([c for i in 1:length(components(A))])

function (A::AlgProd{T, S})() where {T, S}
  res = elem_type(S)[]
  for C in components(A)
    push!(res, zero(C))
  end
  return A(res)
end

Base.show(io::IO, x::AlgProdElem) = print(io, x.components)

components(A::AlgProd) = A.components

elem_type(A::AlgProd{T, S}) where {T, S} = AlgProdElem{T, typeof(A), elem_type(S)}
elem_type(A::Type{AlgProd{T, S}}) where {T, S} = AlgProdElem{T, typeof(A), elem_type(S)}

dim(A::AlgProd) = sum(dim(c) for c in components(A))

function any_order(A::AlgProd)
  C = components(A)
  l = length(C)
  res = elem_type(A)[]
  for i in 1:length(C)
    B = C[i]
    O = any_order(B)
    for b in basis_alg(O)
      v = [zero(C[j]) for j in 1:length(C)]
      v[i] = b
      push!(res, A(v))
    end
  end
  return Order(A, res)
end

function *(a::AlgProdElem, b::AlgProdElem)
  return parent(a)([a.components[i] * b.components[i] for i in 1:length(a.components)])
end

function +(a::AlgProdElem, b::AlgProdElem)
  return parent(a)([a.components[i] + b.components[i] for i in 1:length(a.components)])
end

function elem_from_mat_row(A::AlgProd, M::fmpz_mat, i::Int, d::fmpz)
  return A([M[i, j]//d for j in 1:dim(A)])
end

function coefficients(a::AlgProdElem; copy::Bool = true)
  if isdefined(a, :coeffs)
    c = a.coeffs
  else
    c = reduce(vcat, [ coefficients(a.components[i]) for i in 1:length(a.components)])
    a.coeffs = c
  end
  if copy
    return deepcopy(a.coeffs)
  end
  return a.coeffs
end

iscommutative(A::AlgProd) = all(iscommutative(c) for c in components(A))
