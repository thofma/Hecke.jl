function AlgQuat(K::Field, a::T, b::T) where { T <: FieldElem }

  M = zeros(K, 4, 4, 4)

  M[1, 1, 1] = one(K) # 1*1=1
  M[1, 2, 2] = one(K) # 1*i=i
  M[1, 3, 3] = one(K) # 1*j=j
  M[1, 4, 4] = one(K) # 1*ij=1

  M[2, 1, 2] = one(K)
  M[2, 2, 1] = a
  M[2, 3, 4] = one(K)
  M[2, 4, 3] = a

  M[3, 1, 3] = one(K)
  M[3, 2, 4] = -one(K)
  M[3, 3, 1] = b
  M[3, 4, 2] = -b

  M[4, 1, 4] = one(K)
  M[4, 2, 3] = -a
  M[4, 3, 2] = b
  M[4, 4, 1] = -a*b

  z = AlgQuat{T}()

  z.base_ring = K
  z.mult_table = M
  z.one = T[ one(K), zero(K), zero(K), zero(K) ]
  z.std = a, b
  return z
end

function show(io::IO, A::AlgQuat)
  print(io, "Quaternion algebra over\n")
  println(IOContext(io, :compact => true), base_ring(A))
  a, b = standard_form(A)
  print(io, "defined by i^2 = ", a, ", j^2 = ", b)
end

function show(io::IO, a::AlgAssElem{T, AlgQuat{T}}) where {T}
  v = a.coeffs
  print(io, v[1], " + ", v[2], " * i + ", v[3], " * j + ", v[4], " * k")
end

dim(A::AlgQuat) = 4

base_ring(A::AlgQuat{T}) where {T} = A.base_ring::parent_type(T)

multiplication_table(A::AlgQuat; copy = false) = A.mult_table

standard_form(A::AlgQuat) = A.std

has_one(A::AlgQuat) = true

elem_type(A::AlgQuat{T}) where {T} = AlgAssElem{T, AlgQuat{T}}

elem_type(::Type{AlgQuat{T}}) where {T} = AlgAssElem{T, AlgQuat{T}}

iscommutative(A::AlgQuat) = false

issimple(A::AlgQuat) = true

issimple_known(A::AlgQuat) = true

dimension_of_center(A::AlgQuat) = 1

(A::AlgQuat{T})(a::Union{Integer, fmpz}) where {T} = A(map(base_ring(A), [a, 0, 0, 0]))

(A::AlgQuat{nf_elem})(a::nf_elem) = A(map(base_ring(A), [a, 0, 0, 0]))

(A::AlgQuat{T})(a::fmpq) where {T} = A(map(base_ring(A), [a, 0, 0, 0]))

################################################################################
#
#  Conjugation
#
################################################################################

function standard_involution(A::AlgQuat{T}) where {T}
  if isdefined(A, :std_inv)
    return A.std_inv::morphism_type(AlgQuat{T}, AlgQuat{T})
  else
    f = __standard_involution(A)
    A.std_inv = f
    return f
  end
end

function conjugate(a::AlgAssElem{T, AlgQuat{T}}) where {T}
  return standard_involution(parent(a))(a)
end

function trred(a::AlgAssElem{T, AlgQuat{T}}) where {T}
  return base_ring(parent(a))(a + conjugate(a))
end

function normred(a::AlgAssElem{T, AlgQuat{T}}) where {T}
  return base_ring(parent(a))(a * conjugate(a))
end

function reduced_charpoly(a::AlgAssElem{T, AlgQuat{T}}) where {T}
  A = parent(a)
  R = PolynomialRing(base_ring(A), "x", cached = false)[1]
  return x^2 - trred(a) * x + normred(a)
end

function standard_involution(A::AlgAss{T}) where {T}
  return __standard_involution(A)
end

function __standard_involution(A)
  B = copy(basis(A))
  n = dim(A)
  o = one(A)
  for i in 1:n
    if dot(o.coeffs, B[i].coeffs) != 0
      B[i] = o
      B[i], B[1] = B[1], B[i]
      break
    end
  end

  M = zero_matrix(base_ring(A), n, n)
  N = zero_matrix(base_ring(A), n, n)
  for i in 1:n
    elem_to_mat_row!(M, i, B[i])
  end
  # This is the "adjusted" basis matrix
  invM = inv(M)

  K = base_ring(A)

  @assert isone(B[1])
  t = elem_type(base_ring(A))[]
  push!(t, 2 * one(base_ring(A)))
  for i in 2:n
    v = matrix(K, 1, n, (B[i]^2).coeffs) * invM
    ti = v[1, i]
    push!(t, ti)
    #_ni = B[i]^2 - ti * B[i]
    #@assert all(i -> iszero(_ni.coeffs[i]), 2:n)
  end

  #for i in 2:n
  #  for j in (i+1):n
  #    nij = (B[i] + B[j])^2 - (t[i] + t[j])*(B[i] + B[j])
  #    @assert all(i -> iszero(nij.coeffs[i]), 2:n)
  #  end
  #end
  for i in 1:n
    b = t[i] - B[i]
    v = matrix(base_ring(A), 1, n, b.coeffs) * invM
    for j in 1:n
      N[i, j] = v[1, j]
    end
  end
  invol = M * N * inv(M)
  return hom(A, A, invol, inv(invol))
end

# John Voight, "Quaternion algebra companion", Algorithm 4.6.1
# https://math.dartmouth.edu/~jvoight/hints-solns.pdf
function isquaternion_algebra(A::AlgAss)
  @assert dim(A) == 4
  @assert dimension_of_center(A) == 1

  f = standard_involution(A)
  K = base_ring(A)
  G = zero_matrix(K, 4, 4)
  B = copy(basis(A))
  @assert dot(B[1].coeffs, one(A).coeffs) != 0
  B[1] = one(A)
  for i in 1:4
    for j in 1:4
      G[i, j] = trred(B[i] * f(B[j]))//2
    end
  end

  F, S = _gram_schmidt(G, identity)
  stdbasis = elem_type(A)[]
  for i in 1:4
    push!(stdbasis, dot(B, [S[i, j] for j in 1:4]))
  end

  @assert stdbasis[1] == 1

  if iszero(det(F))
    return false
  end

  a = stdbasis[2]^2
  b = stdbasis[3]^2

  (scalea, scaleb, newa, newb) = _reduce_standard_form(K(a), K(b))

  stdbasis[2] = scalea * stdbasis[2]
  stdbasis[3] = scaleb * stdbasis[3]

  stdbasis[4] = stdbasis[2] * stdbasis[3]

  @assert stdbasis[2]^2 == A(newa)
  @assert stdbasis[3]^2 == A(newb)

  @assert stdbasis[2] * stdbasis[3] == -stdbasis[3] * stdbasis[2]
  @assert stdbasis[2] * stdbasis[3] == stdbasis[4]

  QA = AlgQuat(K, newa, newb)

  SB = basis_matrix(stdbasis) * basis_matrix(B)

  SBinv = inv(SB)

  return QA, hom(QA, A, SB, SBinv)
end

################################################################################
#
#  Reduce standard generators
#
################################################################################

function _reduce_standard_form(a::fmpq, b::fmpq)
  n = denominator(a)
  ap = a * denominator(a)^2
  m = denominator(b)
  bp = b * denominator(b)^2

  apabs = abs(ap)

  while apabs > 1 && issquare(numerator(apabs))
    sq = sqrt(numerator(apabs))
    n = n//sq
    apabs = apabs//sq^2
  end

  ap = sign(ap) * apabs

  bpabs = abs(bp)

  while bpabs > issquare(numerator(bpabs))
    sq = sqrt(numerator(bpabs))
    m = m//sq
    bpabs = bpabs//sq^2
  end

  bp = sign(bp) * bpabs

  return (n, m, ap, bp)
end

# TODO: Think about this.
_reduce_standard_form(a::T, b::T) where {T} = (one(parent(a)), one(parent(a)), a, b)

################################################################################
#
#  Enumerate
#
################################################################################

# return elements x with absolute_tr(rednorm(x)) <= B (including zero) up to sign!
function Base.enumerate(O::Union{AlgAssRelOrd, AlgAssAbsOrd}, b::Int, equal::Bool = false)
  A = algebra(O)
  f = standard_involution(A)
  B = elem_in_algebra.(absolute_basis(O))
  d = length(B)
  G = zero_matrix(FlintQQ, d, d)
  for i in 1:d
    for j in 1:d
      G[i, j] = FlintZZ(absolute_tr(trred(B[i] * f(B[j]))))//2
    end
  end

  # TODO: Replace this by short_vectors_gram(M, nrr) once it works
  V = _short_vectors_gram(G, fmpz(b)) 
  res = elem_type(O)[]
  for i in 1:length(V)
    y = sum(V[i][1][j] * B[j] for j in 1:d)
    @assert absolute_tr(normred(y)) <= b
    if equal
      if absolute_tr(normred(y)) == b
        push!(res, O(y))
      end
    else
      push!(res, O(y))
    end
  end

  return res
end 

# Thanks Aurel!
# https://mathoverflow.net/questions/250753/finite-group-of-units-in-quaternion-orders
# TODO: There is a faster version in Magma.
function unit_group_modulo_scalars(O::AlgAssRelOrd)
  A = algebra(O)
  @assert A isa AlgQuat
  OF = base_ring(O)
  u, mu = unit_group(OF)
  q, mq = quo(u, 2)
  norms = fmpz[]
  gens = elem_type(O)[]
  for e in q
    x = mu(mq\e)
    n = abs(FlintZZ(absolute_tr(elem_in_nf(x))))
    if !(n in norms)
      newel = enumerate(O, Int(n), true)
      for un in newel
        if isunit(un) && !(un in gens)
          isnew = true
          for oldunits in gens
            if (all(k -> iszero((elem_in_algebra(un) * inv(elem_in_algebra(oldunits))).coeffs[k]), 2:4))
              isnew = false
              break
            end
          end

          if isnew
            push!(gens, un)
          end
        end
      end
      push!(norms, n)
    end
  end
  
  @assert all(isunit(u) for u in gens)

  return gens
end

function unit_group_modulo_scalars(O::AlgAssAbsOrd)
  A = algebra(O)
  @assert A isa AlgQuat
  return enumerate(O, 1)
end

function unit_group_generators(O::Union{AlgAssRelOrd, AlgAssAbsOrd})
  gens1 = unit_group_modulo_scalars(O)
  u, mu = unit_group(base_ring(O))
  gens2 = [ O(mu(u[i])) for i in 1:ngens(u) ]
  return append!(gens1, gens2)
end
