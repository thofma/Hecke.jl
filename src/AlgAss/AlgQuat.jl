@doc raw"""
    quaternion_algebra(K::Field, a, b) -> QuaternionAlgebra

Return the quaternion algebra $(a, b | K)$ defined by $i^2 = a$, $j^2 = b$.

At the moment, the field must have characteristic not equal to $2$.

# Examples

```jldoctest
julia> Q = quaternion_algebra(QQ, -1, -1)
Quaternion algebra
  over rational field
  defined by i^2 = -1, j^2 = -1

julia> K, sqrt2 = quadratic_field(2);

julia> Q = quaternion_algebra(K, sqrt2, -1)
Quaternion algebra
  over real quadratic field defined by x^2 - 2
  defined by i^2 = sqrt(2), j^2 = -1
```
"""
function quaternion_algebra(K::Field, a, b)
  if parent(a) === K && parent(b) === K
    return QuaternionAlgebra(K, a, b)
  else
    return QuaternionAlgebra(K, K(a)::elem_type(K), K(b)::elem_type(K))
  end
end

function QuaternionAlgebra(K::Field, a::T, b::T) where { T <: FieldElem }
  @req characteristic(K) != 2 "Characteristic must not be 2"

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

  z = QuaternionAlgebra{T}()

  z.base_ring = K
  z.mult_table = M
  z.one = T[ one(K), zero(K), zero(K), zero(K) ]
  z.std = a, b
  return z
end

dim(A::QuaternionAlgebra) = 4

base_ring(A::QuaternionAlgebra{T}) where {T} = A.base_ring::parent_type(T)

base_ring_type(::Type{QuaternionAlgebra{T}}) where {T} = parent_type(T)

multiplication_table(A::QuaternionAlgebra; copy = false) = A.mult_table

standard_form(A::QuaternionAlgebra) = A.std

has_one(A::QuaternionAlgebra) = true

elem_type(::Type{QuaternionAlgebra{T}}) where {T} = AssociativeAlgebraElem{T, QuaternionAlgebra{T}}

is_commutative(A::QuaternionAlgebra) = false

is_simple(A::QuaternionAlgebra) = true

is_simple_known(A::QuaternionAlgebra) = true

dimension_of_center(A::QuaternionAlgebra) = 1

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, mime::MIME"text/plain", A::QuaternionAlgebra)
  @show_name(io, A)
  @show_special(io, mime, A)
  println(io, "Quaternion algebra")
  io = pretty(io)
  a, b = standard_form(A)
  println(io, Indent(), "over ", Lowercase(), base_ring(A))
  print(io, "defined by i^2 = ", a, ", j^2 = ", b)
  print(io, Dedent())
end

function show(io::IO, A::QuaternionAlgebra)
  if is_terse(io)
    print(io, "Quaternion algebra")
  else
    a, b = standard_form(A)
    io = pretty(io)
    print(io, "Quaternion algebra over ")
    print(terse(io), Lowercase(), base_ring(A))
    print(io, " defined by i^2 = ", a, ", j^2 = ", b)
  end
end

# now for elements

@enable_all_show_via_expressify AssociativeAlgebraElem{T, QuaternionAlgebra{T}} where {T}

function AbstractAlgebra.expressify(a::AssociativeAlgebraElem{T, QuaternionAlgebra{T}}; context = nothing) where {T}
  # Expr(:row, a, b) gives a b
  v = a.coeffs
  sum = Expr(:call, :+)
  for (i, sym) in enumerate([1, :i, :j, :k])
    push!(sum.args, Expr(:call, :*, AbstractAlgebra.expressify(v[i]; context), AbstractAlgebra.expressify(sym; context)))
  end
  return sum
end

################################################################################
#
#  Parent call overloading
#
################################################################################

(A::QuaternionAlgebra{T})(a::IntegerUnion) where {T} = A(map(base_ring(A), [a, 0, 0, 0]))

(A::QuaternionAlgebra{AbsSimpleNumFieldElem})(a::AbsSimpleNumFieldElem) = A(map(base_ring(A), [a, 0, 0, 0]))

(A::QuaternionAlgebra{T})(a::QQFieldElem) where {T} = A(map(base_ring(A), [a, 0, 0, 0]))

#order_type(::Type{QuaternionAlgebra{QQFieldElem}}) = AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}, elem_type(QuaternionAlgebra{QQFieldElem})}
#
order_type(::Type{QuaternionAlgebra{T}}) where {T <: NumFieldElem} = AlgAssRelOrd{T, fractional_ideal_type(order_type(parent_type(T))), QuaternionAlgebra{T}}

################################################################################
#
#  Conjugation
#
################################################################################

function standard_involution(A::QuaternionAlgebra{T}) where {T}
  if isdefined(A, :std_inv)
    return A.std_inv::morphism_type(QuaternionAlgebra{T}, QuaternionAlgebra{T})
  else
    f = __standard_involution(A)
    A.std_inv = f
    return f
  end
end

@doc raw"""
    conjugate(a::AssociativeAlgebraElem{_, QuaternionAlgebra})
                                 -> AssociativeAlgebraElem{_, QuaternionAlgebra}

Return the image of $a$ under the canonical involution of the quaternion
algebra.

# Examples

```jldoctest
julia> Q = quaternion_algebra(QQ, -1, -1); a = Q([1, 1, 1, 1])
1 + i + j + k

julia> conjugate(a)
1 - i - j - k
```
"""
function conjugate(a::AssociativeAlgebraElem{T, QuaternionAlgebra{T}}) where {T}
  return standard_involution(parent(a))(a)
end

function trred(a::AssociativeAlgebraElem{T, QuaternionAlgebra{T}}) where {T}
  return (a + conjugate(a)).coeffs[1]
end

function normred(a::AssociativeAlgebraElem{T, QuaternionAlgebra{T}}) where {T}
  return (a * conjugate(a)).coeffs[1]
end

function reduced_charpoly(a::AssociativeAlgebraElem{T, QuaternionAlgebra{T}}) where {T}
  A = parent(a)
  R = polynomial_ring(base_ring(A), "x", cached = false)[1]
  return R([normred(a), -trred(a), one(base_ring(A))])
end

function standard_involution(A::StructureConstantAlgebra{T}) where {T}
  return __standard_involution(A)
end

function __standard_involution(A)
  BB = basis(A)

  if isone(BB[1])
    return ___standard_involution(A)
  end

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

  _A, _AtoA = _change_basis(A, B)

  _f = ___standard_involution(_A)

  M = zero_matrix(base_ring(A), n, n)

  g = inv(_AtoA) * _f * _AtoA

  for i in 1:n
    elem_to_mat_row!(M, i, g(BB[i]))
  end

  return hom(A, A, M, inv(M))
end

function isomorphism(::Type{QuaternionAlgebra}, A::StructureConstantAlgebra)
  @req characteristic(base_ring(A)) != 2 "Characteristic must not be 2"
  fl, iso = _is_quaternion_algebra(A)
  !fl && error("Not an quaternion algebra")
  return iso
end

# John Voight, "Quaternion algebra companion", Algorithm 4.6.1
# https://math.dartmouth.edu/~jvoight/hints-solns.pdf
function _is_quaternion_algebra(A::StructureConstantAlgebra)
  K = base_ring(A)
  if dim(A) != 4 || dimension_of_center(A) != 1
    return false, Nemo.@new_struct(morphism_type(QuaternionAlgebra{elem_type(K)}, typeof(A)))
  end

  f = standard_involution(A)
  G = zero_matrix(K, 4, 4)
  B = copy(basis(A))
  # Make one(A) the first element of B
  for i in 1:4
    if dot(B[i].coeffs, one(A).coeffs) != 0
      B[i] = one(A)
      B[1], B[i] = B[i], B[1]
      break
    end
  end
  @assert B[1] == one(A)
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
    return false, Nemo.@new_struct(morphism_type(QuaternionAlgebra{elem_type(K)}, typeof(A)))
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

  QA = QuaternionAlgebra(K, newa, newb)

  #@show stdbasis

  #@show basis(A)

  SB = basis_matrix(stdbasis)# * basis_matrix(B)

  #@show SB

  for i in 1:4
    @assert sum(SB[i, j] * basis(A)[j] for j in 1:4) == stdbasis[i]
  end

  SBinv = inv(SB)

  return true, hom(QA, A, SB, SBinv)
end

################################################################################
#
#  Reduce standard generators
#
################################################################################

function _reduce_standard_form(a::AbsSimpleNumFieldElem, b::AbsSimpleNumFieldElem)
  K = parent(a)
  if is_rational(a) && is_rational(b)
    n, m, ap, bp = _reduce_standard_form(QQ(a), QQ(b))
    return K(n), K(m), K(ap), K(bp)
  else
    return one(K), one(K), a, b
  end
end

function _reduce_standard_form(a::QQFieldElem, b::QQFieldElem)
  n = denominator(a)
  ap = a * denominator(a)^2
  m = denominator(b)
  bp = b * denominator(b)^2

  apabs = abs(ap)

  while apabs > 1 && is_square(numerator(apabs))
    sq = sqrt(numerator(apabs))
    n = n//sq
    apabs = apabs//sq^2
  end

  ap = sign(ap) * apabs

  bpabs = abs(bp)

  while bpabs > 1 && is_square(numerator(bpabs))
    #@show numerator(bpabs)
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
  G = zero_matrix(QQ, d, d)
  for i in 1:d
    for j in 1:d
      G[i, j] = ZZ(absolute_tr(trred(B[i] * f(B[j]))))//2
    end
  end

  # TODO: Replace this by short_vectors_gram(M, nrr) once it works
  @assert !iszero(det(G))
  V = _short_vectors_gram(Vector, G, ZZRingElem(b), hard = true)
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
  @assert A isa QuaternionAlgebra
  OF = base_ring(O)
  u, mu = unit_group(lll(OF))
  q, mq = quo(u, 2)
  norms = ZZRingElem[]
  gens = elem_type(O)[]
  for e in q
    _x = mu(mq\e)
    _n = abs(ZZ(absolute_tr(_x)))
    # Reduce modulo squares, so that the trace is hopefully small
    x = evaluate(reduce_mod_powers(elem_in_nf(_x), 2))
    n = abs(ZZ(absolute_tr(x)))
    if _n < n
      # the old x has smaller trace
      x = _x
      n = _n
    end
    if !(n in norms)
      newel = enumerate(O, Int(n), true)
      for un in newel
        if is_unit(un) && !(un in gens)
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

  @assert all(is_unit(u) for u in gens)

  return gens
end

function unit_group_modulo_scalars(O::AlgAssAbsOrd)
  A = algebra(O)
  @assert A isa QuaternionAlgebra
  return enumerate(O, 1)
end

function _unit_group_generators_quaternion(O::Union{AlgAssRelOrd, AlgAssAbsOrd}; GRH::Bool = true)
  gens1 = unit_group_modulo_scalars(O)
  u, mu = unit_group(base_ring(O); GRH = GRH)
  A = algebra(O)
  gens2 = [ O(A(elem_in_nf(mu(u[i])))) for i in 1:ngens(u) ]
  return append!(gens1, gens2)
end

### change basis

function _change_basis(A::StructureConstantAlgebra, bas)
  n = dim(A)
  M = zero_matrix(base_ring(A), n, n)
  N = zero_matrix(base_ring(A), n, n)

  for i in 1:n
    elem_to_mat_row!(M, i, bas[i])
  end

  # This is the "adjusted" basis matrix
  invM = inv(M)

  K = base_ring(A)

  mt = Array{elem_type(K), 3}(undef, n, n, n)

  for i in 1:n
    for j in 1:n
      c = bas[i] * bas[j]
      t = matrix(base_ring(A), 1, dim(A), c.coeffs) * invM
      @assert sum(t[1, i] * bas[i] for i in 1:n) == c
      for k in 1:n
        mt[i, j, k] = t[1, k]
      end
    end
  end

  B = StructureConstantAlgebra(K, mt)
  h = hom(B, A, M, invM)
  return B, h
end

function ___standard_involution(A)
  n = dim(A)
  o = one(A)

  @assert isone(basis(A)[1])

  N = zero_matrix(base_ring(A), n, n)

  K = base_ring(A)

  B = basis(A)

  @assert isone(B[1])
  t = elem_type(base_ring(A))[]
  push!(t, zero(K))
  for i in 2:n
    v = matrix(K, 1, n, (B[i]^2).coeffs)
    ti = v[1, i]
    push!(t, ti)
    _ni = B[i]^2 - ti * B[i]
    @assert all(i -> iszero(_ni.coeffs[i]), 2:n)
  end

  for i in 2:n
    for j in (i+1):n
      nij = (B[i] + B[j])^2 - (t[i] + t[j])*(B[i] + B[j])
      @assert all(i -> iszero(nij.coeffs[i]), 2:n)
    end
  end

  for i in 1:n
    b = i == 1 ? B[i] : t[i] - B[i]
    v = matrix(base_ring(A), 1, n, b.coeffs)
    for j in 1:n
      N[i, j] = v[1, j]
    end
  end
  invol = N
  return hom(A, A, invol, inv(invol))
end

function _is_principal_maximal_quaternion_generic_proper(a, M, side = :right)
  A = algebra(M)
  f = standard_involution(A)
  K = base_ring(A)
  #@assert right_order(a) == M
  @assert _test_ideal_sidedness(a, M, :right)
  nr = normred(a)
  nr = simplify(nr)
  #@show norm(nr)
  #@show nr
  fl, c = is_principal_with_data(nr)
  if !fl
    return false, zero(A)
  end
  #@show c
  fl, u, reps = _reps_for_totally_positive(c, K)
  if !fl
    return false, zero(A)
  end

  #@show u
  #@show is_totally_positive(u * c)
  #@show u * c

  Babs = absolute_basis(a)
  d = length(Babs)
  G = zero_matrix(ZZ, d, d)
  #@show reps
  for z in reps
    Nnu = z * u * c

    alpha = inv(Nnu)

    _d = denominator(alpha, maximal_order(K))
    alpha = _d * alpha

    #@show is_integral(alpha)

    for i in 1:d
      for j in 1:d
        G[i, j] = ZZ(absolute_tr(alpha * trred(Babs[i] * f(Babs[j]))))
      end
    end

    B = 2 * trace(alpha * Nnu)

    @assert is_integral(B)

    ##@show Hecke._eltseq(G)
    #
    #@show denominator(G)

    #_d = degree(base_ring(A))

    #@show B

    v = _short_vectors_gram_integral(Vector, G, ZZ(B), hard = true)

    #if min == degree(base_ring(A))
    for w in v
      xi = sum(w[1][i] * Babs[i] for i in 1:length(Babs))
      if abs(norm(normred(xi))) == norm(normred(a))
        @assert xi in a
        @assert xi * M == a
        return true, xi
      end
    end
  end
  # TODO: Replace this by short_vectors_gram(M, nrr) once it works
  return false, zero(A)
end

################################################################################
#
#  Conversion to StructureConstantAlgebra
#
################################################################################

function StructureConstantAlgebra(A::QuaternionAlgebra)
  K = base_ring(A)
  B = StructureConstantAlgebra(K, A.mult_table)
  return B, hom(A, B, identity_matrix(K, 4), identity_matrix(K, 4))
end

################################################################################
#
#  Zero-divisors for split algebras
#
################################################################################

@doc raw"""
    is_split_with_zero_divisor(A::QuaternionAlgebra) -> Bool, AssociativeAlgebraElem

Given a quaternion algebra $A$, return whether $A$ is split together with an element,
which is a zero-divisor in case $A$ is split.

# Examples

```jldoctest
julia> A = quaternion_algebra(QQ, 1, 4);

julia> is_split_with_zero_divisor(A)
(true, 1 + i)

julia> A = quaternion_algebra(QQ, -1, -1);

julia> is_split_with_zero_divisor(A)
(false, 0)
```
"""
function is_split_with_zero_divisor(A::QuaternionAlgebra{<:Union{QQFieldElem, AbsSimpleNumFieldElem}})
  if !is_split(A)
    return false, zero(A)
  end

  _, i, j, k = basis(A)

  # reduced norm is t^2 - a x^2 - b y^2 + ab z^2

  # let's do it via norm norm equations

  a, b = standard_form(A)

  fl, asqrt = is_square_with_sqrt(a)
  if fl
    alpha = asqrt + i
    @assert norm(alpha) == 0
    return true, alpha
  end

  fl, bsqrt = is_square_with_sqrt(b)
  if fl
    alpha = bsqrt + j
    @assert norm(alpha) == 0
    return true, alpha
  end

  d = denominator(a)
  aa = d^2 * a
  K, = radical_extension(2, aa)
  c = norm_equation(K, b)
  # b = nr(c) = nr(x + y * sqrt(aa)) = x^2 - y^2 d^2 * a = x^2 - (y * d)^2 * a
  alpha = coeff(c, 0) + coeff(c, 1)* d * i + j
  @assert !is_zero(alpha)
  @assert norm(alpha) == 0
  return true, alpha
end
