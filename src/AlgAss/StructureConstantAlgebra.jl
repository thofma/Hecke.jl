################################################################################
#
#  Derived types
#
################################################################################

elem_type(::Type{StructureConstantAlgebra{T}}) where {T} = AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}

# Definitions for orders
order_type(::Type{StructureConstantAlgebra{QQFieldElem}}) = AlgAssAbsOrd{StructureConstantAlgebra{QQFieldElem}, ZZRing}

#order_type(::Type{T}, ::Type{ZZRing}) where {T} = AlgAssAbsOrd{ZZRing, T}
#
#order_type(::Type{StructureConstantAlgebra{T}}) where {T <: NumFieldElem} = AlgAssRelOrd{T, fractional_ideal_type(order_type(parent_type(T)))}

################################################################################
#
#  Constructors
#
################################################################################

@doc raw"""
    structure_constant_algebra(R::Ring, sctable::Array{_, 3}; one::Vector = nothing,
                                                              check::Bool = true)

Given an array with dimensions $(d, d, d)$ and a ring $R$, return the
$d$-dimensional structure constant algebra over $R$. The basis `e` of $R$
satisfies `e[i] * e[j] = sum(sctable[i,j,k] * e[k] for k in 1:d)`.

Unless `check = false`, this includes (time consuming) associativity and
distributivity checks.  If `one` is given, record the element with the
supplied coordinate vector as the one element of the algebra.

# Examples

```jldoctest
julia> associative_algebra(QQ, reshape([1, 0, 0, 2, 0, 1, 1, 0], (2, 2, 2)))
Structure constant algebra of dimension 2 over QQ
```
"""
function structure_constant_algebra(R::Ring, sctable::Array{<:Any, 3}; one = nothing,
                                                                       check::Bool = true)
  return associative_algebra(R, sctable; one = one, check = check)
end

structure_constant_algebra(R::Ring, mult_table::Array{T, 3}, one::Vector{T}; check::Bool = true) where T = StructureConstantAlgebra(R, mult_table, one; check)

@doc raw"""
    structure_constant_algebra(f::PolyRingElem)

Given a polynomial $f$ over a commutative ring $R$, return the quotient ring
$R[X]/(f)$ as an algebra.

# Examples

```jldoctest
julia> Qx, x = QQ["x"]; f = x^2 - 2;

julia> structure_constant_algebra(f)
Structure constant algebra of dimension 2 over QQ
```
"""
structure_constant_algebra(f::PolyRingElem) = StructureConstantAlgebra(f)

function associative_algebra(R::Ring, sctable::Array{<:Any, 3}; one = nothing,
                                                                check::Bool = true)
  @req all(isequal(size(sctable, 1)), size(sctable)) "Multiplication must have dimensions have same length"
  d = size(sctable, 1)
  if one !== nothing
    @req length(one) == size(sctable, 1) "Length ($(length(one))) of vector for one element must be $(d)"
  end

  if (d > 0 && parent(d[1, 1, 1]) === R) ||
       (d == 0 && eltype(sctable) === elem_type(R))
    _sctable = sctable::Array{elem_type(R), 3}
  else
    _sctable = convert(Array{elem_type(R), 3}, map(R, sctable))::Array{elem_type(R), 3}
  end

  if one isa Vector
    if length(one) > 0
      if parent(one[1]) === R
        _one = one
      else
        _one = map(R, one)::Vector{elem_type(R)}
      end
    else
      _one = elem_type(R)[]::Vector{elem_type(R)}
    end
    return StructureConstantAlgebra(R, _sctable, _one; check)
  end
  @assert one isa Nothing
  return StructureConstantAlgebra(R, _sctable; check)
end

associative_algebra(R::Ring, mult_table::Array{T, 3}, one::Vector{T}; check::Bool = true) where T = StructureConstantAlgebra(R, mult_table, one; check)

function StructureConstantAlgebra(R::Ring, mult_table::Array{T, 3}, one::Vector{T}; check::Bool = get_assertion_level(:StructureConstantAlgebra) > 0) where {T}
  if size(mult_table, 1) == 0
    return zero_algebra(R)
  end
  A = StructureConstantAlgebra{T}(R, mult_table, one)
  if check
    @req check_associativity(A) "Multiplication table does not define associative operation"
    @req check_distributivity(A) "Multiplication table does not define distributive operation"
  end
  return A
end

function StructureConstantAlgebra(R::Ring, mult_table::Array{T, 3}; check::Bool = get_assertion_level(:StructureConstantAlgebra) > 0) where {T}
  @req all(isequal(size(mult_table, 1)), size(mult_table)) "Multiplication must have dimensions have same length"
  if size(mult_table, 1) == 0
    return zero_algebra(R)
  end
  A = StructureConstantAlgebra{T}(R)
  A.mult_table = mult_table
  A.iszero = false
  has_one, one = find_one(A)
  A.has_one = has_one
  if has_one
    A.one = one
  end
  if check
    @req check_associativity(A) "Multiplication table does not define associative operation"
    @req check_distributivity(A) "Multiplication table does not define distributive operation"
  end
  return A
end

# Does anyone actually use this?
function StructureConstantAlgebra(R::Ring, d::Int, arr::Vector{T}) where {T}
  if d == 0
    return zero_algebra(R)
  end
  mult_table = Array{T, 3}(undef, d, d, d)
  n = d^2
  for i in 1:d
    for j in 1:d
      for k in 1:d
        mult_table[i, j, k] = arr[(i - 1) * n + (j - 1) * d + k]
      end
    end
  end
  return StructureConstantAlgebra(R, mult_table)
end

@doc raw"""
    structure_constant_algebra(K::SimpleNumField) -> StructureConstantAlgebra, Map

Given a number field $L/K$, return $L$ as a $K$-algebra $A$ together with a
$K$-linear map $A \to L$.

# Examples

```jldoctest
julia> L, = quadratic_field(2);

julia> structure_constant_algebra(L)
(Structure constant algebra of dimension 2 over QQ, Map: structure constant algebra -> real quadratic field)
```
"""
function structure_constant_algebra(K::SimpleNumField)
  StructureConstantAlgebra(K)
end

function StructureConstantAlgebra(K::SimpleNumField)
  A = StructureConstantAlgebra(defining_polynomial(K))
  k = base_field(K)
  m = AbsAlgAssToNfAbsMor(A, K, identity_matrix(k, dim(A)), identity_matrix(k, dim(A)))
  A.maps_to_numberfields = [ (K, m) ]
  return A, m
end

################################################################################
#
#  Zero algebra
#
################################################################################

function zero_algebra(R::Ring)
  A = StructureConstantAlgebra{elem_type(R)}(R)
  A.iszero = true
  A.is_commutative = 1
  A.has_one = true
  A.one = elem_type(R)[]
  A.mult_table = Array{elem_type(R), 3}(undef, 0, 0, 0)
  return A
end

zero_algebra(::Type{StructureConstantAlgebra}, R::Ring) = return zero_algebra(R)

################################################################################
#
#  Basic field access
#
################################################################################

function denominator_of_structure_constant_table(A::StructureConstantAlgebra{QQFieldElem})
  get_attribute!(A, :denominator_of_multiplication_table) do
    den = one(ZZ)
    mt = structure_constant_table(A)
    d = dim(A)
    for i in 1:d
      for j in 1:d
        for k in 1:d
          den = lcm!(den, den, denominator(mt[i, j, k]))
        end
      end
    end
    return den
  end::ZZRingElem
end

# use abstract doc
base_ring(A::StructureConstantAlgebra{T}) where {T} = A.base_ring::parent_type(T)

# use abstract doc
base_ring_type(::Type{StructureConstantAlgebra{T}}) where {T} = parent_type(T)

# use abstract doc
has_one(A::StructureConstantAlgebra) = A.has_one

# use abstract doc
iszero(A::StructureConstantAlgebra) = A.iszero

function Generic.dim(A::StructureConstantAlgebra)
  if iszero(A)
    return 0
  end
  return size(structure_constant_table(A, copy = false), 1)
end

@doc raw"""
    structure_constant_table(A::StructureConstantAlgebra; copy::Bool = true) -> Array{_, 3}

Given an algebra $A$, return the structure constant table of $A$. See
[`structure_constant_algebra`](@ref) for the defining property.

# Examples

```jldoctest
julia> A = associative_algebra(QQ, reshape([1, 0, 0, 2, 0, 1, 1, 0], (2, 2, 2)));

julia> structure_constant_table(A)
2×2×2 Array{QQFieldElem, 3}:
[:, :, 1] =
 1  0
 0  2

[:, :, 2] =
 0  1
 1  0
```
"""
function structure_constant_table(A::StructureConstantAlgebra; copy::Bool = true)
  return multiplication_table(A; copy = copy)
end

function multiplication_table(A::StructureConstantAlgebra; copy::Bool = true)
  if copy
    return deepcopy(A.mult_table)
  else
    return A.mult_table
  end
end

################################################################################
#
#  Commutativity
#
################################################################################

is_commutative_known(A::StructureConstantAlgebra) = (A.is_commutative != 0)

function is_commutative(A::StructureConstantAlgebra)
  if is_commutative_known(A)
    return A.is_commutative == 1
  end
  for i = 1:dim(A)
    for j = i + 1:dim(A)
      if structure_constant_table(A, copy = false)[i, j, :] != structure_constant_table(A, copy = false)[j, i, :]
        A.is_commutative = 2
        return false
      end
    end
  end
  A.is_commutative = 1
  return true
end

################################################################################
#
#  Finding the one
#
################################################################################

# This only works if base_ring(A) is a field (probably)
# Returns (true, one) if there is a one and (false, something) if not.
function find_one(A::StructureConstantAlgebra)
  if iszero(A)
    return true, elem_type(base_ring(A))[]
  end
  n = dim(A)
  M = zero_matrix(base_ring(A), n^2, n)
  c = zero_matrix(base_ring(A), n^2, 1)
  for k = 1:n
    kn = (k - 1)*n
    c[kn + k, 1] = base_ring(A)(1)
    for i = 1:n
      for j = 1:n
        M[i + kn, j] = deepcopy(structure_constant_table(A, copy = false)[j, k, i])
      end
    end
  end
  fl, cc = can_solve_with_solution(M, c; side = :right)
  one = elem_type(base_ring(A))[cc[i, 1] for i = 1:n]
  return true, one
end

associative_algebra(f::PolyRingElem) = StructureConstantAlgebra(f)

function StructureConstantAlgebra(f::PolyRingElem)
  R = base_ring(parent(f))
  n = degree(f)
  Rx = parent(f)
  x = gen(Rx)
  B = Vector{elem_type(Rx)}(undef, 2*n - 1)
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
  A = StructureConstantAlgebra(R, mult_table, one)
  A.is_commutative = 1
  return A
end

function StructureConstantAlgebra(A::StructureConstantAlgebra)
  R = base_ring(A)
  d = dim(A)
  return A, hom(A, A, identity_matrix(R, d), identity_matrix(R, d))
end

###############################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::StructureConstantAlgebra)
  if is_terse(io)
    print(io, "Structure constant algebra")
  else
    io = pretty(io)
    print(io, "Structure constant algebra of dimension ", dim(A), " over ")
    print(terse(io), Lowercase(), base_ring(A))
  end
end

################################################################################
#
#  Subalgebra
#
################################################################################

# Builds a multiplication table for the _subalgebra of A with basis matrix B.
# We assume ncols(B) == dim(A).
# A rref of B will be computed IN PLACE! If return_LU is Val{true}, a LU-factorization
# of transpose(rref(B)) is returned.
function _build_subalgebra_mult_table!(A::StructureConstantAlgebra{T}, B::MatElem{T}, ::Val{return_LU} = Val(false); is_commutative = false) where { T, return_LU }
  K = base_ring(A)
  n = dim(A)
  r = rref!(B)
  if r == 0
    if return_LU
      return Array{elem_type(K), 3}(undef, 0, 0, 0), solve_init(B)
    else
      return Array{elem_type(K), 3}(undef, 0, 0, 0)
    end
  end

  basis = Vector{elem_type(A)}(undef, r)
  for i = 1:r
    basis[i] = elem_from_mat_row(A, B, i)
  end

  Btr = transpose(B)
  #_, p, L, U = lu(Btr)
  LL = solve_init(Btr)

  iscom = is_commutative || Hecke.is_commutative(A)

  mult_table = Array{elem_type(K), 3}(undef, r, r, r)
  c = A()
  d = zero_matrix(K, n, 1)
  for i = 1:r
    for j = 1:r
      if iscom && j < i
        continue
      end
      c = mul!(c, basis[i], basis[j])
      #for i in 1:nrows(d)
      #  d[p[i], 1] = c.coeffs[i]
      #end
      #_d = deepcopy(d)
      #mc = matrix(K, length(c.coeffs), 1, c.coeffs)
      #@assert can_solve_with_solution(Btr, mc)[1]
      #d = _solve_lt(L, d)
      #d = _solve_ut(U, d)
      #@assert Btr * d == mc
      dd = solve(LL, c.coeffs, side = :right)
      for k = 1:r
        #@assert dd[k] == d[k, 1]
        mult_table[i, j, k] = dd[k]
        #mult_table[i, j, k] = d[k, 1]
        if iscom && i != j
          #@assert dd[k] == d[k, 1]
          mult_table[j, i, k] = dd[k]
          #mult_table[j, i, k] = d[k, 1]
        end
      end
    end
  end

  if return_LU
    return mult_table, LL #p, L, U, LL
  else
    return mult_table
  end
end

@doc raw"""
     _subalgebra(A::StructureConstantAlgebra, e::AssociativeAlgebraElem, idempotent::Bool = false,
                action::Symbol = :left)
       -> StructureConstantAlgebra, AbsAlgAssMor

Given an algebra $A$ and an element $e$, this function constructs the algebra
$e \cdot A$ (if `action == :left`) respectively $A \cdot e$ (if `action == :right`)
and a map from this algebra to $A$.
If `idempotent` is `true`, it is assumed that $e$ is idempotent in $A$.
"""
function _subalgebra(A::StructureConstantAlgebra{T}, e::AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}, idempotent::Bool = false, action::Symbol = :left) where {T}
  @assert parent(e) == A
  R = base_ring(A)
  n = dim(A)
  # This is the basis of e*A, resp. A*e
  B1 = representation_matrix(e, action)
  mult_table, LL = _build_subalgebra_mult_table!(A, B1, Val(true))

  r = size(mult_table, 1)

  if r == 0
    eA = zero_algebra(R)
    return eA, hom(eA, A, zero_matrix(R, 0, n))
  end

  # The basis matrix of e*A resp. A*e with respect to A is
  basis_mat_of_eA = sub(B1, 1:r, 1:n)

  if idempotent
    #LLsolvectx = solve_init(LL)
    # c = A()
    # d = zero_matrix(R, n, 1)
    # for k = 1:n
    #   d[p[k], 1] = e.coeffs[k]
    # end
    # d = _solve_lt(L, d)
    # d = _solve_ut(U, d)
    # v = Vector{elem_type(R)}(undef, r)
    # for i in 1:r
    #   v[i] = d[i, 1]
    # end
    vv = solve(LL, e.coeffs, side = :right)
    #@assert v == vv[1:r]
    eA = StructureConstantAlgebra(R, mult_table, vv[1:r])
  else
    eA = StructureConstantAlgebra(R, mult_table)
  end

  if A.is_commutative == 1
    eA.is_commutative = 1
  end

  if idempotent
    # We have the map eA -> A, given by the multiplying with basis_mat_of_eA.
    # But there is also the canonical projection A -> eA, a -> ea.
    # We compute the corresponding matrix.
    B2 = representation_matrix(e, action)
    C = zero_matrix(R, n, r)
    for i in 1:n
      #for k = 1:n
      #  d[p[k], 1] = B2[i, k]
      #end
      #d = _solve_lt(L, d)
      #d = _solve_ut(U, d)
      dd = solve(LL, [B2[i, k] for k in 1:n], side = :right)
      #@assert [d[i, 1] for i in 1:nrows(d)] == dd
      for k in 1:r
        C[i, k] = dd[k]
      end
    end
    eAtoA = hom(eA, A, basis_mat_of_eA, C)
  else
    eAtoA = hom(eA, A, basis_mat_of_eA)
  end
  return eA, eAtoA
end

@doc raw"""
    _subalgebra(A::StructureConstantAlgebra, basis::Vector{AssociativeAlgebraElem}) -> StructureConstantAlgebra, AbsAlgAssMor

Returns the _subalgebra of $A$ generated by the elements in `basis` and a map
from this algebra to $A$.
"""
function _subalgebra(A::StructureConstantAlgebra{T}, basis::Vector{AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}}; is_commutative = false) where T
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  for i = 1:length(basis)
    elem_to_mat_row!(M, i, basis[i])
  end
  mt = _build_subalgebra_mult_table!(A, M; is_commutative = is_commutative)
  B = StructureConstantAlgebra(base_ring(A), mt)
  return B, hom(B, A, sub(M, 1:length(basis), 1:dim(A)))
end

###############################################################################
#
#  Center
#
###############################################################################

function _rep_for_center!(M::T, A::StructureConstantAlgebra) where T<: MatElem
  n = dim(A)
  mt = structure_constant_table(A, copy = false)
  tt = zero(base_ring(A))
  for i=1:n
    for j = 1:n
      for k = 1:n
        if tt isa QQFieldElem
          sub!(tt, mt[i, j, k], mt[j, i, k])
          M[k + (i-1)*n, j] = tt
        else
          M[k + (i-1)*n, j] = mt[i, j, k] - mt[j, i, k]
        end
      end
    end
  end
  return nothing
end

function center(A::StructureConstantAlgebra{T}) where {T}
  if is_commutative(A)
    B, mB = StructureConstantAlgebra(A)
    return B, mB
  end
  if isdefined(A, :center)
    return A.center::Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, StructureConstantAlgebra{T})}
  end

  n = dim(A)
  M = zero_matrix(base_ring(A), n^2, n)
  # I concatenate the difference between the right and left representation matrices.
  _rep_for_center!(M, A)
  B = kernel(M, side = :right)
  k = ncols(B)
  res = Vector{elem_type(A)}(undef, k)
  for i=1:k
    res[i]= A(T[B[j,i] for j=1:n])
  end
  C, mC = _subalgebra(A, res, is_commutative = true)
  A.center = C, mC

  # Store the idempotents of A if known so that the Wedderburn decompositions
  # can align

  if isdefined(A, :decomposition)
    idems = elem_type(C)[has_preimage_with_preimage(mC, StoA(one(S)))[2] for (S, StoA) in A.decomposition]
    set_attribute!(C, :central_idempotents, idems)
  end

  return C, mC
end

################################################################################
#
#  Idempotents
#
################################################################################

# See W. Eberly "Computations for Algebras and Group Representations" p. 126.
# TODO: fix the type
function _find_non_trivial_idempotent(A::StructureConstantAlgebra{T}) where { T } #<: Union{fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, FqPolyRepFieldElem, fqPolyRepFieldElem} }
  if dim(A) == 1
    error("Dimension of algebra is 1")
  end
  while true
    a = rand(A)
    if isone(a) || iszero(a)
      continue
    end
    mina = minpoly(a)
    if is_irreducible(mina)
      if degree(mina) == dim(A)
        error("Algebra is a field")
      end
      continue
    end
    if is_squarefree(mina)
      e = _find_idempotent_via_squarefree_poly(A, a, mina)
    else
      e = _find_idempotent_via_non_squarefree_poly(A, a, mina)
    end
    if isone(e) || iszero(e)
      continue
    end
    return e
  end
end

#function _find_idempotent_via_non_squarefree_poly(A::StructureConstantAlgebra{T}, a::AssociativeAlgebraElem{T}, mina::Union{fpPolyRingElem, FpPolyRingElem, FqPolyRepPolyRingElem, fqPolyRepPolyRingElem}) where { T <: Union{fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, FqPolyRepFieldElem, fqPolyRepFieldElem} }
function _find_idempotent_via_non_squarefree_poly(A::StructureConstantAlgebra{T}, a::AssociativeAlgebraElem{T}, mina) where {T}
  fac = factor(mina)
  if length(fac) == 1
    return zero(A)
  end
  sf_part = one(parent(mina))
  for (k, v) in fac
    mul!(sf_part, sf_part, k)
  end
  b = sf_part(a)
  # This is not really an algebra, only a right sided ideal
  bA, bAtoA = _subalgebra(A, b, false, :left)

  # Find an element e of bA such that e*x == x for all x in bA
  M = zero_matrix(base_ring(A), dim(bA), 0)
  for i = 1:dim(bA)
    M = hcat(M, representation_matrix(bA[i], :right))
  end

  N = zero_matrix(base_ring(A), 0, 1)
  for i = 1:dim(bA)
    N = vcat(N, matrix(base_ring(A), dim(bA), 1, coefficients(bA[i])))
  end
  MN = hcat(transpose(M), N)
  r = rref!(MN)
  be = _solve_ut(sub(MN, 1:r, 1:dim(bA)), sub(MN, 1:r, (dim(bA) + 1):(dim(bA) + 1)))
  e = bAtoA(bA([ be[i, 1] for i = 1:dim(bA) ]))
  return e
end

# A should be semi-simple
# See W. Eberly "Computations for Algebras and Group Representations" p. 89.
function _extraction_of_idempotents(A::StructureConstantAlgebra, only_one::Bool = false)
  Z, ZtoA = center(A)
  if dim(Z) == 1
    error("Dimension of centre is 1")
  end

  a = ZtoA(rand(Z))
  f = minpoly(a)
  while is_irreducible(f)
    if degree(f) == dim(A)
      error("Cannot find idempotents (algebra is a field)")
    end
    a = ZtoA(rand(Z))
    f = minpoly(a)
  end

  fac = factor(f)
  fi = [ k for k in keys(fac.fac) ]
  l = length(fi)
  R = parent(f)
  if only_one
    r = zeros(R, l)
    r[1] = one(R)
    g = crt(r, fi)
    return g(a)
  else
    oneR = one(R)
    zeroR = zero(R)
    gi = Vector{elem_type(R)}(undef, l)
    r = zeros(R, l)
    for i = 1:l
      r[i] = oneR
      gi[i] = crt(r, fi)
      r[i] = zeroR
    end
    return [ g(a) for g in gi ]
  end
end

#function _find_idempotent_via_squarefree_poly(A::StructureConstantAlgebra{T}, a::AssociativeAlgebraElem{T}, mina::Union{fpPolyRingElem, FpPolyRingElem, FqPolyRepPolyRingElem, fqPolyRepPolyRingElem}) where { T <: Union{fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, FqPolyRepFieldElem, fqPolyRepFieldElem} }
# TODO: fix the type
function _find_idempotent_via_squarefree_poly(A::StructureConstantAlgebra{T}, a::AssociativeAlgebraElem{T}, mina) where {T}
  B = StructureConstantAlgebra(mina)
  idemB = _extraction_of_idempotents(B, true)

  e = dot(coefficients(idemB, copy = false), [ a^k for k = 0:(degree(mina) - 1) ])
  return e
end

# TODO: fix the type
function _primitive_idempotents(A::StructureConstantAlgebra{T}) where { T } #<: Union{fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, FqPolyRepFieldElem, fqPolyRepFieldElem} }
  if dim(A) == 1
    return [ one(A) ]
  end

  e = _find_non_trivial_idempotent(A)

  idempotents = Vector{elem_type(A)}()

  eA, m1 = _subalgebra(A, e, true, :left)
  eAe, m2 = _subalgebra(eA, m1\e, true, :right)
  if dim(eAe) == dim(A)
    push!(idempotents, e)
  else
    idems = _primitive_idempotents(eAe)
    append!(idempotents, [ m1(m2(idem)) for idem in idems ])
  end

  f = (1 - e)
  fA, n1 = _subalgebra(A, f, true, :left)
  fAf, n2 = _subalgebra(fA, n1\f, true, :right)

  if dim(fAf) == dim(A)
    push!(idempotents, f)
  else
    idems = _primitive_idempotents(fAf)
    append!(idempotents, [ n1(n2(idem)) for idem in idems ])
  end

  return idempotents
end

################################################################################
#
#  Matrix Algebra
#
################################################################################

# This computes a "matrix type" basis for A.
# See W. Eberly "Computations for Algebras and Group Representations" p. 121.
# TODO: fix the type
function _matrix_basis(A::StructureConstantAlgebra{T}, idempotents::Vector{S}) where { T, S }#<: Union{fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, FqPolyRepFieldElem, fqPolyRepFieldElem}, S <: AssociativeAlgebraElem{T, StructureConstantAlgebra{T}} }
  k = length(idempotents)
  # Compute a basis e_ij of A (1 <= i, j <= k) with
  # e_11 + e_22 + ... + e_kk = 1 and e_rs*e_tu = \delta_st*e_ru.
  new_basis = Vector{elem_type(A)}(undef, k^2) # saved column major: new_basis[i + (j - 1)*k] = e_ij
  for i = 1:k
    new_basis[i + (i - 1)*k] = idempotents[i]
  end

  a = idempotents[1]
  for i = 2:k
    b = idempotents[i]
    e = a + b
    eA, m1 = _subalgebra(A, e, true, :left)
    eAe, m2 = _subalgebra(eA, m1\e, true, :right)

    aa = m2\(m1\(a))
    bb = m2\(m1\(b))

    # We compute an element x of eAe which fulfils
    # aa*x == x, bb*x == 0, x*aa == 0 and x*bb == x.
    M1 = representation_matrix(aa - one(eAe), :left)
    M2 = representation_matrix(bb, :left)
    M3 = representation_matrix(aa, :right)
    M4 = representation_matrix(bb - one(eAe), :right)

    M = hcat(M1, M2, M3, M4)
    xx = eAe(kernel(M, side = :left)[1, :])
    x = m1(m2(xx))

    new_basis[1 + (i - 1)*k] = x # this is e_1i

    # We compute an element y of eAe which fulfils
    # aa*y == 0, bb*y == y, y*aa == y, y*bb == 0, y*xx == bb, xx*y == aa.
    N1 = representation_matrix(aa, :left)
    N2 = representation_matrix(bb - one(eAe), :left)
    N3 = representation_matrix(aa - one(eAe), :right)
    N4 = representation_matrix(bb, :right)
    N5 = representation_matrix(xx, :right)
    N6 = representation_matrix(xx, :left)
    N = hcat(N1, N2, N3, N4, N5, N6)
    NN = zero_matrix(base_ring(A), 4*dim(eAe), 1)
    NN = vcat(NN, matrix(base_ring(A), dim(eAe), 1, coefficients(bb)))
    NN = vcat(NN, matrix(base_ring(A), dim(eAe), 1, coefficients(aa)))
    b, yy = can_solve_with_solution(transpose(N), NN; side = :right)
    @assert b
    y = m1(m2(eAe([ yy[i, 1] for i = 1:dim(eAe) ])))

    new_basis[i] = y # this is e_i1
  end

  for j = 2:k
    jk = (j - 1)*k
    e1j = new_basis[1 + jk]
    for i = 2:k
      new_basis[i + jk] = new_basis[i]*e1j # this is e_ij
    end
  end
  return new_basis
end

# Assumes that A is central and isomorphic to a matrix algebra of base_ring(A)
# TODO: fix the type
function _as_matrix_algebra(A::StructureConstantAlgebra{T}) where { T } # <: Union{fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, FqPolyRepFieldElem, fqPolyRepFieldElem}, S <: AssociativeAlgebraElem{T, StructureConstantAlgebra{T}} }

  idempotents = _primitive_idempotents(A)
  @assert length(idempotents)^2 == dim(A)
  Fq = base_ring(A)

  B = matrix_algebra(Fq, length(idempotents))

  matrix_basis = _matrix_basis(A, idempotents)

  # matrix_basis is another basis for A. We build the matrix for the basis change.
  M = zero_matrix(Fq, dim(A), dim(A))
  for i = 1:dim(A)
    elem_to_mat_row!(M, i, matrix_basis[i])
  end
  return B, hom(A, B, inv(M), M)
end

################################################################################
#
#  Direct product
#
################################################################################

@doc raw"""
    direct_product(algebras::StructureConstantAlgebra...; task::Symbol = :sum)
      -> StructureConstantAlgebra, Vector{AbsAlgAssMor}, Vector{AbsAlgAssMor}
    direct_product(algebras::Vector{StructureConstantAlgebra}; task::Symbol = :sum)
      -> StructureConstantAlgebra, Vector{AbsAlgAssMor}, Vector{AbsAlgAssMor}

Returns the algebra $A = A_1 \times \cdots \times A_k$. `task` can be
":sum", ":prod", ":both" or ":none" and determines which canonical maps
are computed as well: ":sum" for the injections, ":prod" for the projections.
"""
function direct_product(algebras::Vector{<: StructureConstantAlgebra{T}}; task::Symbol = :sum) where T
  @req !isempty(algebras) "Must be at least one algebra for direct product (or specifiy the field)"
  return direct_product(algebras..., task = task)
end

function direct_product(K, algebras::Vector{<: StructureConstantAlgebra{T}}; task::Symbol = :sum) where T
  if length(algebras) == 0
    mt = zeros(K, 0, 0, 0)
    A = StructureConstantAlgebra(K, mt; check = false)
    return A, morphism_type(eltype(algebras), typeof(A))[]
  end
  return direct_product(algebras..., task = task)
end

function direct_product(a::StructureConstantAlgebra{T}, _algebras::StructureConstantAlgebra{T}...; task::Symbol = :sum) where T
  algebras = (a, _algebras...)
  @assert !isempty(algebras)
  @assert all( A -> base_ring(A) == base_ring(algebras[1]), algebras)
  @assert task in [ :prod, :sum, :both, :none ]

  d = sum( dim(A) for A in algebras )
  mt = zeros(base_ring(algebras[1]), d, d, d)
  offset = 0
  for B in algebras
    mtB = structure_constant_table(B, copy = false)
    dd = dim(B)
    for i = 1:dd
      for j = 1:dd
        for k = 1:dd
          mt[i + offset, j + offset, k + offset] = mtB[i, j, k]
        end
      end
    end
    offset += dd
  end
  A = StructureConstantAlgebra(base_ring(algebras[1]), mt; check = false)
  if task == :none
    return A
  end

  if task == :sum || task == :both
    inj = Vector{morphism_type(typeof(A), typeof(algebras[1]))}(undef, length(algebras))
  end
  if task == :prod || task == :both
    proj = Vector{morphism_type(typeof(A), typeof(algebras[1]))}(undef, length(algebras))
  end
  offset = 0
  for i = 1:length(algebras)
    B = algebras[i]
    M = zero_matrix(base_ring(A), dim(A), dim(B))
    for i = 1:dim(B)
      M[i + offset, i] = one(base_ring(A))
    end
    Mt = transpose(M)
    if task == :sum || task == :both
      inj[i] = hom(B, A, Mt, M)
    end
    if task == :prod || task == :both
      proj[i] = hom(A, B, M, Mt)
    end
    offset += dim(B)
  end
  if task == :prod
    return A, proj
  elseif task == :sum
    return A, inj
  else
    return A, proj, inj
  end
end

@doc raw"""
    direct_product(fields::AnticNumberFields...)
      -> StructureConstantAlgebra{QQFieldElem}, Vector{AbsAlgAssToNfAbsMor}
    direct_product(fields::Vector{AnticNumberFields})
      -> StructureConstantAlgebra{QQFieldElem}, Vector{AbsAlgAssToNfAbsMor}

Returns the algebra $A = K_1 \times \cdots \times K_k$ and the projection
maps $A ->> K_i$.
"""
function direct_product(fields::Vector{AbsSimpleNumField})
  return direct_product(fields...)
end

function direct_product(_field::AbsSimpleNumField, _fields::AbsSimpleNumField...)
  fields = (_field, _fields...)
  algebras = Tuple{StructureConstantAlgebra{QQFieldElem}, AbsAlgAssToNfAbsMor{StructureConstantAlgebra{QQFieldElem}, elem_type(StructureConstantAlgebra{QQFieldElem}), AbsSimpleNumField, QQMatrix}}[ StructureConstantAlgebra(K) for K in fields ]
  A, proj, inj = direct_product([ B for (B, m) in algebras ], task = :both)
  A.decomposition = [ (algebras[i][1], inj[i]) for i = 1:length(algebras) ]
  maps_to_fields = Vector{AbsAlgAssToNfAbsMor{StructureConstantAlgebra{QQFieldElem}, elem_type(StructureConstantAlgebra{QQFieldElem}), AbsSimpleNumField, QQMatrix}}(undef, length(fields))
  for i = 1:length(fields)
    # Assumes, that the map algebras[i] -> K is given by the identity matrix
    maps_to_fields[i] = AbsAlgAssToNfAbsMor(A, fields[i], proj[i].mat, proj[i].imat)
  end
  A.maps_to_numberfields = Tuple{AbsSimpleNumField, AbsAlgAssToNfAbsMor{StructureConstantAlgebra{QQFieldElem}, elem_type(StructureConstantAlgebra{QQFieldElem}), AbsSimpleNumField, QQMatrix}}[ (fields[i], maps_to_fields[i]) for i = 1:length(fields) ]
  return A, maps_to_fields
end

################################################################################
#
#  Quaternion algebras
#
################################################################################

# internal use only
function quaternion_algebra2(K::Field, a::T, b::T) where { T <: FieldElem }
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

  return StructureConstantAlgebra(K, M, [ one(K), zero(K), zero(K), zero(K) ])
end

quaternion_algebra2(K::Field, a::Int, b::Int) = quaternion_algebra2(K, K(a), K(b))

quaternion_algebra2(a::Int, b::Int) = quaternion_algebra2(QQ, QQFieldElem(a), QQFieldElem(b))

################################################################################
#
#  Opposite algebra
#
################################################################################

function opposite_algebra(A::StructureConstantAlgebra)
  K = base_ring(A)
  B = basis(A)
  d = dim(A)
  z = Array{elem_type(K), 3}(undef, d, d, d)
  for i in 1:d
    for j in 1:d
      z[i, j, :] = A.mult_table[j, i, :]
    end
  end
  o = one(A).coeffs

  B = StructureConstantAlgebra(K, z, o)
  return B, hom(A, B, identity_matrix(K, d), identity_matrix(K, d))
end
