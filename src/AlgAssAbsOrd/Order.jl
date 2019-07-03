export algebra

add_assert_scope(:AlgAssOrd)
add_verbose_scope(:AlgAssOrd)

elem_type(::AlgAssAbsOrd{S, T}) where {S, T} = AlgAssAbsOrdElem{S, T}

elem_type(::Type{AlgAssAbsOrd{S, T}}) where {S, T} = AlgAssAbsOrdElem{S, T}

ideal_type(::AlgAssAbsOrd{S, T}) where {S, T} = AlgAssAbsOrdIdl{S, T}

ideal_type(::Type{AlgAssAbsOrd{S, T}}) where {S, T} = AlgAssAbsOrdIdl{S, T}

frac_ideal_type(::AlgAssAbsOrd{S, T}) where {S, T} = AlgAssAbsOrdFracIdl{S, T}

frac_ideal_type(::Type{AlgAssAbsOrd{S, T}}) where {S, T} = AlgAssAbsOrdFracIdl{S, T}

@doc Markdown.doc"""
    algebra(O::AlgAssAbsOrd) -> AbsAlgAss

> Returns the algebra which contains $O$.
"""
algebra(O::AlgAssAbsOrd) = O.algebra

_algebra(O::AlgAssAbsOrd) = algebra(O)

base_ring(O::AlgAssAbsOrd) = FlintZZ

@doc Markdown.doc"""
    iscommutative(O::AlgAssAbsOrd) -> Bool

> Returns `true` if $O$ is a commutative ring and `false` otherwise.
"""
iscommutative(O::AlgAssAbsOrd) = iscommutative(algebra(O))

ismaximal_known(O::AlgAssAbsOrd) = O.ismaximal != 0

@doc Markdown.doc"""
    ismaximal(O::AlgAssAbsOrd) -> Bool

> Returns `true` if $O$ is a maximal order and `false` otherwise.
"""
function ismaximal(O::AlgAssAbsOrd)
  if O.ismaximal == 1
    return true
  end
  if O.ismaximal == 2
    return false
  end

  A = algebra(O)
  d = discriminant(O)
  if isdefined(A, :maximal_order)
    if d == discriminant(maximal_order(A))
      O.ismaximal = 1
      return true
    else
      O.ismaximal = 2
      return false
    end
  end

  if typeof(A) <: AlgGrp
    fac = factor(degree(O))
  else
    fac = factor(abs(d))
  end

  for (p, j) in fac
    if j == 1
      continue
    end
    d2 = discriminant(pmaximal_overorder(O, Int(p)))
    if d != d2
      O.ismaximal = 2
      return false
    end
  end
  O.ismaximal = 1
  return true
end

################################################################################
#
#  Construction
#
################################################################################

@doc Markdown.doc"""
    Order(A::AbsAlgAss{fmpq}, B::Vector{<: AbsAlgAssElem{fmpq}}) -> AlgAssAbsOrd

> Returns the order of $A$ with basis $B$.
"""
function Order(A::S, B::Vector{T}; check::Bool = false, isbasis = true) where {S <: AbsAlgAss{fmpq}, T <: AbsAlgAssElem{fmpq}}
  check == true || isbasis == false && error("Not implemented yet")
  return AlgAssAbsOrd{S, T}(A, B)
end

@doc Markdown.doc"""
    Order(A::AbsAlgAss{fmpq}, M::FakeFmpqMat) -> AlgAssAbsOrd

> Returns the order of $A$ with basis matrix $M$.
"""
function Order(A::S, M::FakeFmpqMat; check::Bool = false, cached::Bool = false) where {S <: AbsAlgAss{fmpq}}
  check || cached && error("Not implemented yet")
  return AlgAssAbsOrd{S}(A, deepcopy(M))
end

function _Order(A::S, gens::Vector{T}; check::Bool = true) where {S <: AbsAlgAss, T <: AbsAlgAssElem}
  B_A = basis(A)

  if one(A) in gens
    cur = gens
  else
    cur = append!([one(A)], gens)
  end
  Bmat = basis_mat(cur)
  while true
    k = length(cur)
    prods = Vector{elem_type(A)}(undef, k^2)
    for i = 1:k
      ik = (i - 1)*k
      for j = 1:k
        prods[ik + j] = cur[i]*cur[j]
      end
    end
    Ml = hnf(basis_mat(prods))
    r = findfirst(i -> !iszero_row(Ml.num, i), 1:k^2)
    nBmat = sub(Ml, r:nrows(Ml), 1:ncols(Ml))
    if nrows(nBmat) == nrows(Bmat) && Bmat == nBmat
      break
    end
    Bmat = nBmat
  end
  if nrows(Bmat) != dim(A)
    error("Elements do not generate an order")
  end

  return Order(A, Bmat)
end

################################################################################
#
#  Index
#
################################################################################

function index(O::AlgAssAbsOrd)
  B = basis_mat_inv(O, copy = false)
  n = det(B)
  @assert isinteger(n)
  return FlintZZ(n)
end

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function _assure_has_basis(O::AlgAssAbsOrd)
  if !isdefined(O, :basis)
    B = basis(algebra(O))
    M = basis_mat(O, copy = false)
    v = Vector{AlgAssAbsOrdElem}(undef, degree(O))
    for i in 1:degree(O)
      w = sum(M.num[i, j]//M.den * B[j] for j in 1:degree(O))
      v[i] = O(w)
    end
    O.basis = v
  end
  return nothing
end

function assure_basis_mat_inv(O::AlgAssAbsOrd)
  if !isdefined(O, :basis_mat_inv)
    O.basis_mat_inv=inv(basis_mat(O, copy = false))
  end
  return nothing
end

################################################################################
#
#  Basis
#
################################################################################

@doc Markdown.doc"""
    basis(O::AlgAssAbsOrd; copy::Bool = true) -> Vector{AlgAssAbsOrdElem}

> Returns a $\mathbb Z$-basis of $O$.
"""
function basis(O::AlgAssAbsOrd; copy::Bool = true)
  _assure_has_basis(O)
  if copy
    return deepcopy(O.basis)
  else
    return O.basis
  end
end

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

@doc Markdown.doc"""
    basis_mat(O::AlgAssAbsOrd; copy::Bool = true) -> FakeFmpqMat

> Returns the basis matrix of $O$.
"""
function basis_mat(x::AlgAssAbsOrd; copy::Bool = true)
  if copy
    return deepcopy(x.basis_mat)
  else
    return x.basis_mat
  end
end

@doc Markdown.doc"""
    basis_mat_inv(O::AlgAssAbsOrd; copy::Bool = true) -> FakeFmpqMat

> Returns the inverse of the basis matrix of $O$.
"""
function basis_mat_inv(O::AlgAssAbsOrd; copy::Bool = true)
  assure_basis_mat_inv(O)
  if copy
    return deepcopy(O.basis_mat_inv)
  else
    return O.basis_mat_inv
  end
end

################################################################################
#
#  Degree
#
################################################################################

@doc Markdown.doc"""
    degree(O::AlgAssAbsOrd) -> Int

> Returns the dimension of the algebra containing $O$.
"""
function degree(O::AlgAssAbsOrd)
  return dim(algebra(O))
end

################################################################################
#
#  Inclusion of algebra elements
#
################################################################################

function _check_elem_in_order(a::T, O::AlgAssAbsOrd{S, T}, short::Type{Val{U}} = Val{false}) where {S, T, U}
  t = zero_matrix(FlintQQ, 1, degree(O))
  elem_to_mat_row!(t, 1, a)
  t = FakeFmpqMat(t)
  t = t*basis_mat_inv(O, copy = false)
  if short == Val{true}
    return isone(t.den)
  elseif short == Val{false}
    if !isone(t.den)
      return false, Vector{fmpz}()
    else
      v = Vector{fmpz}(undef, degree(O))
      for i = 1:degree(O)
        v[i] = deepcopy(t.num[1, i])
      end
      return true, v
    end
  end
end

@doc Markdown.doc"""
    in(x::AbsAlgAssElem, O::AlgAssAbsOrd) -> Bool

> Returns `true` if the algebra element $x$ is in $O$ and `false` otherwise.
"""
function in(x::T, O::AlgAssAbsOrd{S, T}) where {S, T}
  return _check_elem_in_order(x, O, Val{true})
end

################################################################################
#
#  Denominator in an order
#
################################################################################

@doc Markdown.doc"""
    denominator(a::AbsAlgAssElem, O::AlgAssAbsOrd) -> fmpz

> Returns $d\in \mathbb Z$ such that $d \cdot a \in O$.
"""
function denominator(a::AbsAlgAssElem, O::AlgAssAbsOrd)
  t = zero_matrix(FlintQQ, 1, degree(O))
  elem_to_mat_row!(t, 1, a)
  t = FakeFmpqMat(t)
  t = mul!(t, t, basis_mat_inv(O, copy = false))
  return t.den
end

################################################################################
#
#  Random elements
#
################################################################################

@doc Markdown.doc"""
    rand(O::AlgAssAbsOrd, R::UnitRange) -> AlgAssAbsOrdElem

> Returns a random element of $O$ whose coefficients lie in $R$.
"""
function rand(O::AlgAssAbsOrd, R::UnitRange{T}) where T <: Integer
  return O(map(fmpz, rand(R, degree(O))))
end

@doc Markdown.doc"""
    rand(O::AlgAssAbsOrd, n::Uniot{Integer, fmpz}) -> AlgAssAbsOrdElem

> Returns a random element of $O$ whose coefficients are bounded by $n$.
"""
function rand(O::AlgAssAbsOrd, n::Integer)
  return rand(O, -n:n)
end

function rand(O::AlgAssAbsOrd, n::fmpz)
  return rand(O, -BigInt(n):BigInt(n))
end

################################################################################
#
#  Basis matrices from generators
#
################################################################################

function basis_mat(A::Array{S, 1}) where {S <: AbsAlgAssElem}
  @assert length(A) > 0
  n = length(A)
  d = dim(parent(A[1]))

  M = zero_matrix(FlintZZ, n, d)

  dens = [lcm([denominator(coeffs(A[i], copy = false)[j]) for j=1:d]) for i=1:n]
  deno = lcm(dens)

  for i in 1:n
    for j in 1:d
      temp_den = divexact(deno, denominator(coeffs(A[i], copy = false)[j]))
      M[i, j] = numerator(coeffs(A[i], copy = false)[j]) * temp_den
    end
  end
  return FakeFmpqMat(M, deno)
end

function basis_mat(A::Array{AlgAssAbsOrdElem{S, T}, 1}) where S where T
  @assert length(A) > 0
  n = length(A)
  d = degree(parent(A[1]))
  M = zero_matrix(FlintZZ, n, d)

  for i in 1:n
    el = coordinates(A[i])
    for j in 1:d
      M[i, j] = el[j]
    end
  end
  return M
end

function order_gen(O::AlgAssAbsOrd)
  M = basis_mat(O, copy = false)
  for x in O.basis_alg
    for y in O.basis_alg
      if !(x*y in O)
        a=FakeFmpqMat(coeffs(x*y, copy = false))
        N=vcat(M,a)
        return AlgAssAbsOrd(algebra(O), hnf(N))
      end
    end
  end
end

################################################################################
#
#  Sum of orders
#
################################################################################

# Be careful!
# To be used only in the case of the construction of a maximal order!
function +(a::AlgAssAbsOrd, b::AlgAssAbsOrd)
  aB = basis_mat(a, copy = false)
  bB = basis_mat(b, copy = false)
  d = degree(a)
  c = sub(_hnf(vcat(bB.den*aB.num, aB.den*bB.num), :lowerleft), d + 1:2*d, 1:d)
  return Order(algebra(a), FakeFmpqMat(c, aB.den*bB.den))
end

################################################################################
#
#  Print
#
################################################################################

function show(io::IO, O::AlgAssAbsOrd)
  compact = get(io, :compact, false)
  if compact
    print(io, "Order of ")
    show(IOContext(io, :compact => true), algebra(O))
  else
    print(io, "Order of ")
    print(io, algebra(O))
    println(io, " with basis matrix ")
    print(io, basis_mat(O))
  end
end

################################################################################
#
#  Equality
#
################################################################################

@doc Markdown.doc"""
    ==(S::AlgAssAbsOrd, T::AlgAssAbsOrd) -> Bool

> Returns `true` if $S$ and $T$ are equal and `false` otherwise.
"""
function ==(S::AlgAssAbsOrd, T::AlgAssAbsOrd)
  return basis_mat(S, copy = false) == basis_mat(T, copy = false)
end

################################################################################
#
#  Some tests
#
################################################################################

function check_ideal(I::AlgAssAbsOrdIdl)
  
  O = order(I)
  B = basis(O)
  B1 = basis(I)
  for i = 1:length(B)
    for j = 1:length(B1)
      if !(B[i]*B1[j] in I)
        @show coordinates(B[i]*B1[j])
        error("Ideal not closed under multiplication")
      end 
      if !(B1[j]*B[i] in I)
        @show coordinates(B1[j]*B[i])
        error("Ideal not closed under multiplication")
      end 
    end 
  end
  return true
end

function defines_order(A::AlgAss{fmpq}, v::Array{AlgAssElem{fmpq, AlgAss{fmpq}}, 1})
  d = dim(A)
  M = zero_matrix(FlintQQ, d, d)
  for i in 1:d
    c = coeffs(v[i], copy = false)
    for j in 1:d
      M[i, j] = c[j]
    end
  end
  O = Order(A, FakeFmpqMat(M))
  b = _check_order(O)
  return b, FakeFmpqMat(M)
end

function _check_order(O::AlgAssAbsOrd)
  for x in O.basis_alg
    #@assert denominator(minpoly(x))==1
    for y in O.basis_alg
      if !(x*y in O)
        return false
      end
    end
  end
  if !(one(algebra(O)) in O) return
    false
  end
  return true
end

function check_order(O::AlgAssAbsOrd)
  b = _check_order(O)
  if !b 
    error("Not an order")
  else
    return true
  end
end

function check_pradical(I::AlgAssAbsOrdIdl, p::Int)
  
  O= order(I)
  for i=1:degree(O)
    x=elem_from_mat_row(O,basis_mat(I, copy = false), i)
    for j=1:degree(O)
      @assert divisible(numerator(tr(elem_in_algebra(x; copy = false)*O.basis_alg[j])), p)
    end
  end
  #=
  if p==2
    for i=1:O.dim
      x=elem_from_mat_row(O,I.basis_mat, i)
      for j=1:O.dim
        for k=1:clog(fmpz(O.dim), p)
          @assert divisible(numerator(tr((x.elem_in_algebra*O.basis_alg[j])^(p^k))), p^(k+1))
        end
      end
    end
  end
  =#
  return true
end

################################################################################
#
#  Discriminant and Reduced Trace Matrix
#
################################################################################

@doc Markdown.doc"""
    trred_matrix(O::AlgssAbsOrd) -> fmpz_mat

> Returns the reduced trace matrix $M$ of $O$, i. e. `M[i, j] = trred(b[i]*b[j])`,
> where $b$ is a basis of $O$.
"""
function trred_matrix(O::AlgAssAbsOrd)
  if isdefined(O, :trred_matrix)
    return O.trred_matrix
  end
  A=algebra(O)
  x=O.basis_alg
  m=length(x)
  M=zero_matrix(FlintZZ, m, m)
  a=A()
  for i=1:m
    a = mul!(a, x[i], x[i])
    M[i,i] = FlintZZ(trred(a))
  end
  for i = 1:m
    for j = i+1:m
      a = mul!(a, x[i], x[j])
      b = FlintZZ(trred(a))
      M[i,j] = b
      M[j,i] = b
    end
  end
  O.trred_matrix = M
  return M
end

@doc Markdown.doc"""
    discriminant(O::AlgssAbsOrd) -> fmpz

> Returns the discriminant of $O$.
"""
function discriminant(O::AlgAssAbsOrd)
  if isdefined(O, :disc)
    return O.disc
  end
  M = trred_matrix(O)
  O.disc = det(M)
  return O.disc
end

################################################################################
#
#  Schur Index at Infinity
#
################################################################################

#Steel Nebe paper
@doc Markdown.doc"""
    schur_index_at_real_plc(O::AlgAssAbsOrd) -> Int

> Given an order $O$, this function returns the schur index
> of the algebra over the field of real numbers.
"""
function schur_index_at_real_plc(O::AlgAssAbsOrd)

  x=trace_signature(O)
  n=root(degree(O),2)
  if x[1] == divexact(n*(n+1),2)
    return 1
  else
    return 2
  end
end

function trace_signature(O::AlgAssAbsOrd)

  @vtime :AlgAssOrd 1 M = trred_matrix(O)
  Zx, x = PolynomialRing(FlintZZ, "x", cached = false)
  Qy, y = PolynomialRing(FlintQQ, "y", cached = false)
  @vtime :AlgAssOrd 1 f = charpoly(Zx, M)
  @vtime :AlgAssOrd 1 fac = factor_squarefree(Qy(f))
  npos = 0
  for (t,e) in fac
    @vtime :AlgAssOrd a = number_positive_roots(Zx(t))
    npos += a*e 
  end
  return (npos, degree(f) - npos)
end

################################################################################
#
#  Schur Index at p
#
################################################################################

@doc Markdown.doc"""
    schur_index_at_p(O::AlgAssAbsOrd, p::fmpz)

> Given a maximal order $O$ and a prime $p$, this function returns the schur index
> of the completion of the algebra at $p$.
"""
function schur_index_at_p(O::AlgAssAbsOrd, p::fmpz)
  @assert O.ismaximal==1
  d = discriminant(O)
  v = valuation(d,p)
  if v == 0
    return 1
  end
  n = root(degree(O),2)
  t = n - divexact(v,n)
  return divexact(n,t)
end

################################################################################
#
#  p-maximal overorder
#
################################################################################

function pmaximal_overorder(O::AlgAssAbsOrd, p::Union{fmpz, Int})
  d = discriminant(O)
  if rem(d, p^2) != 0
    return O
  end

  if p > degree(O)
    @vtime :AlgAssOrd 1 O1 = pmaximal_overorder_tr(O,p)::AlgAssAbsOrd
    return O1
  else
    @vtime :AlgAssOrd 1 O1 = pmaximal_overorder_meataxe(O,p)::AlgAssAbsOrd
    return O1
  end
end

function pmaximal_overorder_meataxe(O::AlgAssAbsOrd, p::Union{fmpz, Int})

  extend = false
  d = discriminant(O)
  while true
    dd = fmpz(1)
    @vtime :AlgAssOrd 1 max_id =_maximal_ideals(O, p*O, p, strict_containment = true)
    for m in max_id
      @vtime :AlgAssOrd 1 OO = ring_of_multipliers(m, fmpz(p))
      dd = discriminant(OO)
      if d != dd
        extend = true
        O = OO
        d = dd
        break
      end
    end

    if extend
      if rem(d, p^2) != 0
        break
      end
      extend = false
      continue
    else
      break
    end

  end
  return O
end

function pmaximal_overorder_tr(O::AlgAssAbsOrd, p::Int)
  #First, the head order by computing the pradical and its ring of multipliers
  d = discriminant(O)
  @vtime :AlgAssOrd 1 I = pradical(O, p)
  @vtime :AlgAssOrd 1 OO = ring_of_multipliers(I, fmpz(p))
  dd = discriminant(OO)
  if rem(dd, p^2) != 0
    return OO
  end
  while dd!= d
    d = dd
    O = OO
    @vtime :AlgAssOrd 1 I = pradical(O,p)
    @vtime :AlgAssOrd 1 OO = ring_of_multipliers(I, fmpz(p))
    dd = discriminant(OO)
    if rem(dd, p^2) != 0
      return OO
    end
  end
  #Now, we have to check the maximal ideals.

  extend = false
  @vtime :AlgAssOrd 1 max_id = _maximal_ideals(O, I, p, strict_containment = true)
  for m in max_id
    @vtime :AlgAssOrd 1 OO = ring_of_multipliers(m, fmpz(p))
    dd = discriminant(OO)
    if d != dd
      extend = true
      O = OO
      d = dd
      break
    end
  end
  if extend
    if rem(dd, p^2) != 0
      return OO
    end
    extend = false
  else
    return OO
  end
  while true
    dd = fmpz(1)
    @vtime :AlgAssOrd 1 max_id = _maximal_ideals(O, p*O, p, strict_containment = true)
    for m in max_id
      OO = ring_of_multipliers(m, fmpz(p))
      dd = discriminant(OO)
      if d != dd
        extend = true
        O = OO
        d = dd
        break
      end
    end

    if extend
      if rem(dd, p^2) != 0
        break
      end
      extend = false
      continue
    else
      break
    end

  end
  return O
end

################################################################################
#
#  Maximal Order
#
################################################################################

@doc Markdown.doc"""
    MaximalOrder(O::AlgAssAbsOrd)

> Given an order $O$, this function returns a maximal order containing $O$.
"""
function MaximalOrder(O::AlgAssAbsOrd)
  A = algebra(O)

  d = discriminant(O)
  @vtime :NfOrd fac = factor(abs(d))

  OO = O
  for (p, j) in fac
    if mod(d, p^2) != 0
      continue
    end
    OO += pmaximal_overorder(O, Int(p))
  end
  OO.ismaximal = 1
  return OO
end

function MaximalOrder(O::AlgAssAbsOrd{S, T}) where { S <: AlgGrp, T <: AlgGrpElem }
  A = algebra(O)

  d = discriminant(O)
  fac = factor(degree(O)) # the order of the group

  OO = O
  for (p, j) in fac
    if mod(d, p^2) != 0
      continue
    end
    OO += pmaximal_overorder(O, Int(p))
  end
  OO.ismaximal = 1
  return OO
end

function _denominator_of_mult_table(A::AbsAlgAss{fmpq})
  l = denominator(multiplication_table(A, copy = false)[1, 1, 1])
  for i = 1:dim(A)
    for j = 1:dim(A)
      for k = 1:dim(A)
        l = lcm(l, denominator(multiplication_table(A, copy = false)[i, j, k]))
      end
    end
  end
  return l
end

_denominator_of_mult_table(A::AlgGrp{fmpq}) = fmpz(1)

@doc Markdown.doc"""
    any_order(A::AbsAlgAss{fmpq}) -> AlgAssAbsOrd

> Returns any order of $A$.
"""
function any_order(A::AbsAlgAss{fmpq})
  d = _denominator_of_mult_table(A)

  M = vcat(zero_matrix(FlintQQ, 1, dim(A)), d*identity_matrix(FlintQQ, dim(A)))
  oneA = one(A)
  for i = 1:dim(A)
    M[1, i] = deepcopy(coeffs(oneA, copy = false)[i])
  end
  M = FakeFmpqMat(M)
  M = hnf!(M, :lowerleft)
  O = Order(A, sub(M, 2:dim(A) + 1, 1:dim(A)))
  return O
end

@doc Markdown.doc"""
    MaximalOrder(A::AbsAlgAss{fmpq}) -> AlgAssAbsOrd

> Returns a maximal order of $A$.
"""
function MaximalOrder(A::AbsAlgAss)
  if isdefined(A, :maximal_order)
    return A.maximal_order
  end

  O = any_order(A)
  OO = MaximalOrder(O)
  A.maximal_order = OO
  return OO
end

function maximal_order_via_decomposition(A::AbsAlgAss{fmpq})
  if isdefined(A, :maximal_order)
    return A.maximal_order
  end
  fields_and_maps = as_number_fields(A)
  M = zero_matrix(FlintQQ, dim(A), dim(A))
  row = 1
  for i = 1:length(fields_and_maps)
    K = fields_and_maps[i][1]
    AtoK = fields_and_maps[i][2]
    O = maximal_order(K)
    for b in basis(O)
      a = AtoK\K(b)
      elem_to_mat_row!(M, row, a)
      row += 1
    end
  end
  FakeM = FakeFmpqMat(M)
  FakeM = hnf!(FakeM, :lowerleft)
  OO = Order(A, FakeM)
  OO.ismaximal = 1
  A.maximal_order = OO
  return OO
end

# Requires that O is maximal and A = QQ^(n\times n).
# Computes a maximal order of type
#  (O ... O a^(-1))
#  (:     :   :   )
#  (O ... O a^(-1))
#  (a ... a   O   )
# for an ideal a of O.
# See Bley, Johnston "Computing generators of free modules over orders in group
# algebras", Prop. 5.1.
function _simple_maximal_order(O::AlgAssAbsOrd{S1, S2}, with_trafo::Type{Val{T}} = Val{false}) where { S1 <: AlgMat, S2, T }
  A = algebra(O)
  n = degree(A)

  # Build a matrix with the first rows of basis elements of O
  M = zero_matrix(FlintQQ, dim(A), n)
  for i = 1:dim(A)
    for j = 1:n
      M[i, j] = deepcopy(matrix(elem_in_algebra(basis(O, copy = false)[i], copy = false), copy = false)[1, j])
    end
  end
  M = FakeFmpqMat(M)
  M = hnf!(M, :upperright)
  M = fmpq_mat(sub(M, 1:n, 1:n))

  # Compute M^(-1)*O*M
  iM = inv(M)
  bb = Vector{elem_type(A)}()
  for i = 1:degree(O)
    push!(bb, iM*elem_in_algebra(basis(O, copy = false)[i], copy = false)*M)
  end

  if with_trafo == Val{true}
    return Order(A, bb), A(M)
  else
    return Order(A, bb)
  end
end

################################################################################
#
#  Conductor
#
################################################################################

@doc Markdown.doc"""
    conductor(R::AlgAssAbsOrd, S::AlgAssAbsOrd, action::Symbol) -> AlgAssAbsOrdIdl

> Returns the ideal $\{ x \in R \mid xS \subseteq R \}$ if `action == :right` and
> $\{ x \in R \mid Sx \subseteq R \}$ if `action == :left`.
> It is assumed that $R \subseteq S$.
"""
function conductor(R::AlgAssAbsOrd, S::AlgAssAbsOrd, action::Symbol)
  n = degree(R)
  t = basis_mat(R, copy = false)*basis_mat_inv(S, copy = false)
  @assert isone(t.den)
  basis_mat_R_in_S_inv_num, d = pseudo_inv(t.num)
  M = zero_matrix(FlintZZ, n^2, n)
  B = basis(S, copy = false)
  for k in 1:n
    a = B[k]
    N = representation_matrix(a, action)*basis_mat_R_in_S_inv_num
    for i in 1:n
      for j in 1:n
        M[(k - 1)*n + i, j] = N[j, i]
      end
    end
  end
  H = sub(hnf(M), 1:n, 1:n)
  Hinv, new_den = pseudo_inv(transpose(H))
  Hinv = Hinv*basis_mat_R_in_S_inv_num
  if action == :left
    return ideal(R, divexact(Hinv, new_den), :right)
  else
    return ideal(R, divexact(Hinv, new_den), :left)
  end
end

################################################################################
#
#  Units of quotients
#
################################################################################

# Computes a generating system of U in O, where U is a set of representatives of
# the image of the projection map \pi:O^\times -> (O/g*O)^\times.
# Assumes that O is a maximal order in Mat_{n\times n}(QQ).
# See Bley, Johnson: "Computing generators of free modules over orders in
# group algebras", section 6.
function enum_units(O::AlgAssAbsOrd{S, T}, g::fmpz) where { S <: AlgMat, T }
  A = algebra(O)
  @assert degree(A)^2 == dim(A)

  n = degree(A)

  L = _simple_maximal_order(O)
  a = basis_mat(L, copy = false)[dim(A) - 1, dim(A) - 1]
  ai = basis_mat(L, copy = false)[n, n]

  result = Vector{elem_type(L)}()
  n1 = n - 1
  # n \nmid i, j or n \mid i, j
  for i = 1:n1
    for j = 1:n1
      if j == i
        continue
      end
      E = identity_matrix(FlintQQ, n)
      E[i, j] = deepcopy(g)
      push!(result, L(A(E)))
    end
  end

  # n \nmid i and n \mid j
  for i = 1:n1
    E = identity_matrix(FlintQQ, n)
    E[i, n] = deepcopy(a)
    push!(result, L(A(E)))
  end

  # n \mid i and n \nmid j
  for j = 1:n1
    E = identity_matrix(FlintQQ, n)
    E[n, j] = deepcopy(ai)
    push!(result, L(A(E)))
  end

  E = identity_matrix(FlintQQ, n)
  E[1, 1] = fmpz(-1)
  push!(result, L(A(E)))
  return result
end
