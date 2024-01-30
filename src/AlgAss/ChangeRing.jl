################################################################################
#
#  Change of ring
#
################################################################################

@doc raw"""
    restrict_scalars(A::StructureConstantAlgebra{AbsSimpleNumFieldElem}, Q::QQField)
    restrict_scalars(A::StructureConstantAlgebra{fqPolyRepFieldElem}, Fp::fpField)
    restrict_scalars(A::StructureConstantAlgebra{FqPolyRepFieldElem}, Fp::EuclideanRingResidueField{ZZRingElem})
      -> StructureConstantAlgebra, Map

Given an algebra $A$ over a field $L$ and the prime field $K$ of $L$, this
function returns the restriction $B$ of $A$ to $K$ and the morphism $B \to A$.
"""
# Top level functions to avoid "type mix-ups" (like StructureConstantAlgebra{fqPolyRepFieldElem} with FlintQQ)
function restrict_scalars(A::AbstractAssociativeAlgebra{AbsSimpleNumFieldElem}, Q::QQField)
  return _restrict_scalars(A, Q)
end

function restrict_scalars(A::AbstractAssociativeAlgebra{fqPolyRepFieldElem}, Fp::fpField)
  return _restrict_scalars(A, Fp)
end

function restrict_scalars(A::AbstractAssociativeAlgebra{FqPolyRepFieldElem}, Fp::FpField)
  return _restrict_scalars(A, Fp)
end

function restrict_scalars(A::AbstractAssociativeAlgebra{FqFieldElem}, Fp::FqField)
  return _restrict_scalars(A, Fp)
end

#function restrict_scalars(A::AbstractAssociativeAlgebra{fpFieldElem}, Fp::fpField)
#  function AtoA(x::AssociativeAlgebraElem)
#    return x
#  end
#  return A, AtoA, AtoA
#end

@doc raw"""
    restrict_scalars(A::StructureConstantAlgebra{AbsSimpleNumFieldElem}, KtoL::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField})
      -> StructureConstantAlgebra, Map

Given an algebra $A$ over a number field $L$ and an inclusion map `KtoL` from
a number field $K$ to $L$, this function returns the restriction $B$ of $A$
to $K$ and the morphism $B \to A$.
"""
function restrict_scalars(A::AbstractAssociativeAlgebra{AbsSimpleNumFieldElem}, KtoL::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField})
  return _restrict_scalars(A, KtoL)
end

#function restrict_scalars(A::AbstractAssociativeAlgebra{Nemo.FpFieldElem}, Fp::Nemo.FpField)
#  function AtoA(x::AssociativeAlgebraElem)
#    return x
#  end
#  return A, AtoA, AtoA
#end

mutable struct AlgAssResMor{S, T, U, V} <: Map{S, T, HeckeMap, AlgAssResMor}
  header::MapHeader{S, T}
  domain::S
  codomain::T
  f::U
  B::V

  function AlgAssResMor(B::S, A::T, f::U, Bas::V) where {S, T, U, V}
    z = new{S, T, U, V}()
    z.domain = B
    z.codomain = A
    z.B = Bas
    z.f = f
    z.header = MapHeader(B, A)
    return z
  end
end

domain(f::AlgAssResMor) = f.domain

codomain(f::AlgAssResMor) = f.codomain

function preimage(f::AlgAssResMor, a)
  @assert parent(a) == codomain(f)
  B = domain(f)
  A = codomain(f)
  m = div(dim(B), dim(A))
  y = coefficients(a, copy = false)
  yy = Vector{elem_type(base_ring(B))}(undef, dim(B))
  for i in 1:length(y)
    ee = image(f.f, y[i])
    for j in 1:length(ee)
      yy[(i - 1)*m + j] = ee[j]
    end
  end
  return domain(f)(yy)
end

function image(f::AlgAssResMor, a)
  @assert parent(a) == domain(f)
  A = codomain(f)
  B = domain(f)
  d = div(dim(B), dim(A))
  y = coefficients(a, copy = false)
  yy = Vector{elem_type(base_ring(A))}(undef, dim(A))
  for i in 1:dim(A)
    yy[i] = preimage(f.f, y[(i - 1)*d + 1:i*d])
  end
  return A(yy)
end

#function _restrict_scalars_to_prime_field(A::StructureConstantAlgebra{T}, prime_field::Union{QQField, fpField, EuclideanRingResidueField{ZZRingElem}}) where { T <: Union{AbsSimpleNumFieldElem, fqPolyRepFieldElem, FqPolyRepFieldElem} }
# TODO: fix the type
function _restrict_scalars(A::AbstractAssociativeAlgebra{T}, prime_field) where { T }
  K = base_ring(A)
  n = dim(A)
  # We use b * A[i], b running through a basis of A over prime_field
  # the basis for A over the prime field.
  # Precompute the powers a^k:

  f = FldToVecMor(K, prime_field)
  Bas = f.B
  F = f.K

  m = div(degree(K), degree(F))
  nm = n*m

  absbasis = elem_type(A)[]
  BA = basis(A)
  for i in 1:n
    for j in 1:length(Bas)
      push!(absbasis, Bas[j] * BA[i])
    end
  end

  m1 = m - 1
  mult_table = zeros(F, nm, nm, nm)

  Aij = A()
  t = A()
  tt = K()
  firstindex = 1
  for i in 1:n
    for i2 in 1:m
      secondindex = 1
      for j in 1:n
        Aij = mul!(Aij, A[i], A[j])
        if iszero(Aij)
          secondindex += m
          continue
        end

        for j2 in 1:m
          e = Bas[i2] * Bas[j2] * Aij
          y = Vector{elem_type(F)}(undef, nm)
          yy = coefficients(e, copy = false)
          for i in 1:n
            ee = image(f, yy[i])
            @assert length(ee) == m
            for j in 1:m
              y[(i - 1)*m + j] = ee[j]
            end
          end
          mult_table[firstindex, secondindex, :] = y
          secondindex += 1
        end
      end
      firstindex += 1
    end
  end

  e = one(A)
  y = Vector{elem_type(F)}(undef, nm)
  yy = coefficients(e, copy = false)
  for i in 1:n
    ee = image(f, yy[i])
    for j in 1:m
      y[(i - 1)*m + j] = ee[j]
    end
  end

  B = StructureConstantAlgebra(F, mult_table, y)
  B.is_commutative = is_commutative(A)

  return B, AlgAssResMor(B, A, f, absbasis)
end

mutable struct AlgAssExtMor{S, T, U, V, W, X, Y} <: Map{S, T, HeckeMap, AlgAssExtMor}
  header::MapHeader{S, T}
  domain::S
  codomain::T
  f::U
  B::V
  BB::W
  MMinv::X
  BAoverC::Y

  function AlgAssExtMor(B::S, A::T, f::U, BC::V, BL::W, MMinv::X, BAoverC::Y) where {S, T, U, V, W, X, Y}
    z = new{S, T, U, V, W, X, Y}()
    z.domain = B
    z.codomain = A
    z.f = f
    z.B = BC
    z.BB = BL
    z.BAoverC = BAoverC
    z.MMinv = MMinv
    z.header = MapHeader(B, A)
    return z
  end
end

domain(f::AlgAssExtMor) = f.domain

codomain(f::AlgAssExtMor) = f.codomain

function image(f::AlgAssExtMor, a)
  @assert parent(a) == domain(f)
  B = domain(f)
  A = codomain(f)
  m = div(dim(A), dim(B))
  y = coefficients(a, copy = false)
  z = zero(A)
  for i in 1:length(y)
    z = z + dot(f.B, (f.f\y[i]).coeffs) * f.BAoverC[i]
  end
  return z
end

function preimage(f::AlgAssExtMor, a)
  @assert parent(a) == codomain(f)
  A = codomain(f)
  B = domain(f)
  d = div(dim(A), dim(B))
  _y = matrix(base_ring(A), 1, dim(A), coefficients(a, copy = false)) * f.MMinv
  y = elem_type(base_ring(A))[_y[1, i] for i in 1:dim(A)]
  yy = Vector{elem_type(base_ring(B))}(undef, dim(B))
  for i in 1:dim(B)
    yy[i] = f.f(dot(basis(domain(f.f)), y[(i - 1)*d + 1:i*d]))
  end
  return B(yy)
end

function _as_algebra_over_center(A::StructureConstantAlgebra{T}) where { T <: Union{AbsSimpleNumFieldElem, QQFieldElem}}
  extpT = _ext_type(T)
  extT = elem_type(extpT)
  eltA = elem_type(A)
  matT = dense_matrix_type(T)
  algtype = StructureConstantAlgebra{extT}
  mortype = AlgAssExtMor{algtype, StructureConstantAlgebra{T},
                         AbsAlgAssToNfAbsMor{StructureConstantAlgebra{T}, eltA, extpT, matT},
                         Vector{eltA}, Vector{extT}, matT, Vector{eltA}}
  get_attribute!(A, :_as_algebra_over_center) do
    @assert !iszero(A)
    K = base_ring(A)
    C, CtoA = center(A)
    fields = as_number_fields(C)
    @assert length(fields) == 1
    L, CtoL = fields[1]
    # Maybe do something more efficient A is_central
    return __as_algebra_over_center(A, K, L, CtoA, CtoL)
  end::Tuple{algtype, mortype}
end

function _as_algebra_over_center(A::StructureConstantAlgebra{T}) where { T } #<: Union{QQFieldElem, fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem}, FqPolyRepFieldElem, fqPolyRepFieldElem} }
  @assert !iszero(A)

  K = base_ring(A)
  C, CtoA = center(A)


  # Maybe do something more efficient A is_central

  L, CtoL = _as_field_with_isomorphism(C)
  return __as_algebra_over_center(A, K, L, CtoA, CtoL)
end

function __as_algebra_over_center(A, K, L, CtoA, CtoL)
  C = domain(CtoA)

  is_central = ( dim(C) == 1 )

  basisC = basis(C)
  basisCinA = Vector{elem_type(A)}(undef, dim(C))
  basisCinL = Vector{elem_type(L)}(undef, dim(C))
  for i = 1:dim(C)
    basisCinA[i] = CtoA(basisC[i])
    basisCinL[i] = CtoL(basisC[i])
  end

  # We construct a basis of A over C (respectively L) by using the following fact:
  # A subset M of basis(A) is a C-basis of A if and only if |M| = dim(A)/dim(C)
  # and all possible products of elements of M and basisCinA form a K-basis of A,
  # with K := base_ring(A).
  AoverK = basis(A)
  AoverC = Vector{Int}()
  M = zero_matrix(K, dim(C), dim(A))
  MM = zero_matrix(K, 0, dim(A))
  r = 0
  for i = 1:dim(A)
    b = AoverK[i]

    for j = 1:dim(C)
      elem_to_mat_row!(M, j, b*basisCinA[j])
    end

    N = vcat(MM, M)
    s = rank(N)
    if s > r
      push!(AoverC, i)
      MM = N
      r = s
    end
    if r == dim(A)
      break
    end
  end

  m = div(dim(A), dim(C))

  @assert length(AoverC) == m
  @assert nrows(MM) == dim(A)

  iMM = inv(MM)

  dC = dim(C)

  @assert dC * m == dim(A)

  mult_table = zeros(L, m, m, m)
  Aij = A()
  for i = 1:m
    for j = 1:m
      Aij = mul!(Aij, A[AoverC[i]], A[AoverC[j]])
      if iszero(Aij)
        continue
      end

      xx = matrix(K, 1, dim(A), coefficients(Aij, copy = false))
      xxM = xx * iMM

      y = Vector{elem_type(L)}(undef, m)

      for k in 1:m
        # This linear indexing is fine, since it is a row/vector
        y[k] = CtoL(dot(basis(domain(CtoL)), elem_type(K)[xxM[(k - 1) * dC + l] for l in 1:dC]))
      end

      mult_table[i, j, :] = y
    end
  end

  xx = matrix(K, 1, dim(A), coefficients(one(A), copy = false))
  xxM = xx * iMM

  y = Vector{elem_type(L)}(undef, m)

  for k in 1:m
    # This linear indexing is fine, since it is a row/vector
    y[k] = CtoL(dot(basis(domain(CtoL)), elem_type(K)[xxM[(k - 1) * dC + l] for l in 1:dC]))
  end


  B = StructureConstantAlgebra(L, mult_table, y)
  B.is_commutative = A.is_commutative

  BtoA = AlgAssExtMor(B, A, CtoL, basisCinA, basisCinL, iMM, elem_type(A)[A[i] for i in AoverC])

  return B, BtoA
end

mutable struct PrimeFieldEmbedStub{S, T}
  domain::S
  codomain::T
end

function FldToVecMor(f::PrimeFieldEmbedStub)
  L = codomain(f)
  K = domain(f)
  return FldToVecMor(L, K)
end

function _embed_center_into_field(m::AbsAlgAssToNfAbsMor{StructureConstantAlgebra{QQFieldElem}})
  return PrimeFieldEmbedStub(base_ring(domain(m)), codomain(m))
end

function _embed_center_into_field(m::AbsAlgAssToNfAbsMor{StructureConstantAlgebra{AbsSimpleNumFieldElem}})
  return PrimeFieldEmbedStub(base_ring(domain(m)), codomain(m))
end

function _embed_center_into_field(m::AbsAlgAssToFqMor{StructureConstantAlgebra{fpFieldElem}})
  return PrimeFieldEmbedStub(base_ring(domain(m)), codomain(m))
end

function _embed_center_into_field(m::AbsAlgAssToFqMor{StructureConstantAlgebra{FpFieldElem}})
  return PrimeFieldEmbedStub(base_ring(domain(m)), codomain(m))
end

domain(f::PrimeFieldEmbedStub) = f.domain

codomain(f::PrimeFieldEmbedStub) = f.codomain


