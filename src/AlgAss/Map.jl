mutable struct AbsAlgAssMor{R, S, T} <: Map{R, S, HeckeMap, AbsAlgAssMor}
  header::MapHeader{R, S}

  mat::T
  imat::T
  c_t::T
  d_t::T
  c_t_threaded::Vector{T}
  d_t_threaded::Vector{T}

  function AbsAlgAssMor{R, S, T}(A::R, B::S) where {R, S, T}
    z = new{R, S, T}()
    z.header = MapHeader(A, B)
    return z
  end

  function AbsAlgAssMor{R, S, T}(A::R, B::S, M::T) where {R, S, T}
    z = new{R, S, T}()
    z.c_t = similar(M, 1, dim(A))
    z.d_t = similar(M, 1, dim(B))
    z.c_t_threaded = [similar(M, 1, dim(A)) for i in 1:Threads.nthreads()]
    z.d_t_threaded = [similar(M, 1, dim(B)) for i in 1:Threads.nthreads()]
    z.mat = M

    function image(a)
      if Threads.nthreads() == 1
        zt = z.c_t
      else
        zt = z.c_t_threaded[Threads.threadid()]
      end
      for i in 1:dim(A)
        zt[1, i] = coefficients(a, copy = false)[i]
      end
      s = Vector{elem_type(base_ring(B))}(undef, dim(B))
      #mul!(z.d_t, z.c_t, M) # there is no mul! for Generic.Mat
      z.d_t = zt*M
      for i in 1:dim(B)
        s[i] = z.d_t[1, i]
      end
      return B(s)
    end

    z.header = MapHeader(A, B, image)
    return z
  end

  function AbsAlgAssMor{R, S, T}(A::R, B::S, M::T, N::T) where {R, S, T}
    z = new{R, S, T}()
    z.c_t = similar(M, 1, dim(A))
    z.d_t = similar(M, 1, dim(B))
    z.c_t_threaded = [similar(M, 1, dim(A)) for i in 1:Threads.nthreads()]
    z.d_t_threaded = [similar(M, 1, dim(B)) for i in 1:Threads.nthreads()]
    z.mat = M
    z.imat = N

    function image(a)
      if Threads.nthreads() == 1
        zct = z.c_t
        zdt = z.d_t
      else
        zct = z.c_t_threaded[Threads.threadid()]
        zdt = z.d_t_threaded[Threads.threadid()]
      end

      ca = coefficients(a, copy = false)
      __set!(zct, ca)
      #for i in 1:dim(A)
      #  z.c_t[1, i] = ca[i]
      #end
      s = Vector{elem_type(base_ring(B))}(undef, dim(B))
      if T === QQMatrix
        mul!(zdt, zct, M) # there is no mul! for Generic.Mat
      else
        zdt = zct * M
      end
      for i in 1:dim(B)
        s[i] = zdt[1, i]
      end

      return B(s, copy = false)
    end

    function preimage(a)
      if Threads.nthreads() == 1
        zct = z.c_t
        zdt = z.d_t
      else
        zct = z.c_t_threaded[Threads.threadid()]
        zdt = z.d_t_threaded[Threads.threadid()]
      end

      for i in 1:dim(B)
        zdt[1, i] = coefficients(a, copy = false)[i]
      end
      s = Vector{elem_type(base_ring(A))}(undef, dim(A))
      zct = zdt * N
      for i in 1:dim(A)
        s[i] = zct[1, i]
      end
      return A(s, copy = false)
    end

    z.header = MapHeader(A, B, image, preimage)
    return z
  end
end

function __set!(c_t, ca)
  for i in 1:length(ca)
    c_t[1, i] = ca[i]
  end
end

function __set!(c_t::QQMatrix, ca)
  GC.@preserve c_t begin
    for i in 1:length(ca)
      t = mat_entry_ptr(c_t, 1, i)
      set!(t, ca[i])
    end
  end
end

#inv(a::AbsAlgAssMor) = pseudo_inv(a)

#mutable struct AlgAssMor{R, S, T} <: Map{StructureConstantAlgebra{R}, StructureConstantAlgebra{S}, HeckeMap, AlgAssMor}
#  header::MapHeader{StructureConstantAlgebra{R}, StructureConstantAlgebra{S}}
#
#  mat::T
#  imat::T
#  c_t::T
#  d_t::T
#
#  function AlgAssMor(A::StructureConstantAlgebra{R}, B::StructureConstantAlgebra{S}, M::T) where {R, S, T}
#    z = new{R, S, T}()
#    z.c_t = similar(M, 1, dim(A))
#    z.d_t = similar(M, 1, dim(B))
#    z.mat = M
#
#    function image(a::AssociativeAlgebraElem)
#      for i in 1:dim(A)
#        z.c_t[1, i] = a.coeffs[i]
#      end
#      s = Vector{S}(undef, dim(B))
#      #mul!(z.d_t, z.c_t, M) # there is no mul! for Generic.Mat
#      z.d_t = z.c_t*M
#      for i in 1:dim(B)
#        s[i] = z.d_t[1, i]
#      end
#
#      return AssociativeAlgebraElem{S}(B, s)
#    end
#
#    z.header = MapHeader(A, B, image)
#    return z
#  end
#
#  function AlgAssMor(A::StructureConstantAlgebra{R}, B::StructureConstantAlgebra{S}, M::T, N::T) where {R, S, T}
#    z = new{R, S, T}()
#    z.c_t = similar(M, 1, dim(A))
#    z.d_t = similar(M, 1, dim(B))
#
#    z.mat = M
#    z.imat = N
#
#    function image(a::AssociativeAlgebraElem)
#      for i in 1:dim(A)
#        z.c_t[1, i] = a.coeffs[i]
#      end
#      s = Vector{S}(undef, dim(B))
#      #mul!(z.d_t, z.c_t, M) # there is no mul! for Generic.Mat
#      z.d_t = z.c_t * M
#      for i in 1:dim(B)
#        s[i] = z.d_t[1, i]
#      end
#
#      return AssociativeAlgebraElem{S}(B, s)
#    end
#
#    function preimage(a::AssociativeAlgebraElem)
#      for i in 1:dim(B)
#        z.d_t[1, i] = a.coeffs[i]
#      end
#      s = Vector{R}(undef, dim(A))
#      z.c_t = z.d_t * N
#      for i in 1:dim(A)
#        s[i] = z.c_t[1, i]
#      end
#      return AssociativeAlgebraElem{R}(A, s)
#    end
#
#    z.header = MapHeader(A, B, image, preimage)
#    return z
#  end
#end

function compose_and_squash(f::AbsAlgAssMor{R, U, T}, g::AbsAlgAssMor{S, R, T}) where {R, T, S, U}
  @assert codomain(g) === domain(f)
  if isdefined(f, :imat) && isdefined(g, :imat)
    return hom(domain(g), codomain(f), g.mat * f.mat, f.imat * g.imat)
  else
    return hom(domain(g), codomain(f), g.mat * f.mat)
  end
end

function hom(A::R, B::S, imgs::Vector; check = true) where {R <: AbstractAssociativeAlgebra, S <: AbstractAssociativeAlgebra}
  @assert length(imgs) == dim(A)
  bmat = basis_matrix(imgs)
  return hom(A, B, bmat; check = check)
end

function hom(A::R, B::S, M::T; check = true) where {R <: AbstractAssociativeAlgebra, S <: AbstractAssociativeAlgebra, T <: MatElem}
  h = AbsAlgAssMor{R, S, T}(A, B, M)
  if check
    for a in basis(A), b in basis(A)
      if h(a * b) != h(a) * h(b)
        error("Data does not define an algebra homomorphism")
      end
    end
  end
  return h
end

function hom(A::R, B::S, M::T, N::T; check = true) where {R <: AbstractAssociativeAlgebra, S <: AbstractAssociativeAlgebra, T <: MatElem}
  # TODO: add check
  return AbsAlgAssMor{R, S, T}(A, B, M, N)
end

#function hom(A::StructureConstantAlgebra{R}, B::StructureConstantAlgebra{S}, M::T) where {R <: StructureConstantAlgebra, S <: StructureConstantAlgebra, T}
#  return AlgAssMor{R, S, T}(A, B, M)
#end
#
#function hom(A::StructureConstantAlgebra{R}, B::StructureConstantAlgebra{S}, M::T, N::T) where {R <: StructureConstantAlgebra, S <: StructureConstantAlgebra, T}
#  return AlgAssMor{R, S, T}(A, B, M, N)
#end

function has_preimage_with_preimage(m::AbsAlgAssMor, a::AbstractAssociativeAlgebraElem)
  if isdefined(m, :imat)
    return true, preimage(m, a)
  end

  A = parent(a)
  t = matrix(base_ring(A), 1, dim(A), coefficients(a))
  b, p = can_solve_with_solution(m.mat, t, side = :left)
  if b
    return true, domain(m)([ p[1, i] for i = 1:nrows(m.mat) ])
  else
    return false, zero(domain(m))
  end
end

#function preimage(m::AbsAlgAssMor, a::AbstractAssociativeAlgebraElem)
#  @assert parent(a) === codomain(m)
#  fl, b = has_preimage_with_preimage(m, a)
#  !fl && error("Element has no preimage")
#  return b
#end

# inverse

function inv(m::AbsAlgAssMor)
  if isdefined(m, :imat)
    return hom(codomain(m), domain(m), m.imat, m.mat)
  end

  imat = inv(m.mat)
  m.imat = imat

  return hom(codomain(m), domain(m), imat, m.mat)
end

################################################################################
#
#  Morphisms between algebras and number fields
#
################################################################################

# S is the type of the algebra, T the element type of the algebra
mutable struct AbsAlgAssToNfAbsMor{S, T, U, V} <: Map{S, U, HeckeMap, AbsAlgAssToNfAbsMor}
  header::MapHeader{S, U}
  mat::V
  imat::V
  t::V # dummy vector used in image and preimage
  tt::V # another dummy vector

  function AbsAlgAssToNfAbsMor{S, T, U, V}(A::S, K::U, M::V, N::V) where {S, T, U, V}

    z = new{S, T, U, V}()
    z.mat = M
    z.imat = N
    z.t = zero_matrix(base_field(K), 1, dim(A))
    z.tt = zero_matrix(base_field(K), 1, degree(K))

    function _image(x::T)
      for i = 1:dim(A)
        z.t[1, i] = coefficients(x, copy = false)[i]
      end
      s = z.t*M
      return K(parent(K.pol)([ s[1, i] for i = 1:degree(K) ]))
    end

    function _preimage(x)
      for i = 1:degree(K)
        z.tt[1, i] = coeff(x, i - 1)
      end
      s = z.tt*N
      return A([ s[1, i] for i = 1:dim(A) ])
    end

    z.header = MapHeader{S, U}(A, K, _image, _preimage)
    return z
  end
end

function AbsAlgAssToNfAbsMor(A::S, K::U, M::V, N::V) where {S, U, V}
  return AbsAlgAssToNfAbsMor{S, elem_type(A), U, V}(A, K, M, N)
end

function _abs_alg_ass_to_nf_abs_mor_type(A::AbstractAssociativeAlgebra{T}) where {T}
  return AbsAlgAssToNfAbsMor{typeof(A), elem_type(A), _ext_type(T), dense_matrix_type(T)}
end

################################################################################
#
#  Morphisms between algebras and finite fields
#
################################################################################

# Morphism between an algebra A and a finite field Fq.
# base_ring(A) can be a fpField, a EuclideanRingResidueField{ZZRingElem} or a Fq(Nmod)FiniteField, Fq can be a
# Fq(Nmod)FiniteField.
# MatType is the type of matrices over base_ring(A), PolyRingType the type of a
# polynomial ring over base_ring(A)
mutable struct AbsAlgAssToFqMor{S, T, MatType, PolyRingType} <: Map{S, T, HeckeMap, AbsAlgAssToFqMor}
  header::MapHeader{S, T}
  mat::MatType
  imat::MatType
  t::MatType # dummy vector used in image and preimage
  tt::MatType # another dummy vector
  R::PolyRingType
  RtoFq::FqPolyRingToFqMor # only used if S == AbstractAssociativeAlgebra{FqPolyRepFieldElem} or S == AbstractAssociativeAlgebra{fqPolyRepFieldElem}

  # First case: base_ring(A) == F_p
  function AbsAlgAssToFqMor{S, T, MatType, PolyRingType}(A::S, Fq::T, M::MatType, N::MatType, R::PolyRingType) where {
           S, T, MatType, PolyRingType
           #S <: AbstractAssociativeAlgebra{S1} where { S1 <: Union{ fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem} } },
           #T <: Union{ fqPolyRepField, FqPolyRepField },
           #MatType <: Union{ fpMatrix, Generic.MatSpaceElem{EuclideanRingResidueFieldElem{ZZRingElem}} },
           #PolyRingType <: Union{ fpPolyRing, FpPolyRing }
    }

    z = new{S, T, MatType, PolyRingType}()
    z.mat = M
    z.imat = N
    z.t = zero_matrix(base_ring(A), 1, dim(A))
    z.tt = zero_matrix(base_ring(A), 1, dim(A))
    z.R = R

    function _image(x::AbstractAssociativeAlgebraElem)
      @assert typeof(x) == elem_type(A)
      for i = 1:dim(A)
        z.t[1, i] = coefficients(x, copy = false)[i]
      end
      s = z.t*M
      sR = z.R([ s[1, i] for i = 1:dim(A) ])
      return Fq(sR)
    end

    function _preimage(x::Union{ fqPolyRepFieldElem, FqPolyRepFieldElem })
      @assert typeof(x) == elem_type(T)
      for i = 1:dim(A)
        z.tt[1, i] = base_ring(A)(coeff(x, i - 1))
      end
      s = z.tt*N
      return A([ s[1, i] for i = 1:dim(A) ])
    end

    z.header = MapHeader{S, T}(A, Fq, _image, _preimage)
    return z
  end

  # Second case: base_ring(A) == F_p^n
  function AbsAlgAssToFqMor{S, T, MatType, PolyRingType}(A::S, Fq::T, M::MatType, N::MatType, R::PolyRingType, RtoFq::FqPolyRingToFqMor) where {
                                                                                                                                               S, T, MatType, PolyRingType
           #S <: AbstractAssociativeAlgebra{S1} where { S1 <: Union{ FqPolyRepFieldElem, fqPolyRepFieldElem } },
           #T <: Union{ fqPolyRepField, FqPolyRepField },
           #MatType <: Union{ fqPolyRepMatrix, FqPolyRepMatrix },
           #PolyRingType <: Union{ fqPolyRepPolyRing, FqPolyRepPolyRing }
    }

    z = new{S, T, MatType, PolyRingType}()
    z.mat = M
    z.imat = N
    z.t = zero_matrix(base_ring(A), 1, dim(A))
    z.tt = zero_matrix(base_ring(A), 1, dim(A))
    z.R = R
    z.RtoFq = RtoFq

    function _image(x::AbstractAssociativeAlgebraElem)
      @assert typeof(x) == elem_type(A)
      for i = 1:dim(A)
        z.t[1, i] = coefficients(x, copy = false)[i]
      end
      s = z.t*M
      sR = z.R([ s[1, i] for i = 1:dim(A) ])
      return Fq(z.RtoFq(sR))
    end

    function _preimage(x::Union{ fqPolyRepFieldElem, FqPolyRepFieldElem, FqFieldElem })
      @assert typeof(x) == elem_type(T)
      x = z.RtoFq\x
      for i = 1:dim(A)
        z.tt[1, i] = base_ring(A)(coeff(x, i - 1))
      end
      s = z.tt*N
      return A([ s[1, i] for i = 1:dim(A) ])
    end

    z.header = MapHeader{S, T}(A, Fq, _image, _preimage)
    return z
  end

end

function AbsAlgAssToFqMor(A::AbstractAssociativeAlgebra{fpFieldElem}, Fq::fqPolyRepField, M::fpMatrix, N::fpMatrix, R::fpPolyRing)
  return AbsAlgAssToFqMor{typeof(A), fqPolyRepField, fpMatrix, fpPolyRing}(A, Fq, M, N, R)
end

function AbsAlgAssToFqMor(A::AbstractAssociativeAlgebra{fqPolyRepFieldElem}, Fq::fqPolyRepField, M::fqPolyRepMatrix, N::fqPolyRepMatrix, R::fqPolyRepPolyRing, RtoFq::FqPolyRingToFqMor)
  return AbsAlgAssToFqMor{typeof(A), fqPolyRepField, fqPolyRepMatrix, fqPolyRepPolyRing}(A, Fq, M, N, R, RtoFq)
end

#function AbsAlgAssToFqMor(A::AbstractAssociativeAlgebra{EuclideanRingResidueFieldElem{ZZRingElem}}, Fq::FqPolyRepField, M::Generic.MatSpaceElem{EuclideanRingResidueFieldElem{ZZRingElem}}, N::Generic.MatSpaceElem{EuclideanRingResidueFieldElem{ZZRingElem}}, R::FpPolyRing)
function AbsAlgAssToFqMor(A, Fq::FqPolyRepField, M, N, R::FpPolyRing)
  return AbsAlgAssToFqMor{typeof(A), FqPolyRepField, typeof(M), FpPolyRing}(A, Fq, M, N, R)
end

function AbsAlgAssToFqMor(A::AbstractAssociativeAlgebra{FqPolyRepFieldElem}, Fq::FqPolyRepField, M::FqPolyRepMatrix, N::FqPolyRepMatrix, R::FqPolyRepPolyRing, RtoFq::FqPolyRingToFqMor)
  return AbsAlgAssToFqMor{typeof(A), FqPolyRepField, FqPolyRepMatrix, FqPolyRepPolyRing}(A, Fq, M, N, R, RtoFq)
end

function AbsAlgAssToFqMor(A::AbstractAssociativeAlgebra{FqFieldElem}, Fq::FqField, M::FqMatrix, N::FqMatrix, R::FqPolyRing, RtoFq)
  return AbsAlgAssToFqMor{typeof(A), FqField, FqMatrix, FqPolyRing}(A, Fq, M, N, R, RtoFq)
end

################################################################################
#
#  Maps to orders
#
################################################################################

function (f::AbsAlgAssMor)(O::AlgAssAbsOrd)
  domain(f) != algebra(O) && error("Order not an order of the domain")
  B = codomain(f)
  # dirty trick, because it does not work for orders
  J = ideal_from_lattice_gens(B, elem_type(B)[f(b) for b in O.basis_alg])
  C = order(B, basis(J), check = false, isbasis = true)
  return C
end

function (f::AbsAlgAssMor)(I::AlgAssAbsOrdIdl)
  domain(f) != algebra(I) && error("Order not an order of the domain")
  B = codomain(f)
  J = ideal_from_lattice_gens(B, elem_type(B)[f(b) for b in basis(I)])
  return J
end
