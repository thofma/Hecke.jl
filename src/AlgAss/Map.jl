mutable struct AbsAlgAssMor{R, S, T} <: Map{R, S, HeckeMap, AbsAlgAssMor}
  header::MapHeader{R, S}

  mat::T
  imat::T
  c_t::T
  d_t::T

  function AbsAlgAssMor{R, S, T}(A::R, B::S, M::T) where {R, S, T}
    z = new{R, S, T}()
    z.c_t = similar(M, 1, dim(A))
    z.d_t = similar(M, 1, dim(B))
    z.mat = M

    function image(a)
      for i in 1:dim(A)
        z.c_t[1, i] = a.coeffs[i]
      end
      s = Vector{elem_type(base_ring(B))}(undef, dim(B))
      #mul!(z.d_t, z.c_t, M) # there is no mul! for Generic.Mat
      z.d_t = z.c_t*M
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

    z.mat = M
    z.imat = N

    function image(a)
      for i in 1:dim(A)
        z.c_t[1, i] = a.coeffs[i]
      end
      s = Vector{elem_type(base_ring(B))}(undef, dim(B))
      #mul!(z.d_t, z.c_t, M) # there is no mul! for Generic.Mat
      z.d_t = z.c_t * M
      for i in 1:dim(B)
        s[i] = z.d_t[1, i]
      end

      return B(s)
    end

    function preimage(a)
      for i in 1:dim(B)
        z.d_t[1, i] = a.coeffs[i]
      end
      s = Vector{elem_type(base_ring(A))}(undef, dim(A))
      z.c_t = z.d_t * N
      for i in 1:dim(A)
        s[i] = z.c_t[1, i]
      end
      return A(s)
    end

    z.header = MapHeader(A, B, image, preimage)
    return z
  end
end

#mutable struct AlgAssMor{R, S, T} <: Map{AlgAss{R}, AlgAss{S}, HeckeMap, AlgAssMor}
#  header::MapHeader{AlgAss{R}, AlgAss{S}}
#
#  mat::T
#  imat::T
#  c_t::T
#  d_t::T
#
#  function AlgAssMor(A::AlgAss{R}, B::AlgAss{S}, M::T) where {R, S, T}
#    z = new{R, S, T}()
#    z.c_t = similar(M, 1, dim(A))
#    z.d_t = similar(M, 1, dim(B))
#    z.mat = M
#
#    function image(a::AlgAssElem)
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
#      return AlgAssElem{S}(B, s)
#    end
#
#    z.header = MapHeader(A, B, image)
#    return z
#  end
#
#  function AlgAssMor(A::AlgAss{R}, B::AlgAss{S}, M::T, N::T) where {R, S, T}
#    z = new{R, S, T}()
#    z.c_t = similar(M, 1, dim(A))
#    z.d_t = similar(M, 1, dim(B))
#
#    z.mat = M
#    z.imat = N
#
#    function image(a::AlgAssElem)
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
#      return AlgAssElem{S}(B, s)
#    end
#
#    function preimage(a::AlgAssElem)
#      for i in 1:dim(B)
#        z.d_t[1, i] = a.coeffs[i]
#      end
#      s = Vector{R}(undef, dim(A))
#      z.c_t = z.d_t * N
#      for i in 1:dim(A)
#        s[i] = z.c_t[1, i]
#      end
#      return AlgAssElem{R}(A, s)
#    end
#
#    z.header = MapHeader(A, B, image, preimage)
#    return z
#  end
#end

function compose_and_squash(f::AbsAlgAssMor{R, U, T}, g::AbsAlgAssMor{S, R, T}) where {R, T, S, U}
  if isdefined(f, :imat) && isdefined(g, :imat)
    return hom(domain(g), codomain(f), g.mat * f.mat, f.imat * g.imat)
  else
    return hom(domain(g), codomain(f), g.mat * f.mat)
  end
end

function hom(A::R, B::S, M::T) where {R <: AbsAlgAss, S <: AbsAlgAss, T}
  return AbsAlgAssMor{R, S, T}(A, B, M)
end

function hom(A::R, B::S, M::T, N::T) where {R <: AbsAlgAss, S <: AbsAlgAss, T}
  return AbsAlgAssMor{R, S, T}(A, B, M, N)
end

#function hom(A::AlgAss{R}, B::AlgAss{S}, M::T) where {R <: AlgAss, S <: AlgAss, T}
#  return AlgAssMor{R, S, T}(A, B, M)
#end
#
#function hom(A::AlgAss{R}, B::AlgAss{S}, M::T, N::T) where {R <: AlgAss, S <: AlgAss, T}
#  return AlgAssMor{R, S, T}(A, B, M, N)
#end

################################################################################
#
#  Morphisms between algebras and number fields
#
################################################################################

# S is the type of the algebra, T the element type of the algebra
mutable struct AbsAlgAssToNfAbsMor{S, T} <: Map{S, AnticNumberField, HeckeMap, AbsAlgAssToNfAbsMor}
  header::MapHeader{S, AnticNumberField}
  M::fmpq_mat
  N::fmpq_mat
  t::fmpq_mat # dummy vector used in image and preimage
  tt::fmpq_mat # another dummy vector

  function AbsAlgAssToNfAbsMor{S, T}(A::S, K::AnticNumberField, M::fmpq_mat, N::fmpq_mat) where { S <: AbsAlgAss{fmpq}, T <: AbsAlgAssElem{fmpq} }

    z = new{S, T}()
    z.M = M
    z.N = N
    z.t = zero_matrix(FlintQQ, 1, dim(A))
    z.tt = zero_matrix(FlintQQ, 1, degree(K))

    function _image(x::T)
      for i = 1:dim(A)
        z.t[1, i] = x.coeffs[i]
      end
      s = z.t*N
      return K(parent(K.pol)([ s[1, i] for i = 1:degree(K) ]))
    end

    function _preimage(x::nf_elem)
      for i = 1:degree(K)
        z.tt[1, i] = coeff(x, i - 1)
      end
      s = z.tt*M
      return A([ s[1, i] for i = 1:dim(A) ])
    end

    z.header = MapHeader{S, AnticNumberField}(A, K, _image, _preimage)
    return z
  end

  # a is a primitive element in A
  function AbsAlgAssToNfAbsMor{S, T}(A::S, K::AnticNumberField, a::T) where { S <: AbsAlgAss{fmpq}, T <: AbsAlgAssElem{fmpq} }

    s = one(A)
    M = zero_matrix(FlintQQ, dim(A), dim(A))
    elem_to_mat_row!(M, 1, s)
    for i = 2:dim(A)
      s = mul!(s, s, a)
      elem_to_mat_row!(M, i, s)
    end

    return AbsAlgAssToNfAbsMor{S, T}(A, K, M, inv(M))
  end
end

function AbsAlgAssToNfAbsMor(A::AbsAlgAss{fmpq}, K::AnticNumberField, M::fmpq_mat, N::fmpq_mat)
  return AbsAlgAssToNfAbsMor{typeof(A), elem_type(A)}(A, K, M, N)
end

function AbsAlgAssToNfAbsMor(A::AbsAlgAss{fmpq}, K::AnticNumberField, a::AbsAlgAssElem{fmpq})
  return AbsAlgAssToNfAbsMor{typeof(A), elem_type(A)}(A, K, a)
end
