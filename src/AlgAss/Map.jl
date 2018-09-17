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
