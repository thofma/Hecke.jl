mutable struct AlgAssMor{R, S, T} <: Map{AlgAss{R}, AlgAss{S}, HeckeMap, AlgAssMor}
  header::MapHeader{AlgAss{R}, AlgAss{S}}

  mat::T
  imat::T
  c_t::T
  d_t::T

  function AlgAssMor(A::AlgAss{R}, B::AlgAss{S}, M::T) where {R, S, T}
    z = new{R, S, T}()
    z.c_t = similar(M, 1, dim(A))
    z.d_t = similar(M, 1, dim(B))
    z.mat = M

    function image(a::AlgAssElem)
      for i in 1:dim(A)
        z.c_t[1, i] = a.coeffs[i]
      end
      s = Vector{S}(undef, dim(B))
      #mul!(z.d_t, z.c_t, M) # there is no mul! for Generic.Mat
      z.d_t = z.c_t*M
      for i in 1:dim(B)
        s[i] = z.d_t[1, i]
      end

      return AlgAssElem{S}(B, s)
    end

    z.header = MapHeader(A, B, image)
    return z
  end

  function AlgAssMor(A::AlgAss{R}, B::AlgAss{S}, M::T, N::T) where {R, S, T}
    z = new{R, S, T}()
    z.c_t = similar(M, 1, dim(A))
    z.d_t = similar(M, 1, dim(B))

    z.mat = M
    z.imat = N

    function image(a::AlgAssElem)
      for i in 1:dim(A)
        z.c_t[1, i] = a.coeffs[i]
      end
      s = Vector{S}(undef, dim(B))
      #mul!(z.d_t, z.c_t, M) # there is no mul! for Generic.Mat
      z.d_t = z.c_t * M
      for i in 1:dim(B)
        s[i] = z.d_t[1, i]
      end

      return AlgAssElem{S}(B, s)
    end

    function preimage(a::AlgAssElem)
      for i in 1:dim(B)
        z.d_t[1, i] = a.coeffs[i]
      end
      s = Vector{R}(undef, dim(A))
      z.c_t = z.d_t * N
      for i in 1:dim(A)
        s[i] = z.c_t[1, i]
      end
      return AlgAssElem{R}(A, s)
    end

    z.header = MapHeader(A, B, image, preimage)
    return z
  end
 

end

function compose_and_squash(f::AlgAssMor{R, R, T}, g::AlgAssMor{R, R, T}) where {R, T}
  if isdefined(f, :imat) && isdefined(g, :imat)
    return AlgAssMor(domain(g), codomain(f), g.mat * f.mat, f.imat * g.imat)
  else
    return AlgAssMor(domain(g), codomain(f), g.mat * f.mat)
  end
end

