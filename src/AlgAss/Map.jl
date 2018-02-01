mutable struct AlgAssMor{R, S, T} <: Map{AlgAss{R}, AlgAss{S}}
  header::MapHeader{AlgAss{R}, AlgAss{S}}

  mat::T
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
      s = Vector{S}(dim(B))
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
end

function compose_and_squash(f::AlgAssMor{R, R, T}, g::AlgAssMor{R, R, T}) where {R, T}
  return AlgAssMor(domain(g), codomain(f), g.mat * f.mat)
end

