@testset "Random lines" begin
  P = Hecke.enumerate_lines(GF(5), 20)
  io = IOBuffer()
  show(io, MIME"text/plain"(), P)
  show(Hecke.AbstractAlgebra.terse(io), P)
  show(io, P)
  for i in 1:100
    v = rand(P)
    @test !iszero(v) && isone(v[findfirst(!iszero, v)])
  end
end

@testset "Line orbits" begin
  # The orbits returned by line_orbits partition the lines and have the
  # stated lengths, for every matrix type with its own helpers and for a
  # relative field.
  function is_line_orbit_partition(G, res)
    K = base_ring(G[1])
    n = nrows(G[1])
    normalize(v) = inv(v[findfirst(!iszero, v)]) .* v
    orbit_of = Dict{Vector{elem_type(K)}, Int}()
    for (i, (v, len)) in enumerate(res)
      v = normalize(v)
      haskey(orbit_of, v) && return false
      orbit_of[v] = i
      orb = [v]
      j = 1
      while j <= length(orb)
        for g in G
          wg = matrix(K, 1, n, orb[j]) * g
          w = normalize([wg[1, k] for k in 1:n])
          if !haskey(orbit_of, w)
            orbit_of[w] = i
            push!(orb, w)
          elseif orbit_of[w] != i
            return false
          end
        end
        j += 1
      end
      length(orb) == len || return false
    end
    return length(orbit_of) == length(Hecke.enumerate_lines(K, n))
  end

  function random_invertible(K, n)
    g = rand(matrix_space(K, n, n))
    while is_zero(det(g))
      g = rand(matrix_space(K, n, n))
    end
    return g
  end

  F = GF(3, 2)
  Fx, x = F[:x]
  L, = finite_field(x^2 + x + gen(F), :b)
  fields = [Native.GF(5), Native.GF(ZZ(5)), Native.finite_field(3, 2, "a")[1],
            Native.finite_field(ZZ(3), 2, "a")[1], GF(5), F, L]
  for K in fields
    G = [random_invertible(K, 3)]
    @test is_line_orbit_partition(G, line_orbits(G))
    @test is_line_orbit_partition(G, Hecke._line_orbits(G))
  end
end
