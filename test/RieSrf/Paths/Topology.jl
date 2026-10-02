# The standard form [0 I 0; -I 0 0; 0 0 0] of size n with blocks of size g.
function _standard_symplectic_form(g::Int, n::Int)
  J = zero_matrix(ZZ, n, n)
  for k in 1:g
    J[k, g + k] = 1
    J[g + k, k] = -1
  end
  return J
end

@testset "Topology" begin
  @testset "Symplectic reduction" begin
    J = _standard_symplectic_form(2, 5)
    # a signed permutation of the standard form: only swaps needed
    perm = [3, 5, 1, 2, 4]
    signs = [1, -1, -1, 1, 1]
    U = zero_matrix(ZZ, 5, 5)
    for i in 1:5
      U[i, perm[i]] = signs[i]
    end
    K = transpose(U) * J * U
    S = RSM.symplectic_reduction(K)
    @test abs(det(S)) == 1
    @test S * K * transpose(S) == J
    # elimination needed
    K = matrix(ZZ, [0 1 1; -1 0 1; -1 -1 0])
    S = RSM.symplectic_reduction(K)
    @test abs(det(S)) == 1
    @test S * K * transpose(S) == _standard_symplectic_form(1, 3)
  end

  @testset "Homology basis (Tretkoff): $name" for (name, f, g) in FAST_CURVES[[5, 9]]
    model = RSM.original_model(_rs(f, 100))
    m = degree(f, 2)
    cycles, K, S = RSM.homology_basis(model)
    @test length(cycles) == 2*g + m - 1
    @test K == -transpose(K)
    @test rank(K) == 2*g
    @test abs(det(S)) == 1
    @test S * K * transpose(S) == _standard_symplectic_form(g, 2*g + m - 1)
    # every cycle starts and ends on a sheet and alternates sheets and chains
    @test all(isodd(length(cycle)) && cycle[1] == cycle[end] for cycle in cycles)
  end
end
