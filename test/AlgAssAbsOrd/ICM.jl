@testset "Ideal class monoid of orders in number fields" begin

  Qx, x = FlintQQ["x"]
  f = x^3 + 31*x^2 + 43*x + 77
  K, a = number_field(f, "a")
  O = equation_order(K)
  icm = ideal_class_monoid(O)
  @test length(icm) == 59
  @test isisomorphic(evaluate(icm[1]), evaluate(icm[2]))[1] == false
  t, b = isisomorphic(O(2)*O, O(3)*O)
  @test t == true
  @test (O(3)*O)*(b*O) == K(2)*O
  t, b = isisomorphic(K(2)*O, K(3)*O)
  @test t == true
  @test (O(3)*O)*(b*O) == K(2)*O

  f = x^3 - 1000*x^2 - 1000*x - 1000
  K, a = number_field(f, "a")
  O = equation_order(K)
  icm = ideal_class_monoid(O)
  @test length(icm) == 69116

end

@testset "Ideal class monoid of orders in algebras" begin

  Qx, x = FlintQQ["x"]
  f = x^3 + 31*x^2 + 43*x + 77
  A = AlgAss(f)
  O = Order(A, basis(A))
  icm = ideal_class_monoid(O)
  @test length(icm) == 59
  @test isisomorphic(evaluate(icm[1]), evaluate(icm[2]))[1] == false
  t, b = isisomorphic(O(2)*O, O(3)*O)
  @test t == true
  @test (O(3)*O)*(b*O) == A(2)*O
  t, b = isisomorphic(A(2)*O, A(3)*O)
  @test t == true
  @test (O(3)*O)*(b*O) == A(2)*O

  f1 = x^2 + 4*x + 7
  f2 = x^3 - 9*x^2 - 3*x - 1
  A = AlgAss(f1*f2)
  O = Order(A, basis(A))
  icm = ideal_class_monoid(O)
  @test length(icm) == 852

end

@testset "Conjugacy of integral matrices" begin

  Zx, x = FlintZZ["x"]
  f = x^3 - 4x^2 + 8x + 5

  M = companion_matrix(f)
  U = identity_matrix(FlintZZ, nrows(M))
  for i = 1:nrows(M)
    for j = i + 1:ncols(M)
      U[i, j] = rand(-10:10)
    end
  end
  N = U*M*inv(U)

  b, V = isconjugate(M, N)
  @test b == true
  @test M == V*N*inv(V)

  N = identity_matrix(FlintZZ, nrows(M))
  b, V = isconjugate(M, N)
  @test b == false

  g = x^2 + 10x - 1
  h = x^2 - x + 5

  M = companion_matrix(f*g*h)
  U = identity_matrix(FlintZZ, nrows(M))
  for i = 1:nrows(M)
    for j = i + 1:ncols(M)
      U[i, j] = rand(-10:10)
    end
  end
  N = U*M*inv(U)

  b, V = isconjugate(M, N)
  @test b == true
  @test M == V*N*inv(V)

  N = identity_matrix(FlintZZ, nrows(M))
  b, V = isconjugate(M, N)
  @test b == false

end
