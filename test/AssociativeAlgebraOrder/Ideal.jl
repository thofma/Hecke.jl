@testset "Associative algebra ideals" begin
  @testset "PID" begin
    A = matrix_algebra(QQ, 2)
    O = Hecke.new_order(A, ZZ, basis(A); is_basis = true)
    LO = Hecke.lattice(O)
    U = Hecke.unit_ideal(O)
    Z = Hecke.zero_ideal(O)

    @test U isa Hecke.AssociativeAlgebraIdeal
    @test ideal_type(typeof(O)) == typeof(U)
    @test Hecke.fractional_ideal_type(typeof(O)) == typeof(U)
    @test order(U) === O
    @test Hecke.lattice(U) == LO
    @test algebra(U) === A
    @test base_ring(U) === ZZ
    @test Hecke.rank(U) == dim(A)
    @test Hecke.ambient_rank(U) == dim(A)
    @test Hecke.is_full_lattice(U)
    @test Hecke.is_full_rank(U)
    @test isone(U)
    @test one(U) == U
    @test iszero(Z)
    @test Hecke.is_left_ideal(Z)
    @test Hecke.is_right_ideal(Z)

    Iunknown = ideal(O, 2*LO; side = nothing, check = false)
    @test Hecke.is_left_ideal(Iunknown)
    @test Hecke.is_right_ideal(Iunknown)
    @test_throws ErrorException ideal(O, LO; side = :invalid)
    @test_throws ErrorException Hecke._test_ideal_sidedness(U, :invalid)

    I = ideal(O, 2*LO; side = :twosided)
    J = ideal(O, 3*LO; side = :twosided)
    @test ideal(O, 2*identity_matrix(QQ, dim(A));
                side = :twosided, is_basis_matrix = true) == I
    @test ideal(O, 2 .* basis(A); side = :twosided) == I
    @test basis_matrix(I) == 2*identity_matrix(QQ, dim(A))
    @test 2*basis(A)[1] in I
    @test !(basis(A)[1] in I)
    @test O(2)*O(1) in I
    @test issubset(I, U)
    @test !issubset(U, I)
    @test I + J == U
    @test intersect(I, J) == 6*U
    @test I*J == 6*U
    @test hash(ideal(O, 2*LO; side = :twosided)) == hash(I)
    @test copy(I) === I

    E12 = A(QQ[0 1; 0 0])
    IL = ideal(O, E12, :left)
    IR = ideal(O, E12, :right)
    @test Hecke.is_left_ideal(IL)
    @test !Hecke.is_right_ideal(IL)
    @test Hecke.is_right_ideal(IR)
    @test !Hecke.is_left_ideal(IR)
    @test ideal(O, O(E12), :left) == IL
    @test E12*I == O(E12)*I
    @test I*E12 == I*O(E12)

    IT = ideal(O, E12)
    @test Hecke.is_left_ideal(IT)
    @test Hecke.is_right_ideal(IT)
    @test ideal(O) == U
  end

  @testset "Dedekind domain" begin
    K, = quadratic_field(5)
    R = maximal_order(K)
    A = matrix_algebra(K, 2)
    O = Hecke.new_order(A, R, basis(A))
    LO = Hecke.lattice(O)
    U = Hecke.unit_ideal(O)
    Z = Hecke.zero_ideal(O)
    I = ideal(O, 2*LO; side = :twosided)

    C = [fractional_ideal(R, one(R)) for _ in 1:dim(A)]
    PM = pseudo_matrix(R, 2*identity_matrix(K, dim(A)), C)
    PB = [Hecke._pseudo_element(2*x, R) for x in basis(A)]

    @test length(Hecke.pseudo_basis(I)) == dim(A)
    @test_throws ArgumentError basis(I)
    @test ideal(O, PM; side = :twosided, is_basis_matrix = true) == I
    @test ideal(O, PB; side = :twosided) == I
    @test Hecke.is_left_ideal(I)
    @test Hecke.is_right_ideal(I)
    @test iszero(Z)
    @test Z + I == I
    @test intersect(U, I) == I
    @test I*I == 4*U
  end
end
