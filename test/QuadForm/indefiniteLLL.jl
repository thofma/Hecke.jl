# Helper function to check how reduced a basis is
function find_gamma(H::MatElem{QQFieldElem})
  O,M = Hecke._gram_schmidt(H,QQ)
  d = diagonal(O)
  gamma =[abs(d[i])//abs(d[i+1]) for i=1:ncols(H)-1]
  gamma_max = maximum(gamma)
  return gamma_max
end

@testset "Complete to basis" begin
  w = ZZ[ 0 2  3  0 ; -5 3 -5 -5; 4 3 -5  4; 1 2 3 4; 0 1 0 0]
  v = ZZ[ 0 2  3  0; -5 3 -5 -5; 4 3 -5  4]

  x = Hecke._complete_to_basis(w)
  y = Hecke._complete_to_basis(v)

  @test x[end, :] == w[end, :]
  @test abs(det(x)) == 1
  @test y[end, :] == v[end, :]
  @test abs(det(y)) == 1
end

@testset "Quad form solve triv" begin
  G1 = ZZ[1 2; 2 3]
  v1 = Hecke._quadratic_form_solve_triv(G1)
  @test v1[1] == G1 && v1[2] == identity_matrix(G1)

  G2 = ZZ[0 1 0; 1 -2 3; 0 3 1]
  v2 = Hecke._quadratic_form_solve_triv(G2)
  @test v2[3]*G2*transpose(v2[3]) == 0

  G3 = ZZ[1 0 0 0; 0 -1 3 4; 0 3 -1 1; 0 4 1 1]
  v3 = Hecke._quadratic_form_solve_triv(G3;base = true)
  @test v3[2][1:1,:] == v3[3]
  @test v3[3] * G3 * transpose(v3[3]) == 0
end

@testset "lll gram indef with transform" begin
  # Finds an isotropic vector
  G0 = ZZ[0 1 2; 1 -1 3; 2 3 0]
  H0,U0 = Hecke.lll_gram_indef_with_transform(G0)
  @test U0*G0*transpose(U0) == H0 
  @test H0[1,1] == 0

  G1 = ZZ[1 2 3; 2 -1 0 ; 3 0 0]
  H1,U1 = Hecke.lll_gram_indef_with_transform(G1)
  @test U1*G1*transpose(U1) == H1
  gamma_H1 = find_gamma(change_base_ring(QQ,H1))
  gamma_G1 = find_gamma(change_base_ring(QQ,G1))
  @test  gamma_H1 <= gamma_G1 
  @test abs(G1[1,1])^3 <= gamma_H1^3 * abs(det(G1))

  A = ZZ[1 -1 2 3; 2 4 0 1; 0 0 -1 3; 1 1 2 0]
  G2 = A+transpose(A)
  H2,U2 = Hecke.lll_gram_indef_with_transform(G2)
  @test U2*G2*transpose(U2) == H2
  gamma_H2 = find_gamma(change_base_ring(QQ,H2))
  gamma_G2 = find_gamma(change_base_ring(QQ,G2))
  @test  gamma_H2 <= gamma_G2
  @test abs(G2[1,1])^4 <= gamma_H2^6 * abs(det(G2))

  # Finds an isotropic vector
  G3 = ZZ[1 0 -2 3;0 -1 1 1;-2 1 0 4; 3 1 4 0]
  H3,U3 = Hecke.lll_gram_indef_with_transform(G3)
  @test U3*G3*transpose(U3) == H3
  gamma_H3 = find_gamma(change_base_ring(QQ,H3[2:3,2:3]))
  gamma_G3 = find_gamma(change_base_ring(QQ,G3[2:3,2:3]))
  @test  gamma_H3 <= gamma_G3
  @test H3[1,1] == 0

  G4 = ZZ[2 2 2 0 3; 2 0 3 1 0;2 3 -6 -4 -3; 0 1 -4 2 6; 3 0 -3 6 0]
  H4,U4 = Hecke.lll_gram_indef_with_transform(G4)
  @test U4*G4*transpose(U4) == H4
  gamma_H4 = find_gamma(change_base_ring(QQ,H4))
  gamma_G4 = find_gamma(change_base_ring(QQ,G4))
  @test  gamma_H4 <= gamma_G4
  @test abs(G4[1,1])^5 <= gamma_H4^10 * abs(det(G4))

  # Finds an isotropic vector
  G5 = ZZ[2 2 1 12 0 0; 2 -4 -1 1 2 6;1 -1 8 1 2 5;12 1 1 2 0 2 ; 0 2 2 0 0 0; 0 6 5 2 0 -2]
  H5,U5 = Hecke.lll_gram_indef_with_transform(G5)
  @test U5*G5*transpose(U5) == H5
  gamma_H5 = find_gamma(change_base_ring(QQ,H5[2:5,2:5]))
  gamma_G5 = find_gamma(change_base_ring(QQ,G5[2:5,2:5]))
  @test  gamma_H5 <= gamma_G5
  @test H5[1,1] == 0

  G6 = ZZ[2 0 3 2 0 6; 0 6 0 2 1 0; 3 0 -4 0 1 1;2 2 0 -4 2 4;0 1 1 2 4 -2;6 0 1 4 -2 4]
  H6,U6 = Hecke.lll_gram_indef_with_transform(G6)
  @test U6*G6*transpose(U6) == H6
  gamma_H6 = find_gamma(change_base_ring(QQ,H6))
  gamma_G6 = find_gamma(change_base_ring(QQ,G6))
  @test  gamma_H6 <= gamma_G6
  @test abs(G6[1,1])^6 <= gamma_H6^15 * abs(det(G6))

  G7 = ZZ[1 2 ;2 -1]
  H7,U7 = Hecke.lll_gram_indef_with_transform(G7)
  @test U7*G7*transpose(U7) == H7
  gamma_H7 = find_gamma(change_base_ring(QQ,H7))
  gamma_G7 = find_gamma(change_base_ring(QQ,G7))
  @test  gamma_H7 <= gamma_G7
  @test abs(G7[1,1])^2 <= gamma_H7 * abs(det(G7))

  G8 = ZZ[1 2 3 4 5 6; 2 1 0 0 0 0; 3 0 1 0 0 0; 4 0 0 1 0 0 ; 5 0 0 0 5 2; 6 0 0 0 2 -3]
  H8, U8 = Hecke.lll_gram_indef_with_transform(G8)
  HH8, UU8 = Hecke.lll_gram_indef_with_transform(H8)
  @test U8*G8*transpose(U8) == H8
  gamma_H8 = find_gamma(change_base_ring(QQ,HH8))
  gamma_G8 = find_gamma(change_base_ring(QQ,G8))
  @test  gamma_H8 <= gamma_G8

  L = integer_lattice(gram = G8)
  L2 = lattice(ambient_space(L), U8*basis_matrix(L))
  L3 = lattice(ambient_space(L2), UU8*basis_matrix(L2))
  @test L == L3

  gen1 = integer_genera((1,1),1)
  L1 = representative(gen1[1])
  H1,U1 = Hecke.lll_gram_indef_with_transform(change_base_ring(ZZ,gram_matrix(L1)))
  Lat1 = lattice(ambient_space(L1),U1*basis_matrix(L1))
  @test L1 == Lat1

  gen2 = integer_genera((2,1),1)
  L2 = representative(gen2[1])
  H2,U2 = Hecke.lll_gram_indef_with_transform(change_base_ring(ZZ,gram_matrix(L2)))
  Lat2 = lattice(ambient_space(L2),U2*basis_matrix(L2))
  @test L2 == Lat2

  gen3 = integer_genera((2,2),1)
  L3 = representative(gen3[1])
  H3,U3 = Hecke.lll_gram_indef_with_transform(change_base_ring(ZZ,gram_matrix(L3)))
  Lat3 = lattice(ambient_space(L3),U3*basis_matrix(L3))
  @test L3 == Lat3

  gen4 = integer_genera((2,3),1)
  L4 = representative(gen4[1])
  H4,U4 = Hecke.lll_gram_indef_with_transform(change_base_ring(ZZ,gram_matrix(L4)))
  Lat4 = lattice(ambient_space(L4),U4*basis_matrix(L4))
  @test L4 == Lat4

  gen5 = integer_genera((1,5),1)
  L5 = representative(gen5[1])
  H5,U5 = Hecke.lll_gram_indef_with_transform(change_base_ring(ZZ,gram_matrix(L5)))
  Lat5 = lattice(ambient_space(L5),U5*basis_matrix(L5))
  @test L5 == Lat5

  gen6 = integer_genera((4,2),1)
  L6 = representative(gen6[1])
  H6,U6 = Hecke.lll_gram_indef_with_transform(change_base_ring(ZZ,gram_matrix(L6)))
  Lat6 = lattice(ambient_space(L6),U6*basis_matrix(L6))
  @test L6 == Lat6

  gen7 = integer_genera((1,3),1)
  L7 = representative(gen7[1])
  H7,U7 = Hecke.lll_gram_indef_with_transform(change_base_ring(ZZ,gram_matrix(L7)))
  Lat7 = lattice(ambient_space(L7),U7*basis_matrix(L7))
  @test L7 == Lat7

  gen8 = integer_genera((1,2),1)
  L8 = representative(gen8[1])
  H8,U8 = Hecke.lll_gram_indef_with_transform(change_base_ring(ZZ,gram_matrix(L8)))
  Lat8 = lattice(ambient_space(L8),U8*basis_matrix(L8))
  @test L8 == Lat8

  gen9 = integer_genera((3,3),1)
  L9 = representative(gen9[1])
  H9,U9 = Hecke.lll_gram_indef_with_transform(change_base_ring(ZZ,gram_matrix(L9)))
  Lat9 = lattice(ambient_space(L9),U9*basis_matrix(L9))
  @test L9 == Lat9

  gen10 = integer_genera((1,3),1)
  L10 = representative(gen10[1])
  H10,U10 = Hecke.lll_gram_indef_with_transform(change_base_ring(ZZ,gram_matrix(L10)))
  Lat10 = lattice(ambient_space(L10),U10*basis_matrix(L10))
  @test L10 == Lat10
end

@testset "lll gram indef ternary hyperbolic" begin
  G = ZZ[1 0 0; 0 4 3; 0 3 2]
  H,U = Hecke.lll_gram_indef_ternary_hyperbolic(G)
  gamma_H = find_gamma(change_base_ring(QQ,H))
  gamma_G = find_gamma(change_base_ring(QQ,G))
  @test gamma_H < gamma_G
end
