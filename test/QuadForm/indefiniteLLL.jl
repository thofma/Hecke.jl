@testset "indefiniteLLL" begin

######################################################
#  complete_to_basis
######################################################

  w = ZZ[ 0 2  3  0 ; -5 3 -5 -5; 4 3 -5  4; 1 2 3 4; 0 1 0 0]
  v = ZZ[ 0 2  3  0; -5 3 -5 -5; 4 3 -5  4]
    
  x = Hecke._complete_to_basis(w)
  y = Hecke._complete_to_basis(v)

  @test x[:,ncols(x)] == w[:,ncols(w)]
  @test det(x) == 1 || det(x) == -1
  @test y[:,ncols(y)] == v[:,ncols(v)]
  @test det(y) == 1 || det(y) == -1

######################################################
#  ker_mod_p
######################################################

  p1 = 3

  rank1, U1 = Hecke._ker_mod_p(v,p1)
  rank2, U2 = Hecke._ker_mod_p(w,p1)
  v_mod_p = change_base_ring(ResidueRing(ZZ,p1),v)
  w_mod_p = change_base_ring(ResidueRing(ZZ,p1),w)

  u1 = change_base_ring(ResidueRing(ZZ,p1),U1[:,1:rank1])
  for i = 1:rank1
    @test v_mod_p*u1[:,i] == 0
  end
  
  u2 = change_base_ring(ResidueRing(ZZ,p1),U2[:,1:rank2])
  for i = 1:rank2
    @test w_mod_p*u2[:,i] == 0
  end
 
######################################################
#  quad_form_solve_triv
######################################################

  G1 = ZZ[1 2; 2 3]
  v1 = Hecke._quad_form_solve_triv(G1)
  @test v1[1] == G1 && v1[2] == identity_matrix(G1)

  G2 = ZZ[0 1 0; 1 -2 3; 0 3 1]
  v2 = Hecke._quad_form_solve_triv(G2)
  @test transpose(v2[3])*G2*v2[3] == 0

  G3 = ZZ[1 0 0 0; 0 -1 3 4; 0 3 -1 1; 0 4 1 1]
  v3 = Hecke._quad_form_solve_triv(G3;base = true)
  @test v3[2][:,1] == v3[3]
  @test transpose(v3[3]) * G3 * v3[3] == 0
  
######################################################
#  lll_gram_indefgoon
#######################################################

  function find_gamma(H::MatElem{fmpq})
    O,M = Hecke._gram_schmidt(H,QQ)
    d = diagonal(O)
    gamma =[abs(d[i])//abs(d[i+1]) for i=1:ncols(H)-1]
    gamma_max = maximum(gamma)
    return gamma_max
  end
  
  G0 = ZZ[0 1 2; 1 -1 3; 2 3 0] #Finds an isotropic vector
  H0,U0 = Hecke.lll_gram_indefgoon(G0)
  @test transpose(U0)*G0*U0 == H0 

  G1 = ZZ[1 2 3; 2 -1 0 ; 3 0 0]
  H1,U1 = Hecke.lll_gram_indefgoon(G1)
  @test transpose(U1)*G1*U1 == H1
  gamma_H1 = find_gamma(change_base_ring(QQ,H1))
  gamma_G1 = find_gamma(change_base_ring(QQ,G1))  
  @test  gamma_H1 <= gamma_G1 
  @test abs(G1[1,1])^3 <= gamma_H1^3 * abs(det(G1))
  
  A = ZZ[1 -1 2 3; 2 4 0 1; 0 0 -1 3; 1 1 2 0]
  G2 = A+transpose(A)
  H2,U2 = Hecke.lll_gram_indefgoon(G2)
  @test transpose(U2)*G2*U2 == H2
  gamma_H2 = find_gamma(change_base_ring(QQ,H2))
  gamma_G2 = find_gamma(change_base_ring(QQ,G2))  
  @test  gamma_H2 <= gamma_G2
  @test abs(G2[1,1])^4 <= gamma_H2^6 * abs(det(G2))

  G3 = ZZ[1 0 -2 3;0 -1 1 1;-2 1 0 4; 3 1 4 0] #Finds an isotropic vector
  H3,U3 = Hecke.lll_gram_indefgoon(G3)
  @test transpose(U3)*G3*U3 == H3
  gamma_H3 = find_gamma(change_base_ring(QQ,H3[2:3,2:3]))
  gamma_G3 = find_gamma(change_base_ring(QQ,G3[2:3,2:3]))  
  @test  gamma_H3 <= gamma_G3

  G4 = ZZ[2 2 2 0 3; 2 0 3 1 0;2 3 -6 -4 -3; 0 1 -4 2 6; 3 0 -3 6 0]
  H4,U4 = Hecke.lll_gram_indefgoon(G4)
  @test transpose(U4)*G4*U4 == H4
  gamma_H4 = find_gamma(change_base_ring(QQ,H4))
  gamma_G4 = find_gamma(change_base_ring(QQ,G4))  
  @test  gamma_H4 <= gamma_G4
  @test abs(G4[1,1])^5 <= gamma_H4^10 * abs(det(G4))
  
  G5 = ZZ[2 2 1 12 0 0; 2 -4 -1 1 2 6;1 -1 8 1 2 5;12 1 1 2 0 2 ; 0 2 2 0 0 0; 0 6 5 2 0 -2] #Finds an isotropic vector
  H5,U5 = Hecke.lll_gram_indefgoon(G5)
  @test transpose(U5)*G5*U5 == H5
  gamma_H5 = find_gamma(change_base_ring(QQ,H5[2:5,2:5]))
  gamma_G5 = find_gamma(change_base_ring(QQ,G5[2:5,2:5]))  
  @test  gamma_H5 <= gamma_G5
  
  G6 = ZZ[2 0 3 2 0 6; 0 6 0 2 1 0; 3 0 -4 0 1 1;2 2 0 -4 2 4;0 1 1 2 4 -2;6 0 1 4 -2 4]
  H6,U6 = Hecke.lll_gram_indefgoon(G6)
  @test transpose(U6)*G6*U6 == H6
  gamma_H6 = find_gamma(change_base_ring(QQ,H6))
  gamma_G6 = find_gamma(change_base_ring(QQ,G6))  
  @test  gamma_H6 <= gamma_G6
  @test abs(G6[1,1])^6 <= gamma_H6^15 * abs(det(G6))
  
  G7 = ZZ[1 2 ;2 -1]
  H7,U7 = Hecke.lll_gram_indefgoon(G7)
  @test transpose(U7)*G7*U7 == H7
  gamma_H7 = find_gamma(change_base_ring(QQ,H7))
  gamma_G7 = find_gamma(change_base_ring(QQ,G7))  
  @test  gamma_H7 <= gamma_G7
  @test abs(G7[1,1])^2 <= gamma_H7 * abs(det(G7))
  
  #=
  gen1 = genera((1,1),1)
  L1 = representative(gen1[1]) 
  H1,U1 = Hecke.lll_gram_indefgoon(change_base_ring(ZZ,gram_matrix(L1)))
  Lat1 = lattice(ambient_space(L1),transpose(U1)*basis_matrix(L1))
  @test L1 == Lat1

  gen2 = genera((2,1),1)
  L2 = representative(gen2[1]) 
  H2,U2 = Hecke.lll_gram_indefgoon(change_base_ring(ZZ,gram_matrix(L2)))
  Lat2 = lattice(ambient_space(L2),transpose(U2)*basis_matrix(L2))
  @test L2 == Lat2

  gen3 = genera((2,2),1)
  L3 = representative(gen3[1]) 
  H3,U3 = Hecke.lll_gram_indefgoon(change_base_ring(ZZ,gram_matrix(L3)))
  Lat3 = lattice(ambient_space(L3),transpose(U3)*basis_matrix(L3))
  @test L3 == Lat3

  gen4 = genera((2,3),1)
  L4 = representative(gen4[1]) 
  H4,U4 = Hecke.lll_gram_indefgoon(change_base_ring(ZZ,gram_matrix(L4)))
  Lat4 = lattice(ambient_space(L4),transpose(U4)*basis_matrix(L4))
  @test L4 == Lat4

  gen5 = genera((1,5),1)
  L5 = representative(gen5[1]) 
  H5,U5 = Hecke.lll_gram_indefgoon(change_base_ring(ZZ,gram_matrix(L5)))
  Lat5 = lattice(ambient_space(L5),transpose(U5)*basis_matrix(L5))
  @test L5 == Lat5

  gen6 = genera((4,2),1)
  L6 = representative(gen6[1]) 
  H6,U6 = Hecke.lll_gram_indefgoon(change_base_ring(ZZ,gram_matrix(L6)))
  Lat6 = lattice(ambient_space(L6),transpose(U6)*basis_matrix(L6))
  @test L6 == Lat6

  gen7 = genera((1,3),1)
  L7 = representative(gen7[1]) 
  H7,U7 = Hecke.lll_gram_indefgoon(change_base_ring(ZZ,gram_matrix(L7)))
  Lat7 = lattice(ambient_space(L7),transpose(U7)*basis_matrix(L7))
  @test L7 == Lat7

  gen8 = genera((1,2),1)
  L8 = representative(gen8[1]) 
  H8,U8 = Hecke.lll_gram_indefgoon(change_base_ring(ZZ,gram_matrix(L8)))
  Lat8 = lattice(ambient_space(L8),transpose(U8)*basis_matrix(L8))
  @test L8 == Lat8

  gen9 = genera((3,3),1)
  L9 = representative(gen9[1]) 
  H9,U9 = Hecke.lll_gram_indefgoon(change_base_ring(ZZ,gram_matrix(L9)))
  Lat9 = lattice(ambient_space(L9),transpose(U9)*basis_matrix(L9))
  @test L9 == Lat9

  gen10 = genera((1,3),1)
  L10 = representative(gen10[1]) 
  H10,U10 = Hecke.lll_gram_indefgoon(change_base_ring(ZZ,gram_matrix(L10)))
  Lat10 = lattice(ambient_space(L10),transpose(U10)*basis_matrix(L10))
  @test L10 == Lat10
  =#
  #=
  G8 = ZZ[1 2 3 4 5 6; 2 1 0 0 0 0; 3 0 1 0 0 0; 4 0 0 1 0 0 ; 5 0 0 0 5 2; 6 0 0 0 2 -3]
  H8, U8 = Hecke.lll_gram_indefgoon(G8)
  @test transpose(U8)*G8*U8 == H8
  gamma_H8 = find_gamma(change_base_ring(QQ,H8))
  gamma_G8 = find_gamma(change_base_ring(QQ,G8))
  @test  gamma_H8 <= gamma_G8
  =#

end
