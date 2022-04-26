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
#  quad_form_lll_gram_indefgoon
#######################################################

  G0 = ZZ[0 1 2; 1 -1 3; 2 3 0]
  H0,U0 = Hecke.quad_form_lll_gram_indefgoon(G0)
  @test transpose(U0)*G0*U0 == H0 
  @test abs(det(U0)) == 1 
 
  G1 = ZZ[1 2 3; 2 -1 0 ; 3 0 0]
  H1,U1 = Hecke.quad_form_lll_gram_indefgoon(G1)
  @test transpose(U1)*G1*U1 == H1
  @test abs(det(U1)) == 1 
  O1, M1 = Hecke._gram_schmidt(change_base_ring(QQ,H1),QQ)
  for i = 1:ncols(O1)-1
    @test abs(O1[i,i]) <= 2*abs(O1[i+1,i+1])
  end

  G2 = ZZ[1 2 3; 2 -1 -1; 3 -1 0] 
  H2,U2 = Hecke.quad_form_lll_gram_indefgoon(G2)
  @test transpose(U2)*G2*U2 == H2
  @test abs(det(U2)) == 1 

  G3 = ZZ[0 2 3; 2 -1 0; 3 0 0] 
  H3,U3 = Hecke.quad_form_lll_gram_indefgoon(G3)
  @test transpose(U3)*G3*U3 == H3
  @test abs(det(U3)) == 1 

  G4 = ZZ[0 1 3; 1 2 1; 3 1 0] 
  H4,U4 = Hecke.quad_form_lll_gram_indefgoon(G4)
  @test transpose(U4)*G4*U4 == H4
  @test abs(det(U4)) == 1 

  G5 = ZZ[1 2 0; 2 -1 1 ; 0 1 -1] 
  H5,U5 = Hecke.quad_form_lll_gram_indefgoon(G5)
  @test transpose(U5)*G5*U5 == H5
  @test abs(det(U5)) == 1 

  G6 = ZZ[1 2 ;2 -1]
  H6,U6 = Hecke.quad_form_lll_gram_indefgoon(G6)
  @test transpose(U6)*G6*U6 == H6
  @test abs(det(U6)) == 1 
  O6, M6 = Hecke._gram_schmidt(change_base_ring(QQ,H6),QQ)
  for i = 1:ncols(O6)-1
    @test abs(O6[i,i]) <= 2*abs(O6[i+1,i+1])
  end

  G7 = ZZ[1 2 3 4 5 6; 2 1 0 0 0 0; 3 0 1 0 0 0; 4 0 0 1 0 0 ; 5 0 0 0 5 2; 6 0 0 0 2 -3]
  H7,U7 = Hecke.quad_form_lll_gram_indefgoon(G7)
  @test transpose(U7)*G7*U7 == H7
  @test abs(det(U7)) == 1 
  O7, M7 = Hecke._gram_schmidt(change_base_ring(QQ,H7),QQ)
  for i = 1:ncols(O7)-1
    @test abs(O7[i,i]) <= 3*abs(O7[i+1,i+1])
  end

end