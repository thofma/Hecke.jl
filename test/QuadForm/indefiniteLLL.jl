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

  function find_delta(H::MatElem{fmpq})
    O,M = Hecke._gram_schmidt(H,QQ)
    d = diagonal(O)
    delta =[abs(d[i])//abs(d[i+1]) for i=1:ncols(H)-1]
    delta_max = maximum(delta)
    return delta_max
  end
  
  G0 = ZZ[0 1 2; 1 -1 3; 2 3 0]
  H0,U0 = Hecke.lll_gram_indefgoon(G0)
  @test transpose(U0)*G0*U0 == H0 

  G1 = ZZ[1 2 3; 2 -1 0 ; 3 0 0]
  H1,U1 = Hecke.lll_gram_indefgoon(G1)
  @test transpose(U1)*G1*U1 == H1
  @test find_delta(change_base_ring(QQ,H1)) <= find_delta(change_base_ring(QQ,G1))
  
  A = ZZ[1 -1 2 3; 2 4 0 1; 0 0 -1 3; 1 1 2 0]
  G2 = A+transpose(A)
  H2,U2 = Hecke.lll_gram_indefgoon(G2)
  @test transpose(U2)*G2*U2 == H2
  @test find_delta(change_base_ring(QQ,H2)) <= find_delta(change_base_ring(QQ,G2))

  G3 = ZZ[1 0 -2 3;0 -1 1 1;-2 1 0 4; 3 1 4 0]
  H3,U3 = Hecke.lll_gram_indefgoon(G3)
  @test transpose(U3)*G3*U3 == H3
  @test find_delta(change_base_ring(QQ,H3[2:3,2:3])) <= find_delta(change_base_ring(QQ,G3[2:3,2:3]))

  G4 = ZZ[2 2 2 0 3; 2 0 3 1 0;2 3 -6 -4 -3; 0 1 -4 2 6; 3 0 -3 6 0]
  H4,U4 = Hecke.lll_gram_indefgoon(G4)
  @test transpose(U4)*G4*U4 == H4
  @test find_delta(change_base_ring(QQ,H4)) <= find_delta(change_base_ring(QQ,G4))
  
  #=
  G2 = ZZ[1 2 3; 2 -1 -1; 3 -1 0] 
  H2,U2 = Hecke.lll_gram_indefgoon(G2)
  @test transpose(U2)*G2*U2 == H2
  @test abs(det(U2)) == 1 

  G3 = ZZ[0 2 3; 2 -1 0; 3 0 0] 
  H3,U3 = Hecke.lll_gram_indefgoon(G3)
  @test transpose(U3)*G3*U3 == H3
  @test abs(det(U3)) == 1 

  G4 = ZZ[0 1 3; 1 2 1; 3 1 0] 
  H4,U4 = Hecke.lll_gram_indefgoon(G4)
  @test transpose(U4)*G4*U4 == H4
  @test abs(det(U4)) == 1 

  G5 = ZZ[1 2 0; 2 -1 1 ; 0 1 -1] 
  H5,U5 = Hecke.lll_gram_indefgoon(G5)
  @test transpose(U5)*G5*U5 == H5
  @test abs(det(U5)) == 1 

  G6 = ZZ[1 2 ;2 -1]
  H6,U6 = Hecke.lll_gram_indefgoon(G6)
  @test transpose(U6)*G6*U6 == H6
  @test abs(det(U6)) == 1  #G7 = ZZ[1 2 3 4 5 6; 2 1 0 0 0 0; 3 0 1 0 0 0; 4 0 0 1 0 0 ; 5 0 0 0 5 2; 6 0 0 0 2 -3]
  @test find_delta(change_base_ring(QQ,H6)) <= find_delta(change_base_ring(QQ,G6))
  
  G7 = ZZ[1 2 3 4 5 6; 2 1 0 0 0 0; 3 0 1 0 0 0; 4 0 0 1 0 0 ; 5 0 0 0 5 2; 6 0 0 0 2 -3]
  L7_G = Zlattice(gram = G7)
  H7,U7 = Hecke.lll_gram_indefgoon(G7)
  L7_H = Zlattice(gram = H7)
  @test isrationally_isometric(L7_G,L7_H)
  #@test find_delta(change_base_ring(QQ,H7)) <= find_delta(change_base_ring(QQ,G7))
  
  gen = genera((2,2),1)
  L = representative(gen[1]) #Takes pretty long to compute
  G = gram_matrix(L)
  H,U = Hecke.lll_gram_indefgoon(G)
  L1 = lattice(ambient_space(L),transpose(U)*basis_matrix(L))
  @test L == L1
  =#
end
