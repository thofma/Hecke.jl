@testset "indefiniteLLL" begin

######################################################
#                   complete_to_basis
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
#                   ker_mod_p
######################################################

  p1 = 3
  p2 = 4

  rank1, U1 = Hecke._ker_mod_p(v,p1)
  rank2, U2 = Hecke._ker_mod_p(w,p2)
  v_mod_p = change_base_ring(ResidueRing(ZZ,p1),v)
  w_mod_p = change_base_ring(ResidueRing(ZZ,p2),w)

  if (rank1 != 0)
    u1 = change_base_ring(ResidueRing(ZZ,p1),U1[:,1:rank1])
    for i = 1:rank1
      @test v_mod_p*u1[:,i] == 0
    end
  end

  if (rank2 != 0)
    u2 = change_base_ring(ResidueRing(ZZ,p2),U2[:,1:rank2])
    for i = 1:rank2
      @test w_mod_p*u2[:,i] == 0
    end
  end

######################################################
#              quad_form_solve_triv
######################################################
G1 = ZZ[1 2; 2 3]
G2 = ZZ[0 1 0; 1 -2 3; 0 3 1]
G3 = ZZ[1 0 0 0; 0 -1 3 4; 0 3 -1 1; 0 4 1 1]
v = Hecke._quad_form_solve_triv(G1)
v2 = Hecke._quad_form_solve_triv(G2)
v3 = Hecke._quad_form_solve_triv(G3)

if (typeof(v) <: MatElem)
  @test transpose(v)*G1*v == 0
elseif (length(v) == 2)
  @test v[1] == G1 && v[2] == one(parent(G1))
else
  @test v[2][:,1] == v[3]
  @test transpose(v[3]) * G1 * v[3] == 0
end

if (typeof(v2) <: MatElem)
  @test transpose(v2)*G2*v2 == 0
elseif (length(v2) == 2)
  @test v2[1] == G2 && v2[2] == one(parent(G1))
else
  @test v2[2][:,1] == v2[3]
  @test transpose(v2[3]) * G2 * v2[3] == 0
end

if (typeof(v3) <: MatElem)
  @test transpose(v3)*G3*v3 == 0
elseif (length(v3) == 2)
  @test v3[1] == G3 && v3[2] == one(parent(G1))
else
  @test v3[2][:,1] == v3[3]
  @test transpose(v3[3]) * G3 * v3[3] == 0
end

######################################################
#             quad_form_lll_gram_indefgoon
#######################################################
G = ZZ[0 1 2; 1 -1 3; 2 3 0]
G1 = ZZ[1 2 3; 2 -1 0 ; 3 0 0]
G2 = ZZ[1 2 3; 2 -1 -1; 3 -1 0] 
G3 = ZZ[0 2 3; 2 -1 0; 3 0 0] 
G4 = ZZ[0 1 3; 1 2 1; 3 1 0] 
G5 = ZZ[1 2 0; 2 -1 1 ; 0 1 -1] 
G6 = ZZ[1 2 ;2 -1]
A = ZZ[0 -1 1 3; 1 3 4 6; -1 -2 3 4; 0 -1 2 3]
G7 = A+transpose(A)
G7 = ZZ[1 2 3 4 5 6; 2 1 0 0 0 0; 3 0 1 0 0 0; 4 0 0 1 0 0 ; 5 0 0 0 5 2; 6 0 0 0 2 -3]

H,U = Hecke.quad_form_lll_gram_indefgoon(G)

if(typeof(Hecke.quad_form_lll_gram_indef(G)) <: MatElem)
  if (ncols(H) <= 3)
    @test true
  else
    O, M = Hecke._gram_schmidt(change_base_ring(QQ,H[2:ncols(H)-1,2:ncols(H)-1]),QQ)
    for i = 1:ncols(O)-1
      @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
    end
  end
else
  O, M = Hecke._gram_schmidt(change_base_ring(QQ,H),QQ)
  for i = 1:ncols(O)-1
    @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
  end
end

H1,U1 = Hecke.quad_form_lll_gram_indefgoon(G1)

if(typeof(Hecke.quad_form_lll_gram_indef(G1)) <: MatElem)
  if (ncols(H1) <= 3)
    @test true
  else
    O, M = Hecke._gram_schmidt(change_base_ring(QQ,H1[2:ncols(H1)-1,2:ncols(H1)-1]),QQ)
    for i = 1:ncols(O)-1
      @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
    end
  end
else
  O, M = Hecke._gram_schmidt(change_base_ring(QQ,H1),QQ)
  for i = 1:ncols(O)-1
    @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
  end
end

H2,U2 = Hecke.quad_form_lll_gram_indefgoon(G2)

if(typeof(Hecke.quad_form_lll_gram_indef(G2)) <: MatElem)
  if (ncols(H2) <= 3)
    @test true
  else
    O, M = Hecke._gram_schmidt(change_base_ring(QQ,H2[2:ncols(H2)-1,2:ncols(H2)-1]),QQ)
    for i = 1:ncols(O)-1
      @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
    end
  end
else
  O, M = Hecke._gram_schmidt(change_base_ring(QQ,H2),QQ)
  for i = 1:ncols(O)-1
    @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
  end
end

H3,U3 = Hecke.quad_form_lll_gram_indefgoon(G3)

if(typeof(Hecke.quad_form_lll_gram_indef(G3)) <: MatElem)
  if (ncols(H3) <= 3)
    @test true
  else
    O, M = Hecke._gram_schmidt(change_base_ring(QQ,H3[2:ncols(H3)-1,2:ncols(H3)-1]),QQ)
    for i = 1:ncols(O)-1
      @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
    end
  end
else
  O, M = Hecke._gram_schmidt(change_base_ring(QQ,H3),QQ)
  for i = 1:ncols(O)-1
    @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
  end
end

H4,U4 = Hecke.quad_form_lll_gram_indefgoon(G4)

if(typeof(Hecke.quad_form_lll_gram_indef(G4)) <: MatElem)
  if (ncols(H4) <= 3)
    @test true
  else
    O, M = Hecke._gram_schmidt(change_base_ring(QQ,H4[2:ncols(H4)-1,2:ncols(H4)-1]),QQ)
    for i = 1:ncols(O)-1
      @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
    end
  end
else
  O, M = Hecke._gram_schmidt(change_base_ring(QQ,H4),QQ)
  for i = 1:ncols(O)-1
    @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
  end
end

H5,U5 = Hecke.quad_form_lll_gram_indefgoon(G5)

if(typeof(Hecke.quad_form_lll_gram_indef(G5)) <: MatElem)
  if (ncols(H5) <= 3)
    @test true
  else
    O, M = Hecke._gram_schmidt(change_base_ring(QQ,H5[2:ncols(H5)-1,2:ncols(H5)-1]),QQ)
    for i = 1:ncols(O)-1
      @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
    end
  end
else
  O, M = Hecke._gram_schmidt(change_base_ring(QQ,H5),QQ)
  for i = 1:ncols(O)-1
    @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
  end
end

H6,U6 = Hecke.quad_form_lll_gram_indefgoon(G6)

if(typeof(Hecke.quad_form_lll_gram_indef(G6)) <: MatElem)
  if (ncols(H6) <= 3)
    @test true
  else
    O, M = Hecke._gram_schmidt(change_base_ring(QQ,H6[2:ncols(H6)-1,2:ncols(H6)-1]),QQ)
    for i = 1:ncols(O)-1
      @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
    end
  end
else
  O, M = Hecke._gram_schmidt(change_base_ring(QQ,H6),QQ)
  for i = 1:ncols(O)-1
    @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
  end
end

H7,U7 = Hecke.quad_form_lll_gram_indefgoon(G7)

if(typeof(Hecke.quad_form_lll_gram_indef(G7)) <: MatElem)
  if (ncols(H7) <= 3)
    @test true
  else
    O, M = Hecke._gram_schmidt(change_base_ring(QQ,H7[2:ncols(H7)-1,2:ncols(H7)-1]),QQ)
    for i = 1:ncols(O)-1
      @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
    end
  end
else
  O, M = Hecke._gram_schmidt(change_base_ring(QQ,H7),QQ)
  for i = 1:ncols(O)-1
    @test abs(O[i,i]) <= 4//3*abs(O[i+1,i+1])
  end
end

end