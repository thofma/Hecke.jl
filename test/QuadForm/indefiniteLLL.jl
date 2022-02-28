@testset "indefiniteLLL" begin

######################################################
#                   complete_to_basis
######################################################

  w = ZZ[ 0 2  3  0 ; -5 3 -5 -5; 4 3 -5  4; 1 2 3 4; 0 1 0 0]
  v = ZZ[ 0 2  3  0; -5 3 -5 -5; 4 3 -5  4]
    
  x = Hecke.complete_to_basis(w)
  y = Hecke.complete_to_basis(v)

  @test x[:,ncols(x)] == w[:,ncols(w)]
  @test det(x) == 1 || det(x) == -1
  @test y[:,ncols(y)] == v[:,ncols(v)]
  @test det(y) == 1 || det(y) == -1

######################################################
#                   ker_mod_p
######################################################

  p1 = 3
  p2 = 4

  rank1, U1 = Hecke.ker_mod_p(v,p1)
  rank2, U2 = Hecke.ker_mod_p(w,p2)
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
v = Hecke.quad_form_solve_triv(G1)
v2 = Hecke.quad_form_solve_triv(G2)
v3 = Hecke.quad_form_solve_triv(G3)

if (length(v) == 2)
  @test v == Dict([1 => G1, 2 => one(parent(G1))])
elseif (length(v) == 3)
  @test v[2][:,1] == v[3]
  @test transpose(v[3]) * G1 * v[3] == 0
else
  @test transpose(v[1])*G1*v[1] == 0
end

if (length(v2) == 2)
  @test v2 == Dict([1 => G2, 2 => one(parent(G2))])
elseif (length(v2) == 3)
  @test v2[2][:,1] == v2[3]
  @test transpose(v2[3]) * G2 * v2[3] == 0
else
  @test transpose(v2[1])*G2*v2[1] == 0
end

if (length(v3) == 2)
  @test v3 == Dict([1 => G3, 2 => one(parent(G3))])
elseif (length(v3) == 3)
  @test v3[2][:,1] == v3[3]
  @test transpose(v3[3]) * G3 * v3[3] == 0
else
  @test transpose(v3[1])*G3*v3[1] == 0
end
######################################################
#             quad_form_lll_gram_indef
#######################################################
G = ZZ[0 1 2; 1 -1 3; 2 3 0]

d = Hecke.quad_form_lll_gram_indef(G)

if(length(d) == 1)
  @test transpose(d[1])*G*d[1] == 0
end


    
end