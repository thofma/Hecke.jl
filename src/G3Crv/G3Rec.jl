#Reconstruction code by Thomas Bouchet from https://github.com/Thittho/Reconstruction
#With permission from Thomas

function DOBis(f::MPolyRingElem{T}) where T
  R = parent(f)
  K = base_field(R)
  p = characteristic(K)
  DO_invs = dixmier_ohno_invariants(f)
  if _P in [19, 47, 277, 523] 
    DO_invs[3] += DO_invs[4] 
  end
  return DO_invs
end
#Reconstruct a ternary quartic from a generic tu_Ple of Dixmier-Ohno DO_invariants. 
#It is not implemented for characteristic 2, 3, 5, 7 or 17.
function reconstruct_from_dixmier_ohno(DO_invs::Vector{T}) where T
  K = parent(DO_invs[1])
  p = characteristic(K)

  @req !(p in [2, 3, 5, 7, 17])  "Not implemented for char 2, 3, 5, 7 or 17 "

  if p in [19, 47, 277, 523] 
    DO_invs[3] += DO_invs[4] 
  end
  
  M = matrix([[Hecke.G3_inv_P11(DO_invs), Hecke.G3_inv_P12(DO_invs), Hecke.G3_inv_P13(DO_invs)],
                [Hecke.G3_inv_P21(DO_invs), Hecke.G3_inv_P22(DO_invs), Hecke.G3_inv_P23(DO_invs)],
                [Hecke.G3_inv_P31(DO_invs), Hecke.G3_inv_P32(DO_invs), Hecke.G3_inv_P33(DO_invs)]])
  R, (x, y, z) = polynomial_ring(K, [:x,:y,:z])
  
  f = Hecke.G3_inv_P1111(DO_invs)*x^4 + 4*Hecke.G3_inv_P1112(DO_invs)*x^3*y +
      4*Hecke.G3_inv_P1113(DO_invs)*x^3*z + 6*Hecke.G3_inv_P1122(DO_invs)*x^2*y^2 +
      12*Hecke.G3_inv_P1123(DO_invs)*x^2*y*z + 6*Hecke.G3_inv_P1133(DO_invs)*x^2*z^2 +
      4*Hecke.G3_inv_P1222(DO_invs)*x*y^3 + 12*Hecke.G3_inv_P1223(DO_invs)*x*y^2*z +
      12*Hecke.G3_inv_P1233(DO_invs)*x*y*z^2 + 4*Hecke.G3_inv_P1333(DO_invs)*x*z^3 +
      Hecke.G3_inv_P2222(DO_invs)*y^4 + 4*Hecke.G3_inv_P2223(DO_invs)*y^3*z+
      6*Hecke.G3_inv_P2233(DO_invs)*y^2*z^2 + 4*Hecke.G3_inv_P2333(DO_invs)*y*z^3+
      Hecke.G3_inv_P3333(DO_invs)*z^4
  
  if det(M) != 0
    #TODO:Minimization
    return f
  end
  
  DO_invs1 = DOBis(f)
  weights = [3, 6, 9, 9, 12, 12, 15, 15, 18, 18, 21, 21, 27]
  if weighted_equality(DO_invs, DO_invs1, weights)
      return f
  end
  error("Not a basis, not implemented yet.")
end