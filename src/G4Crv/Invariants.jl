#Invariants code by Thomas Bouchet from https://github.com/Thittho/Genus-4
#With permission from Thomas

@doc raw"""
    g4_invariants(C::HypellCrv{T}) -> Vector{T}, Vector{Int}
Returns the invariants of a genus 4 curve C
and the corresponding weights.
"""
function g4_invariants(Q::MPolyRingElem{T}, Gamma::MPolyRingElem{T}) where T
 	R0 = parent(Q)
	@req (R0 == parent(Gamma)) "Q and Gamma must have the same parent"
	@req (number_of_variables(R0) == 4) "Q and Gamma must be polynomials in 4 variables"
	@req is_homogeneous(Q) && is_homogeneous(Gamma) "Q and Gamma must be homogeneous"
	@req (total_degree(Q) == 2) && (total_degree(Gamma) == 3) "Q must be of degree 2 and Gamma of degree 3"


  X, Y, Z, W = gens(R0)
	K = base_ring(R0)

	# Detect quadric rank and choose a canonical basis
	if Q == X*W - Y*Z
		f0 = Gamma
		P = identity_matrix(K, 4)
		t = 4
  elseif Q == X*Z - Y^2
		f0 = Gamma
		P = identity_matrix(K, 4)
		t = 3
	else
		P, t = quad_4_normal_form(Q)
    f0 = transformation_GLn(Gamma, P)
	end

	# Rank 4 case
	if t == 3 || t == 4
    invs, ws = _compute_invs_ws(f0, det(P), t)
    invs = elem_type(K)[K(inv) for inv in invs]

		return invs, ws
  end
  error("Rank has to be 3 or 4.")
end

function quadratic_form_to_matrix(f::MPolyRingElem{T}) where T <: FieldElem
  R = parent(f)
  K = base_ring(R)
  d = number_of_variables(R)
  M = zero_matrix(K, d, d)
  if characteristic(K) == 2
    error("Cannot construct matrix over characteristic 2.")
  end
  for i in (1:d)
    for j in (1:d)
      index = zeros(Int, d)
      index[i]+=1
      index[j]+=1
      if i == j
        M[i, j] = coeff(f, index)
      else
        M[i, j] = coeff(f, index)/2
      end
    end
  end
  
  return M
end

function _compute_invs_ws(f0::MPolyRingElem{T}, detP::T, t::Int) where T <: FieldElem
  L = base_ring(parent(f0))
  if t == 4
    R, (x, y, u, v) = polynomial_ring(L, 4)
    B = f0(x*u, y*u, x*v, y*v)
    f_bic = 1/detP^3 * B

		invs, ws = invariants_genus4_curves_rank4(f_bic)
    return invs, ws
  else 
    R, (s, t, w) = polynomial_ring(L, 3)
		B = f0(s^2, s*t, t^2, w)
    @req coeff(B, w^3) != 0 "The curve is singular."

		# Normalize weighted sextic
		alpha = coeff(B, w^3)
		B /= alpha
		B = B(s, t, w - coefficients(B, 3)[3]/3)
    S, x = polynomial_ring(L, 2)
		invs, ws = invariants_genus4_curves_rank3(f_weighted(x[1], x[2], S(0)), (coefficients(f_weighted, 3)[2])(x[1], x[2], S(0)))
		invs = weighted_multiply(invs, ws,  alpha/detP^3)
    return invs, ws
  end
end

function quad_4_normal_form(Q::MPolyRingElem{T}) where T
   # /* Given a quadratic form Q in 4 variables, put it in the form XT-YZ when Q defines a smooth quadric surface, or XZ-Y^2 when it defines a quadric cone.
   # Output: 
   #     - P_fin is the transformation to that basis such that Q^P_fin = XT-YZ or XZ-Y^2,
   #     - t is the rank of Q as a quadratic form */
  K = base_ring(parent(Q))
  M = quadratic_form_to_matrix(Q)
  t = rank(M)
  D, P = Hecke._gram_schmidt(M, identity, false)
  diags = [D[i,i] for i in (1:4)]
  
  if t < 3
    error("Warning: The quadric is not of rank 3 or 4")
  elseif t == 4
    L = [-diags[4]/D[1, 1], -D[3, 3]/D[2, 2]]
    return _quad_4_subroutine(P, K, D, L)
  else 
    i = 1
    if T <: Union{ArbFieldElem, AcbFieldElem}
      _, i = findmin([abs(D[j, j]) for j in (1:4)])
    else
      while (D[i, i] != 0) && (i < 4)
        i = i+1
      end 
    end

    L_swap = [1,2,3,4]
    L_swap[i] = 4
    L_swap[4] = i
    S_4 = Hecke.SymmetricGroup(4)
    P_swap = S_4(L_swap)

    D_new = P_swap*D*P_swap
    P = P_swap*P
    L = [-D_new[3, 3]/D_new[1, 1], -D_new[2, 2]]
    return _quad_4_subroutine(P, K, D_new, L)
  end
end

function _quad_4_subroutine(P::MatElem{T}, K::Field, D::MatElem{T}, L::Vector{T}) where T <: FieldElem

  bool1, sq1 = is_power(L[1], 2)
  bool2, sq2 = is_power(L[2], 2)

  if bool1 && bool2
    S1 = K
    _, sq1 = is_power(L[1], 2)
    _, sq2 = is_power(L[2], 2)
    Sq = [sq1, sq2]
    P = change_base_ring(S1, P)
    P_fin = _helper_test(change_base_ring(S1, D), Sq) * P
    return transpose(P_fin), 4
  else
    R, x = polynomial_ring(K)
    S2 = splitting_field((x^2-L[1])*(x^2-L[2]))::Field
    Sq = [sqrt(S2(L[1])), sqrt(S2(L[2]))]
    P = change_base_ring(S2, P)
    P_fin = _helper_test(change_base_ring(S2, D), Sq) * P
    return transpose(P_fin), 4
  end
end

function _helper_test(D::MatElem{T}, Sq::Vector{T}) where T <: FieldElem
  S = parent(Sq[1])
  P_fin = matrix(S, 4, 4, [1//(2*D[1, 1]), S(0), S(0), S(1)//(2*D[1, 1]*Sq[1]),
          S(0), S(-1)//(2*D[2, 2]), S(-1)//(2*D[2, 2]*Sq[2]), S(0), 
          S(0), S(1//2), S(-1)//(2*Sq[2]), S(0), 
          S(1//2), S(0), S(0), S(-1)//(2*Sq[1])])
return P_fin
end

function invariants_genus4_curves_rank4(f::MPolyRingElem{T}, normalize = false) where T <:FieldElem
	K = base_ring(parent(f))

  GCD_hsop = [288, 12288, 746496, 12582912, 1741425868800, 19327352832, 764411904, 144, 570630428688384, 4076863488]
	GCD_others = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 144, 144, 144, 1, 1, 1, 1, 1, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144 ]

	Jac = transvectant(f, f, 1, 1)
	H = transvectant(f, f, 2, 2)

	# Covariants
	# Degree 3
	c31 = transvectant(H, f, 2, 2)/1536

	c331 = transvectant(Jac, f, 2, 2)
	c332 = transvectant(H, f, 1, 1)

	# Degree 4
	c421 = transvectant(H, H, 1, 1)
	c422 = transvectant(c31, f, 1, 1)
	c423 = transvectant(c332, f, 2, 2)

	c441 = transvectant(c332, f, 1, 1)
	c442 = transvectant(transvectant(Jac, f, 1, 1), f, 2, 2)

	# Degree 5
	c511 = transvectant(c422, f, 2, 2)/144
	c512 = transvectant(c441, f, 3, 3)/995328
	c513 = transvectant(c442, f, 3, 3)/1492992

	c531 = transvectant(c422, f, 1, 1)
	c532 = transvectant(c423, f, 1, 1)
	c533 = transvectant(transvectant(f^3, f, 3, 3), f, 3, 3)

	# Degree 6
	c621 = transvectant(c531, f, 2, 2)
	c622 = transvectant(c532, f, 2, 2)
	c623 = transvectant(c511, f, 1, 1)

	# Degree 7
	c711 = transvectant(c621, f, 2, 2)/9216
	c712 = transvectant(c511, transvectant(f, f, 2, 2), 1, 1)/32
	c713 = transvectant(c512, transvectant(f, f, 2, 2), 1, 1)/96
    
	c731 = transvectant(c622, f, 1, 1)
	c732 = transvectant(c623, f, 1, 1)

	# Degree 8 
	c821 = transvectant(c711, f, 1, 1)
	c822 = transvectant(c732, f, 2, 2)

	c84 = transvectant(c731, f, 1, 1)

	# Degree 9
	c91 = transvectant(c822, f, 2, 2)
	
	c931 = transvectant(c821, f, 1, 1)
	c932 = transvectant(c84, f, 2, 2)

	# Degree 10
	c102 = transvectant(c91, f, 1, 1)

	# Degree 11
	c111 = transvectant(c102, f, 2, 2)

	c113 = transvectant(c932*f, f, 3, 3)

	# Invariants
	# HSOP
	I2 = K(transvectant(f, f, 3, 3, true))#288
	I41 = K(transvectant(H, H, 2, 2, true))# 12288
	I42 = K(transvectant(c331, f, 3, 3, true))# 746496
	I61 = K(transvectant(H, c421, 2, 2, true))# 12582912
	I62 = K(transvectant(c533, f, 3, 3, true))# 1741425868800
	I81 = K(transvectant(c421, c421, 2, 2, true))# 19327352832
	I82 = K(transvectant(c731, f, 3, 3, true))# 764411904
	I10 = K(transvectant(f, c31^3, 3, 3, true))# 432
	I12 = K(transvectant(c113, f, 3, 3, true))# 570630428688384
	I14 = K(transvectant(c111*H, f, 3, 3, true))# 4076863488
	invHSOP = [I2,I41,I42,I61,I62,I81,I82,I10,I12,I14]

	# Degree 6
	j61 = K(transvectant(c31, c31, 1, 1, true))#2
	inv6 = [j61]

	# Degree 8
	j81 = K(transvectant(c31, c511, 1, 1, true))#2
	j82 = K(transvectant(c31, c512, 1, 1, true))#2
	inv8 = [j81,j82]

	# Degree 10
	j101 = K(transvectant(c511, c511, 1, 1, true))#2
    j102 = K(transvectant(c511, c512, 1, 1, true))#2
    j103 = K(transvectant(c511, c513, 1, 1, true))#2
    j104 = K(transvectant(c512, c512, 1, 1, true))#2
    j105 = K(transvectant(c512, c513, 1, 1, true))#2
    j106 = K(transvectant(c513, c513, 1, 1, true))#2
	inv10 = [j101,j102,j103,j104,j105,j106]

	# Degree 12
    j121 = K(transvectant(c711, c511, 1, 1, true))#1
    j122 = K(transvectant(c711, c512, 1, 1, true))#2
    j123 = K(transvectant(c711, c513, 1, 1, true))#1
    j124 = K(transvectant(c712, c511, 1, 1, true))#2
    j125 = K(transvectant(c712, c512, 1, 1, true))#6
    j126 = K(transvectant(c712, c513, 1, 1, true))#2
    j127 = K(transvectant(f, c511*c31^2, 3, 3, true))#432
    j128 = K(transvectant(f, c512*c31^2, 3, 3, true))#432
    j129 = K(transvectant(f, c513*c31^2, 3, 3, true))#432
	inv12 = [j121,j122,j123,j124,j125,j126,j127,j128,j129]

	# Degree 14
	j141 = K(transvectant(c711, c711, 1, 1, true))#2
    j142 = K(transvectant(c711, c712, 1, 1, true))#1
	j143 = K(transvectant(c711, c713, 1, 1, true))#2
    j144 = K(transvectant(c712, c713, 1, 1, true))#2
	j145 = K(transvectant(c713, c713, 1, 1, true))#2
    j146 = K(transvectant(f, c511*c511*c31, 3, 3, true))#144
    j147 = K(transvectant(f, c511*c512*c31, 3, 3, true))#432
    j148 = K(transvectant(f, c511*c513*c31, 3, 3, true))#144
    j149 = K(transvectant(f, c512*c512*c31, 3, 3, true))#432
    j1410 = K(transvectant(f, c512*c513*c31, 3, 3, true))#432
    j1411 = K(transvectant(f, c513*c513*c31, 3, 3, true))#144
    j1412 = K(transvectant(f, c711*c31*c31, 3, 3, true))#432
	inv14 = [j141,j142,j143,j144,j145,j146,j147,j148,j149,j1410,j1411,j1412]

	# Degree 16
	j161 = K(transvectant(f, c711*c511*c31, 3, 3, true))#144
    j162 = K(transvectant(f, c711*c512*c31, 3, 3, true))#432
    j163 = K(transvectant(f, c711*c513*c31, 3, 3, true))#144
    j164 = K(transvectant(f, c712*c511*c31, 3, 3, true))#144
    j165 = K(transvectant(f, c511*c511*c511, 3, 3, true))#432
    j166 = K(transvectant(f, c511*c511*c512, 3, 3, true))#144
    j167 = K(transvectant(f, c511*c511*c513, 3, 3, true))#144
    j168 = K(transvectant(f, c511*c512*c512, 3, 3, true))#432
    j169 = K(transvectant(f, c511*c512*c513, 3, 3, true))#144
    j1610 = K(transvectant(f, c511*c513*c513, 3, 3, true))#144
    j1611 = K(transvectant(f, c512*c512*c512, 3, 3, true))#432
    j1612 = K(transvectant(f, c512*c512*c513, 3, 3, true))#432
    j1613 = K(transvectant(f, c512*c513*c513, 3, 3, true))#144
    j1614 = K(transvectant(f, c513*c513*c513, 3, 3, true))#432
    inv16 = [j161,j162,j163,j164,j165,j166,j167,j168,j169,j1610,j1611,j1612,j1613,j1614]


	# Degree 18
	j181 = K(transvectant(f, c711*c711*c31, 3, 3, true))#144
	j182 = K(transvectant(f, c711*c511*c511, 3, 3, true))#144
	j183 = K(transvectant(f, c711*c511*c512, 3, 3, true))#144
	j184 = K(transvectant(f, c711*c511*c513, 3, 3, true))#144
	j185 = K(transvectant(f, c711*c512*c512, 3, 3, true))#432
  j186 = K(transvectant(f, c711*c512*c513, 3, 3, true))#144
	j187 = K(transvectant(f, c711*c513*c513, 3, 3, true))#144
	j188 = K(transvectant(f, c711*c712*c31, 3, 3, true))#144
	j189 = K(transvectant(f, c712*c712*c31, 3, 3, true))#144
	j1810 = K(transvectant(f, c712*c511*c512, 3, 3, true))#144
	j1811 = K(transvectant(f, c712*c512*c512, 3, 3, true))#432
	inv18 = [j181,j182,j183,j184,j185,j186,j187,j188,j189,j1810,j1811]

	inv_others = vcat(inv6, inv8, inv10, inv12, inv14, inv16, inv18)

	invs = map(K, vcat([invHSOP[i]/GCD_hsop[i] for i in (1:length(invHSOP))], [inv_others[i]/GCD_others[i] for i in (1:length(inv_others))]))

	ws = [2,4,4,6,6,8,8,10,12,14,6,8,8,10,10,10,10,10,10,12,12,12,12,12,12,12,12,12,14,14,14,14,14,14,14,14,14,14,14,14,16,16,16,16,16,16,16,16,16,16,16,16,16,16,18,18,18,18,18,18,18,18,18,18,18]

	if normalize
		return weighted_reduction(invs, ws), ws
	end

	return invs, ws
end

function invariants_genus4_curves_rank3(f::MPolyRingElem{T}, v::MPolyRingElem{T}) where T
	K = base_ring(parent(f))

	# Covariants of f
	h24 = transvectant(f, f, 4)
	h28 = transvectant(f, f, 2)
	h32 = transvectant(h24, f, 4)
	h36 = transvectant(h24, f, 2)
	h38 = transvectant(h24, f, 1)
	h312 = transvectant(h28, f, 1)
	h44 = transvectant(h32, f, 2)
	h46 = transvectant(h32, f, 1)
	h52 = transvectant(h24, h32, 2)
	h54 = transvectant(h24, h32, 1)
	h58 = transvectant(h28, h32, 1)
	h661 = transvectant(h38, h32, 2)
	h662 = transvectant(h36, h32, 1)
	h74 = transvectant(f, h32^2, 3)
	h82 = transvectant(h24, h32^2, 3)
	h94 = transvectant(h38, h32^2, 4)
	h102 = transvectant(h32^3, f, 5)

	# Covariants of v
	k24 = transvectant(v, v, 2)
	k36 = transvectant(v, k24, 1)

	# Invariants
	# Invariants of f
	J2f = K(transvectant(f, f, 6)(0,0))
	J4f = K(transvectant(h24, h24, 4)(0,0))
	J6f = K(transvectant(h32, h32, 2)(0,0))
	J10f = K(transvectant(h32^3, f, 6)(0,0))
	J15f = K(transvectant(h38, h32^4, 8)(0,0))
	invf = [J2f, J4f, J6f, J10f, J15f]

	# Invariants of v
	J2v = K(transvectant(v, v, 4)(0,0))
	J3v = K(transvectant(k24, v, 4)(0,0))
	invv = [J2v, J3v]

	#  Joint degree 3
	J3 = K(transvectant(h24, v, 4)(0,0))
	inv3 = [J3]

	#  Joint degree 4
	J41 = K(transvectant(h28, v^2, 8)(0,0))
	J42 = K(transvectant(h24, k24, 4)(0,0))
	J43 = K(transvectant(k36, f, 6)(0,0))
	inv4 = [J41, J42, J43]

	# Joint degree 5
	J51 = K(transvectant(h38, v^2, 8)(0,0))
	J52 = K(transvectant(h44, v, 4)(0,0))
	J53 = K(transvectant(h28, v*k24, 8)(0,0))
	J54 = K(transvectant(f^2, v^3, 12)(0,0))
	inv5 = [J51, J52, J53, J54]

	# Joint degree 6
	J61 = K(transvectant(h38, v*k24, 8)(0,0))
	J62 = K(transvectant(f^2, v^2*k24, 12)(0,0))
	J63 = K(transvectant(h28, k24^2, 8)(0,0))
	J64 = K(transvectant(h36, k36, 6)(0,0))
	J65 = K(transvectant(h312, v^3, 12)(0,0))
	J66 = K(transvectant(h54, v, 4)(0,0))
	J67 = K(transvectant(h44, k24, 4)(0,0))
	J68 = K(transvectant(h32*f, v^2, 8)(0,0))
	inv6 = [J61, J62, J63, J64, J65, J66, J67, J68]

	# Joint degree 7
	J71 = K(transvectant(h32^2, v, 4)(0,0))
	J72 = K(transvectant(h54, k24, 4)(0,0))
	J73 = K(transvectant(h58, v^2, 8)(0,0))
	J74 = K(transvectant(f*h36, v^3, 12)(0,0))
	J75 = K(transvectant(f^2, v*k24^2, 12)(0,0))
	J76 = K(transvectant(h32*f, v*k24, 8)(0,0))
	J77 = K(transvectant(h46, k36, 6)(0,0))
	J78 = K(transvectant(h312, v^2*k24, 12)(0,0))
	J79 = K(transvectant(h38, k24^2, 8)(0,0))
	inv7 = [J71, J72, J73, J74, J75, J76, J77, J78, J79]

	# Joint degree 8
	J81 = K(transvectant(h32*h24, k36, 6)(0,0))
	J82 = K(transvectant(h312, v*k24^2, 12)(0,0))
	J83 = K(transvectant(h32*h36, v^2, 8)(0,0))
	J84 = K(transvectant(h32^2, k24, 4)(0,0))
	J85 = K(transvectant(h74, v, 4)(0,0))
	J86 = K(transvectant(f*h46, v^3, 12)(0,0))
	J87 = K(transvectant(f*h36, v^2*k24, 12)(0,0))
	J88 = K(transvectant(h32*f, k24^2, 8)(0,0))
	J89 = K(transvectant(h58, v*k24, 8)(0,0))
	inv8 = [J81, J82, J83, J84, J85, J86, J87, J88, J89]

	# Joint degree 9
	J91 = K(transvectant(h74, k24, 4)(0,0))
	J92 = K(transvectant(h32*h52, v, 4)(0,0))
	J93 = K(transvectant(h52*f, v*k24, 8)(0,0))
	J94 = K(transvectant(h312, k24^3, 12)(0,0))
	J95 = K(transvectant(h32*h28, v*k36, 10)(0,0))
	J96 = K(transvectant(f*h46, v^2*k24, 12)(0,0))
	J97 = K(transvectant(h36^2, v^3, 12)(0,0))
	J98 = K(transvectant(h32*h46, v^2, 8)(0,0))
	inv9 = [J91, J92, J93, J94, J95, J96, J97, J98]

	# Joint degree 10
	J101 = K(transvectant(h94, v, 4)(0,0))
	J102 = K(transvectant(h32*h28, k24*k36, 10)(0,0))
	J103 = K(transvectant(h52*h36, v^2, 8)(0,0))
	J104 = K(transvectant(f*h661, v^3, 12)(0,0))
	inv10 = [J101, J102, J103, J104]

	# Joint degree 11
	J111 = K(transvectant(h52^2, v, 4)(0,0))
	J112 = K(transvectant(f*h662, v^2*k24, 12)(0,0))
	J113 = K(transvectant(h32*h661, v^2, 8)(0,0))
	inv11 = [J111, J112, J113]

	# Joint degree 12
	J121 = K(transvectant(h32*h82, v, 4)(0,0))
	J122 = K(transvectant(h32*h662, v*k24, 8)(0,0))
	inv12 = [J121, J122]

	# Joint degree 13
	J13 = K(transvectant(h82*h36, v^2, 8)(0,0))
	inv13 = [J13]

	# Joint degree 14
	J14 = K(transvectant(h32*h102, v, 4)(0,0))
	inv14 = [J14]

	return vcat(invf, invv, inv3, inv4, inv5, inv6, inv7, inv8, inv9, inv10, inv11, inv12, inv13, inv14), 
  [6,12,18,30,45,4,6,8,10,10,9,13,14,12,12,15,14,14,15,15,17,16,16,20,19,19,18,16,18,18,17,17,21,19,22,22,23,21,20,20,21,25,26,24,21,23,23,24,25,29,25,28,27,32,29,31,35,33,37,41]
end

