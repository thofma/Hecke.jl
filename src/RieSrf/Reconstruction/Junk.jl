

function reconstruct_g4_curve_from_period_matrix_QQ(tau::AcbMatrix)
  CC = base_ring(parent(tau))
  z = zeros(CC, 4)
  theta_zeros = thetas(z, tau)
  quadric, cubic = equations(reconstruct_g4_curve_from_thetas(theta_zeros))

  CC4 = Parent(quadric)
  CC = BaseRing(CC4)
  prec = Precision(CC)
  X=Matrix(CC4, 4,1, [CC4.i: i in [1..4]])

  tritangentbasis = [
    1/2*Matrix(Rationals(), 8, 1, [1, 1, 1, 0, 1, 1, 1, 0]),
    1/2*Matrix(Rationals(), 8, 1, [1, 0, 1, 0, 0, 0, 1, 0]),
    1/2*Matrix(Rationals(), 8, 1, [1, 1, 1, 0, 0, 0, 1, 0]),
    1/2*Matrix(Rationals(), 8, 1, [1, 0, 1, 0, 0, 1, 1, 0]),
    1/2*Matrix(Rationals(), 8, 1, [0, 1, 1, 0, 0, 1, 0, 0])]

  TTB = TritangentPlanes(Pi, tritangentbasis)
  

  TtoS = Matrix(TTB[1..4])
  D = DiagonalMatrix(Eltseq(Vector(TTB[5]) * (TtoS)^-1))
  M = TtoS^-1 * D^-1

  vprint Reconstruction: "Rescaling equations"
  quadric=Evaluate(quadric, Eltseq(ChangeRing(Inverse(M),CC4)*X))
  quadric_C=quadric/LeadingCoefficient(quadric)
  cubic_C=Evaluate(cubic, Eltseq(ChangeRing(Inverse(M), CC4)*X))
  
  R<x,y,z,w> = PolynomialRing(QQ, 4)
  mons2 = MonomialsOfDegree(R,2)
  mons3 = MonomialsOfDegree(R,3)
  
  h = hom< R -> CC4 | x, y, z, w>
  
  quadric_Q= R!0
  vprint Reconstruction:  quadric_C
  for m in mons2
    coeff_C = MonomialCoefficient(quadric_C, h(m))
    coeff_Q = BestApproximation(Real(coeff_C), 10^(prec div 4))
    quadric_Q += coeff_Q * m
  end
  
  V = VectorSpace(QQ, #mons3)
  U = sub< V |[Vector([MonomialCoefficient(quadric_Q *R.i, m) : m in mons3]) : i in [1..4]]> 
  B = ExtendBasis(U, V)
  Uc = B[5..#mons3]
  
  MB = Matrix(B)
  MUc = Matrix(Uc)
  
  v = Vector([MonomialCoefficient(cubic_C, h(m)) : m in mons3]) 
  w = Vector(Eltseq((v * ChangeRing(MB^(-1), CC)))[5..#mons3])
  w = (w * ChangeRing(MUc, CC))
  
  scalar, i = Maximum([Abs(k) : k in Eltseq(w)])
  
  w = w/w[i]
  
  cubic_C = &+[w[i] * h(mons3[i]) : i in [1..#mons3]]
  cubic_Q= R!0
  vprint Reconstruction:  cubic_C
  vprint Reconstruction: "Trying to recognize coefficients over QQ"
  for m in mons3
    coeff_C = MonomialCoefficient(cubic_C, h(m))
    coeff_Q = BestApproximation(Real(coeff_C), 10^(prec div 4))
    cubic_Q += coeff_Q * m
  end
  
  return [quadric_Q, cubic_Q]
end

function azygetic_system_flip(g::Int)
zer = zero_matrix(GF(2), g, g)
  zer1 = zero_matrix(GF(2), g, 1)
	zer2 = zero_matrix(GF(2), g, 2)
	id = identity_matrix(GF(2), g)
	triang = zer
	for i in (1:g)
		for j in (i:g)
			triang[i,j] = 1
		end
	end

  odd_chars = [triang; id]
	even_chars = [[zer1 triang zer1] ; [id zer2] ]
  return [odd_chars even_chars]
end

function decompose_symplectic(S::MatElem)
  ZZ4 = residue_ring(ZZ, 4)
  n = number_of_rows(S)/2

  id_ZZ = identity_matrix(ZZ, n)
  zero_block_ZZ = zero_matrix(ZZ, n, n)

  J = [zero_block_ZZ id_ZZ
      -id_ZZ zero_block_ZZ]
  A = S[1 : n, 1 : n]
  B = S[1 : n, n + 1 : 2*n]
  C = S[n + 1 : 2*n, 1 : n]
  D = S[n + 1 : 2*n, n + 1 : 2*n]


  C_ech, T1 = echelon_form_with_transformation(C)
  diag, T2 = echelon_form_with_transformation(transpose(C_ech))

  T1lift = lift_SL_n(T1, 3)
  T2lift = lift_SL_n(T2, 3)

  ret1 = [change_base_ring(block_diagonal_matrix(transpose(T1lift), T1lift^(-1)), ZZ)]
  ret2 = [change_base_ring(block_diagonal_matrix(transpose(T2lift)^(-1),  T2lift), ZZ)]
  trafo1 = block_diagonal_matrix(transpose(T1) , T1^(-1))
  trafo2 = block_diagonal_matrix(transpose(T2)^(-1), T2)

  S = trafo1^(-1)*S*trafo2^(-1)

  A = S[1 : n, 1 : n]
  B = S[1 : n, n + 1 : 2*n]
  C = S[n + 1 : 2*n, 1 : n]
  D = S[n + 1 : 2*n, n + 1 : 2*n]

  nu = maximum(filter(x -> x!= 0, diagonal(diag)init = 0))
  X = identity_matrix(GF(2), nu) - A[1:nu, 1:nu]
  X = block_diagonal_matrix(X, zero_matrix(GF(2), n - nu, n - nu))
  trafo = BlockMatrix(2,2,[[id, X], [zer, id]])
  push!(ret1, change_base_ring(trafo, ZZ))
  S = trafo^(-1)*S
  A = S[1:n, 1:n]
  Alift = lift_SL_n(A,3)
  trafo = block_diagonal_matrix(A , transpose(A)^(-1))
  push!(ret1, change_base_ring(block_diagonal_matrix(Alift, transpose(Alift)^(-1)), ZZ))

  S = trafo^(-1)*S
  C = S[n+1:2*n, 1:n]
  id_GF2 = identity_matrix(GF(2), n)
  zero_GF2 = zero_matrix(GF(2), n, n)
  trafo = [id_GF2 zero_GF2 C id]
  push!(ret1, J)
  push!(ret1, change_base_ring(ZZ, [id_GF2  C zero_GF2 id_GF2]))
  push!(ret1, J)
  kappa = (-1)^n
  S = trafo^(-1)*S
  push!(ret2, change_base_ring(S, ZZ))
  return vcat(ret1, reverse(ret2)), kappa
end

function signs_in_derivative_formula(S::Matrix)
#Computes the signs on the right hand side of the generalized Jacobi derivative formula
	dec, kappa = decompose_symplectic(transpose(S))
	psi1 = 0
	psi2 = 0

	zero_block = zero_matrix(GF(2), 4,4)
	id = identity_matrix(GF(2), 4)
	J = [zero_block  id id zero_block]
	J1 = [zero_block id zero_block zero_block]

	triangle = zero_block
	for i in (1:4)
		for j in (1:4)
			triangle[i,j] = 1
		end
	end

	M = vertical_join(id, triangle)

  zero_1 = zero_matrix(GF(2), 4,1)
	zero_2 = zero_matrix(GF(2), 4,2)
	N = vcat(hcat(id, zer2), hcat(zer1, hcat(triang, zer1)))
	G = (matrix(GF(2), 6, 6, [1 for i in (1:36)]) + identity_matrix(GF(2), 6))
	N2 = N*G

  for de in dec
    Si = transpose(de)
    A = Si[1:4, 1:4]
    B = Si[1:4, 5:8]
    C = Si[5:8, 1:4]
    D = Si[5:8, 5:8]
    
    Mpre = Si*M
    Npre = Si*N
    N2pre = Si*N2
    vecpre = vcat(-2*Vector([0,0,0,0],diagonal(D*transpose(C))))
    Mpre +=  transpose(matrix([vecpre for i in [1:4]]))
    Npre +=  transpose(matrix([vecpre for i in [1:6]]))
    N2pre += transpose(matrix([vecpre for i in [1:6]]))
    psi1 += trace(transpose(Mpre)*J1*Mpre)-trace(transpose(M)*J1*M)-trace(transpose(Npre)*J1*Npre)+trace(transpose(N)*J1*N)
    psi2 += trace(transpose(Mpre)*J1*Mpre)-trace(transpose(M)*J1*M)-trace(transpose(N2pre)*J1*N2pre)+trace(transpose(N2)*J1*N2)		
    M = Si*M
    N = Si*N
    N2 = Si*N2
    vec =  vcat(diagonal(B*transpose(A)), diagonal(D*transpose(C)))
    M += transpose(matrix([vec for i in (1:4)]))
    N += transpose(matrix([vec for i in (1:6)]))
    N2 += transpose(matrix([vec for i in (1:6)]))
	end
  
	carryM = M / 2
	carryN = N / 2
	carryN2 = N2 / 2	
	switch1 = (-1)^(trace(transpose(M)*J1*carryM)+trace(transpose(N)*J1*carryN))
	switch2 = (-1)^(trace(transpose(M)*J1*carryM)+trace(transpose(N2)*J1*carryN2))

  if is_divisible_by(psi1, 4)
    quo1 = psi1/4
    if is is_divisible_by(psi2, 4)
      quo2 = psi2/4
      return [kappa*(-1)^(quo1)*switch1, -kappa*(-1)^(quo2)*switch2] #TODO: Find initial signs
    end
	end
  error("Not divisible by 4")
end


function map_azygetic(azy1, azy2)
	id = identity_matrix(GF(2), 4)
  zer = zero_matrix(GF(2), 4,4)
	J = [zer id ; id zer]
	Rhs = map(GF(2),[0, 0,1])

  M1 = matrix([azy1[1]+azy1[2], azy1[1]+azy1[3], azy1[1]+azy1[2]+azy1[3]+azy1[4]])
	M1 = vcat(M1, matrix(GF(2),1, 8, solve(J*transpose(M1), Rhs)))
	K1 = kernel(J*transpose(M1))
  

  symp_gram1 = K1*J*transpose(K1)

	hyp_dec_1 = hyperbolic_splitting(symp_gram)

	hypmat1 = matrix([hyp_dec1[1][1][1], hyp_dec1[1][1][2], hyp_dec1[1][2][1], hyp_dec1[1][2][2]])
  #hypmat1 = matrix(GF(2), [[1,0,0,0], [0,0,0,1], [1,0,1,0], [0,1,1,0]])
	M1 = vcat(M1, hypmat1*K1)
	M1 = M1[[1,3,5,7,2,4,6,8], 1:8]

	M2 = matrix([azy2[1]+azy2[2], azy2[1]+azy2[3], azy2[1]+azy2[2]+azy2[3]+azy2[4]])
	M2 = vcat(M2, matrix(GF(2),1, 8, solve(J*transpose(M2), Rhs)))
	K2 = kernel(J*transpose(M2))

	symp_gram2 = K2*J*transpose(K2)
	hyp_dec_2 = hyperbolic_splitting(symp_gram2)
	hypmat2 = matrix([hyp_dec2[1][1][1], hyp_dec2[1][1][2], hyp_dec2[1][2][1], hyp_dec2[1][2][2]])
	M2 = vcat(M2, hypmat2*K2)
	M2 = M2[[1,3,5,7,2,4,6,8], 1:8]

	S=M1^(-1)*M2
	@req !any([(matrix(azy1)*S-matrix(azy2))[1] != (matrix(azy1)*S-matrix(azy2))[i] for i in (2:4)]) "First symplectic transformation is wrong"

	vec1 = (matrix(azy1)*M1^(-1))[1,:]
	vec2 = (matrix(azy2)*M2^(-1))[1,:]

  A1, B1, C1, D1 = _split_in_blocks(transpose(M1^(-1)))
  A2, B2, C2, D2 = _split_in_blocks(transpose(M2^(-1)))


	vec1 += Vector(Diagonal(B1*Transpose(A1)) cat Diagonal(D1*Transpose(C1)))
	vec2 += Vector(Diagonal(B2*Transpose(A2)) cat Diagonal(D2*Transpose(C2)))
	trans= vec1+vec2

	S1add1at3 = Add1at2(vec1)
  S2add1at3 = Add1at2(vec2)

	vec1 = vec1*S1add1at3
  vec2 = vec2*S2add1at3
	error if vec1[2] eq 0, "Mistake in function Add1at2()"
        error if vec2[2] eq 0, "Mistake in function Add1at2()"
	ortho1 = map_orthogonal(vec1)
  ortho2 = map_orthogonal(vec2)

	vec1=vec1*Ortho1
	vec2=vec2*Ortho2

  A1, B1, C1, D1 = _split_in_blocks(transpose(ortho1))
  A2, B2, C2, D2 = _split_in_blocks(transpose(ortho2))

	vec1 += Vector(Diagonal(B1*Transpose(A1)) cat Diagonal(D1*Transpose(C1)))
        vec2+= Vector(Diagonal(B2*Transpose(A2)) cat Diagonal(D2*Transpose(C2)))
   @req vec1 == vec2 "Mistake in map_orthogonal()"
	return transpose(M1^(-1)*S1add1at3* ortho1*ortho2^(-1) *S2add1at3^(-1)*M2)
end




function signs_from_relations(g::Int, thetas::Dict{NTuple{N, Int64}, AcbFieldElem}, rho::Vector{QQFieldElem}, sigma::Vector{QQFieldElem}) where N
  @req g >= 4 "g needs to be bigger than 3."
  a = aronhold_system(g)
  #a = aronhold_system(g, azygetic_system_flip(g))
  a = [QQ.(lift.(Ref(ZZ), av))/2 for av in a]
  a0 = sum(a)

  l = Vector{QQFieldElem}[]
  for p in (1:g-3)
    push!(l, a[2*p+6] + a[2*p+7])
  end

  lambda = Vector{QQFieldElem}[]
  l_M = matrix(l)
  V = Iterators.product(repeat([[QQ(0),QQ(1)]], g-3)...)
  for v in V 
    v = [v...]
    push!(lambda, v * l_M)
  end

  A = Vector{QQFieldElem}[]

  for lam in lambda
    for ai in [[a0] ; a[1:7]]
      push!(A, lam+ai)
    end
  end

  L = sum(a[i] for i in (8:2:2*g))
  if mod(g, 2) == 1
    L += a0
  end

  CC = parent(thetas[zeros(Int, 2*g)...])
  R, X = polynomial_ring(CC, 2^(2*g))


  D = thetas

  theta_indices = Hecke.theta_characteristics_indices(g)
  Dv = Dict([(theta_indices[i+1], X[i]) for i in (1:2^(2*g)-1)])
  Dv[zeros(Int, 2*g)...] = X[2^(2*g)]


  factor = (-1)^(half_char_inner_prod(L, a[2*g]) + half_char_inner_prod(a[2*g], L) )
    terms = zeros(CC, 2^(g-3) +2^(g-1))
    term_tup = Vector{Int}[]
    i = 1
  
    for h in (1:2^(g-3)) 
      v1 = L + lambda[h]
      v2 = v1 + rho
      v3 = v1 + sigma 
      v4 = v3 + rho
      terms[i] = factor * (-1)^(half_char_inner_prod(lambda[h], lambda[h]) + 
      half_char_inner_prod(v1 +a0 + a[2*g], v1 + a0 + a[2*g])+half_char_inner_prod(rho+sigma, v1)) * 
      mod(half_char_inner_prod(v2) - 1, 2) *
      theta_HI(D, v1) * theta_HI(D, v2) *
      theta_HI(D, v3) * theta_HI(D, v4)
      push!(term_tup, char_to_index.([v1,v2,v3,v4]))
      i+=1
    end

    for a_rho in [[a0] ; a[1:7]]
      for j in (1:2^(g-4))
        v1 = L + lambda[j] + a_rho + a[2*g]
        v2 = v1 + rho
        v3 = v1 + sigma 
        v4 = v3 + rho
        terms[i] = - (-1)^((half_char_inner_prod(lambda[j] + a_rho, L)  + half_char_inner_prod(L, lambda[j] +a_rho) + half_char_inner_prod(rho + sigma, v1))) *
        mod(half_char_inner_prod(v2) - 1, 2) * 
        theta_HI(D, v1) * theta_HI(D, v2) *
        theta_HI(D, v3) * theta_HI(D, v4)
        push!(term_tup, char_to_index.([v1,v2,v3,v4]))
        i+=1
      end
    end

  sol = integral_left_kernel(matrix(terms))[1][end,:]
  result = filter(x->x[2]!=0, collect(zip(term_tup, sol)))
  if length(result) == g
    return true, result 
  else 
    return false, [(Vector{Int64}[],ZZ(0))]
  end
end
