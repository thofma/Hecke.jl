
function integral_left_kernel(M::ArbMatrix)

  RR = base_ring(M)
  prec = precision(RR)

#Subtracting 2 to ensure that rounding later on works without ambiguity.
  b10_prec = floor(Int, prec*log(2)/log(10))-2

# Endomorphisms and polarizations have far smaller coefficients, 
# so we could potentially work with lower precision
  n = nrows(M)
  MJ = zero_matrix(ZZ, n, n)
  Hecke.round_scale!(MJ, M, b10_prec)

  k = number_of_rows(M)
  MI = identity_matrix(ZZ, k)
  MJ = hcat(MI, MJ)
  L, K = lll_with_transform(MJ)
  

  #height_bound might not be necessary, but it filters out some obvious wrong
  #matrices. Might also need fine-tuning.
  height_bound = RR(ZZ(3)^(30+(div(b10_prec,4))))

  rowsK0 = Vector{ZZRingElem}[]
  for i in (1:k)
    row = K[i,:]
    ht = maximum([ abs(c) for c in row ])
    test1 = ht <  height_bound

    if test1 
        prod = matrix(RR, [ row ])*M;
        test2 = all([ contains(c, zero(RR)) for c in prod])
        if test2
            push!(rowsK0, row)
        end
    end
  end

  if length(rowsK0) == 0 
    return matrix([ [ 0 for row in (1:k) ] ]), false
  end
  return matrix(rowsK0), true
end

function integral_left_kernel(M::AcbMatrix)
  CC = base_ring(M)
  prec = precision(CC)
  RR = ArbField(prec)
  b10_prec = floor(ZZRingElem, prec*log(2)/log(10))-2
  test = all([ contains(imag(c), zero(RR)) for c in M])
  if test
    return integral_left_kernel(real(M))
  end
  return  integral_left_kernel(hcat(real(M), imag(M)))
end


function complex_structure(P)
  CC = base_ring(P)
  iP = onei(CC)*P
  P_split = vcat(real(P), imag(P))
  iP_split = vcat(real(iP), imag(iP))
  return solve(P_split, iP_split, side = :right)
end

function rational_homomorphism_equations(JP, JQ)
#Given two complex structures JP and JQ, returns the equations on homology
#satisfied by a homomorphism between the two corresponding abelian varieties.

  RR = base_ring(JP)
  gP = div(number_of_rows(JP),2)
  gQ = div(number_of_rows(JQ),2)
  n = 4 * gP * gQ
#Building a formal matrix corresponding to all possible integral transformations of the lattice */
  R, vars = polynomial_ring(RR, n)
  M = matrix(R, 2 * gQ, 2 * gP, vars)
#Condition that integral transformation preserve the complex structure */
  commutator = reduce(vcat,transpose((M * JP - JQ* M)))
# Splitting previous linear equations by formal variable */
return matrix(RR,[ [coeff(c, var) for c in commutator] for var in vars ])
end

function tangent_representation(R, P, Q)
  CC = base_ring(P)
  prec = precision(CC)
  RR = ArbField(prec)
  g = number_of_rows(P)
  #P0 is an invertible submatrix of P. We are using here that P is a period matrix.
  P0 = P[1:g, 1:g]
  s0 = (1:g)
  QR = Q * change_base_ring(CC, R)
  QR0 = QR[1:g,s0]
  A = solve(P0, QR0)
  AP_QR = reduce(vcat,transpose((A*P - Q*change_base_ring(CC, R))))
  test = all([ contains(c, zero(CC)) for c in AP_QR ])
  if !test
      error("Error in determining tangent representation")
  end
  return A, s0
end

function tangent_representation(R, P)
  return tangent_representation(R, P, P)
end

function homology_representation(A, P, Q)
#Given a complex tangent representation A of a homomorphism and two period
#matrices P and Q, returns a homology representation R of that same
#homomorphism, so that A P = Q R.
  CC = base_ring(P)
  AP = A*P
  AP_split = vcat(real(AP), imag(AP))
  Q_split = vcat(real(Q), imag(Q))
  RRR = transpose(solve(Q_split, AP_split, side = :right))
  r = number_of_rows(RRR)
  R = matrix(QQ, [ [ round(ZZRingElem, cRR) for cRR in RRR[i,:] ]  for i in (1:r) ])
  AP_QR = reduce(vcat,transpose((A*P - Q*change_base_ring(CC, R))))
  test = all([ contains(c, zero(CC)) for c in AP_QR ])
  if !test
    error("Error in determining homology representation")
  end

  return R
end

function homology_representation(A, P)
  return homology_representation(A, P, P)
end

function geometric_homomorphism_representation(P, Q)
  gP = number_of_rows(P)
  gQ = number_of_rows(Q)

  precP = precision(base_ring(P))
  precQ = precision(base_ring(Q))
  @req number_of_columns(P) == 2*gP "P should be a g x 2g matrix"
  @req number_of_columns(Q) == 2*gQ "Q should be a g x 2g matrix"

  JP = complex_structure(P)
  JQ = complex_structure(Q)

  CC = base_ring(P)
  RR = base_ring(JP)

  b10_prec = floor(ZZRingElem, precP*log(2)/log(10))-2

#Determination of approximate endomorphisms by LLL
  M = rational_homomorphism_equations(JP, JQ)
  
  Ker, test = integral_left_kernel(M)
  k = number_of_rows(Ker)

  if !test
    return []
  end

  #Deciding which rows to keep 

  gens = []

  for i in (1:k)
    row = Ker[i,:]
    R = matrix(ZZ, 2*gQ, 2*gP, row)
    R_RR = change_base_ring(RR, R)
    #Culling the correct transformations from holomorphy condition */
    commutator = reduce(vcat,transpose((R_RR * JP - JQ* R_RR)))
    if all([ contains(abs(c), zero(RR)) for c in commutator ])
      A, s0 = tangent_representation(R, P, Q)
      push!(gens, (A, R))
    end
  end
  return gens
end

function geometric_endomorphism_representation(P)
  return geometric_homomorphism_representation(P,P)
end 

function geometric_homomorphism_representation_nf(P, Q, F, v, upper_bound = 16)

  CC = base_ring(P)
  gens_part = geometric_homomorphism_representation(P,Q)
  ana_rep_part = reduce(vcat, [ reduce(vcat, gen[1]) for gen in gens_part ])
  K, seq, v, hFK = approximate_number_field(ana_rep_part, F, v, upper_bound)

  r = number_of_rows(gens_part[1][1]) 
  c = number_of_rows(transpose(gens_part[1][1]))
  As = [ matrix(K, r, c, seq[((k - 1)*r*c + 1):(k*r*c)]) for k in (1:length(gens_part))]
  gens = [ (As[k], gens_part[k][2] ) for k in (1:length(gens_part)) ]

  return gens, hFK

end

function geometric_endomorphism_representation_nf(P, F, v, upper_bound = 16)
  return geometric_homomorphism_representation(P,P, F, v, upper_bound = 16)
end 
