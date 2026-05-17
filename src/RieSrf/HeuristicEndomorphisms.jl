#Heuristic endomorphisms based on Rigorous computation of the endomorphism ring of a Jacobian
# by Edgar Costa, Nicolas Mascot, Jeroen Sijsling and John Voight.

@doc raw"""
integral_left_kernel(M::ArbMatrix) -> Vector{ZZRingElem}[]

Compute an array of vectors v in ZZ^n such that v * M = 0.
"""
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

@doc raw"""
integral_left_kernel(M::AcbMatrix) -> Vector{ZZRingElem}[]

Numerically compute an array of vectors v in ZZ^n such that 
v * (real(M), imag(M)) = 0.
"""
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

@doc raw"""
complex_structure(P::AcbMatrix) -> ArbMatrix

Compute the complex structure JP of a given period matrix P.
I.e. the matrix JP that acts like complex multiplication on the
lattice spanned by the 2g vectors <real(P), imag(P)>.
"""
function complex_structure(P::AcbMatrix)
  CC = base_ring(P)
  iP = onei(CC)*P
  P_split = vcat(real(P), imag(P))
  iP_split = vcat(real(iP), imag(iP))
  return solve(P_split, iP_split, side = :right)
end

@doc raw"""
complex_structure(P::AcbMatrix) -> ArbMatrix

Given two complex structures JP and JQ, returns the equations on homology
satisfied by a homomorphism between the two corresponding abelian varieties.
"""
function rational_homomorphism_equations(JP::ArbMatrix, JQ::ArbMatrix)

  JP_prec = precision(base_ring(JP))
  JQ_prec = precision(base_ring(JQ))

  prec = minimum([JP_prec, JQ_prec])

  RR = ArbField(prec)

  JP = change_base_ring(RR, JP)
  JQ = change_base_ring(RR, JQ)

  gP = div(number_of_rows(JP),2)
  gQ = div(number_of_rows(JQ),2)
  n = 4 * gP * gQ
#Building a formal matrix corresponding to all possible integral transformations of the lattice */
  R, vars = polynomial_ring(RR, n)
  M = matrix(R, 2 * gQ, 2 * gP, vars)
  JP = change_base_ring(R, JP)
  JQ = change_base_ring(R, JQ)

#Condition that integral transformation preserve the complex structure */
  commutator = reduce(vcat,transpose((M * JP - JQ* M)))
# Splitting previous linear equations by formal variable */
return matrix(RR,[ [coeff(c, var) for c in commutator] for var in vars ])
end


@doc raw"""
tangent_representation(R::ZZMatrix, P::AcbMatrix, Q::AcbMatrix) -> AcbMatrix

Given the homology representation R of a homomorphism between two Riemann 
surfaces with period matrices P and Q.

Return the tangent respresentation of said homomorphism, 
so that A * P = Q * R.
"""
function tangent_representation(R::ZZMatrix, P::AcbMatrix, Q::AcbMatrix)
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

@doc raw"""
tangent_representation(R::ZZMatrix, P::AcbMatrix) -> AcbMatrix

Given the homology representation R of an endomorphism of a Riemann 
surface with period matrix P.

Return the tangent respresentation A of said endomorphism, 
so that A * P = P * R.
"""
function tangent_representation(R::ZZMatrix, P::AcbMatrix)
  return tangent_representation(R, P, P)
end

@doc raw"""
homology_representation(A::AcbMatrix, P::AcbMatrix, Q::AcbMatrix) -> AcbMatrix

Given a complex tangent representation A of a homomorphism a homomorphism 
between two Riemann surfaces with period matrices P and Q.

Return the homology representation R of said homomorphism, 
so that A * P = Q * R.
"""
function homology_representation(A::AcbMatrix, P::AcbMatrix, Q::AcbMatrix)
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

@doc raw"""
homology_representation(A::AcbMatrix, P::AcbMatrix) -> AcbMatrix

Given a complex tangent representation A of an endomorphism of
a Riemann surface with period matrix P.

Return the homology representation R of said homomorphism, 
so that A * P = Q * R.
"""
function homology_representation(A::AcbMatrix, P::AcbMatrix)
  return homology_representation(A, P, P)
end

@doc raw"""
geometric_homomorphism_representation(P::AcbMatrix, Q::AcbMatrix) 
  -> Vector{(QQMatrix, AcbMatrix)}

Given two period matrices P and Q.

Return a list of generators of the homomorphism algebra. Each entry in the list
will consist of a tuple (R, A) where R is the homology representation and A is
the analytic representation given over the complex numbers.
"""
function geometric_homomorphism_representation(P::AcbMatrix, Q::AcbMatrix)
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

@doc raw"""
geometric_homomorphism_representation(P::AcbMatrix, Q::AcbMatrix) 
  -> Vector{(QQMatrix, AcbMatrix)}

Given a period matrix P.

Return a list of generators of the endomorphism algebra. Each entry in the list
will consist of a tuple (R, A) where R is the homology representation and A is
the analytic representation given over the complex numbers.
"""
function geometric_endomorphism_representation(P)
  return geometric_homomorphism_representation(P,P)
end 

@doc raw"""
geometric_homomorphism_representation_nf(P::AcbMatrix, Q::AcbMatrix, F::NumField,
v::Union{PosInf, InfPlc}, upper_bound::Int = 16)
  -> Vector{(QQMatrix, Matrix{NumFieldElem})}, 
   NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}

Given two period matrices P and Q, a base field F, and a place v
encoding the embedding of F into CC.

Return a list of generators of the homomorphism algebra. 
Each entry in the list will consist of a tuple (R, A) where 
R is the homology representation and 
A is the analytic representation. 

The function tries to recognize the smallest number field K containing the
entries of the As and returns the matrices over this number field 
if it succeeds. It will also return the inclusion of F into K.

The optional argumentsupper_bound determines the maximal degree of the possible
subextensions we should search for.
"""
function geometric_homomorphism_representation_nf(P::AcbMatrix, Q::AcbMatrix,
   F::NumField, v::Union{PosInf, InfPlc}, upper_bound::Int = 16)

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

@doc raw"""
geometric_endomorphism_representation_nf(P::AcbMatrix, Q::AcbMatrix, F::NumField,
v::Union{PosInf, InfPlc}, upper_bound::Int = 16)
  -> Vector{(QQMatrix, Matrix{NumFieldElem})}, 
   NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}

Given two period matrices P and Q, a base field F, and a place v
encoding the embedding of F into CC.

Return a list of generators of the endomorphism algebra. 
Each entry in the list will consist of a tuple (R, A) where 
R is the homology representation and 
A is the analytic representation. 

The function tries to recognize the smallest number field K containing the
entries of the As and returns the matrices over this number field 
if it succeeds. It will also return the inclusion of F into K.

The optional argument upper_bound determines the maximal degree of the possible
subextensions we should search for.
"""
function geometric_endomorphism_representation_nf(P, F, v, upper_bound = 16)
  return geometric_homomorphism_representation(P, P, F, v, upper_bound = 16)
end 
