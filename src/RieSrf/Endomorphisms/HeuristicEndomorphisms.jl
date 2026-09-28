#Heuristic endomorphisms based on Rigorous computation of the endomorphism ring of a Jacobian
# by Edgar Costa, Nicolas Mascot, Jeroen Sijsling and John Voight.

@doc raw"""
integral_left_kernel(M::ArbMatrix) -> ZZMatrix, Bool

Compute an array of vectors v in ZZ^n such that v * M = 0.
"""
function integral_left_kernel(M::ArbMatrix)
  # (An adaptive variant, LLL with fewer digits first and more digits only if
  #  the result is ambiguous, was tried: LLL was not faster with fewer digits
  #  for the 64 x 64 homomorphism equations of genus 4 (8.7 s instead of 3.9
  #  s), and it missed the large kernel vectors of minimal polynomials.
  #  LLL with removal of the long vectors (lll_with_removal_transform) was
  #  not faster either: 3.1-4.1 s against 3.1 s.)
  prec = precision(base_ring(M))
  #Subtracting 2 to ensure that rounding later on works without ambiguity.
  D = floor(Int, prec*log(2)/log(10)) - 2
  n = nrows(M)
  rows = _integral_left_kernel_digits(M, D)
  isempty(rows) && return zero_matrix(ZZ, 1, n), false
  return matrix(ZZ, reduce(vcat, [permutedims(r) for r in rows])), true
end

# LLL on (I | round(10^d M)). Returns the rows of the transformation that
# vanish on M at full precision.
function _integral_left_kernel_digits(M::ArbMatrix, d::Int)
  RR = base_ring(M)
  n = nrows(M)
  m = ncols(M)
  MJ = zero_matrix(ZZ, n, m)
  Hecke.round_scale!(MJ, M, d)
  L, K = lll_with_transform(hcat(identity_matrix(ZZ, n), MJ))

  #height_bound might not be necessary, but it filters out some obvious wrong
  #matrices. Might also need fine-tuning.
  height_bound = ZZ(3)^(30 + div(d, 4))
  rows = Vector{ZZRingElem}[]
  for i in 1:n
    row = ZZRingElem[K[i, j] for j in 1:n]
    ht = maximum(abs, row)
    if ht < height_bound
      prod = matrix(RR, 1, n, row) * M
      if all(contains(c, zero(RR)) for c in prod)
        push!(rows, row)
      end
    end
  end
  return rows
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
  return integral_left_kernel(hcat(real(M), imag(M)))
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
rational_homomorphism_equations(P::AcbMatrix) -> ArbMatrix

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

  # Unknowns: the entries of a 2gQ x 2gP matrix M, row-major (M[a, b] is
  # unknown (a - 1)*2gP + b). Equations: the entries of M*JP - JQ*M, also
  # row-major. The coefficient of M[a, b] in (M*JP - JQ*M)[i, j] is
  #   delta(a, i) * JP[b, j] - delta(b, j) * JQ[i, a].
  # Row = unknown, column = equation (as the kernel is taken from the left).
  # (Filled directly instead of via a polynomial ring in 4*gP*gQ variables.)
  p = number_of_rows(JP)   # 2gP
  q = number_of_rows(JQ)   # 2gQ
  n = p * q
  E = zero_matrix(RR, n, n)
  for a in 1:q, b in 1:p
    r = (a - 1)*p + b
    for j in 1:p                       # i = a
      E[r, (a - 1)*p + j] = JP[b, j]
    end
    for i in 1:q                       # j = b
      c = (i - 1)*p + b
      E[r, c] = E[r, c] - JQ[i, a]
    end
  end
  return E
end


# The equations for the homology representations R (2gQ x 2gP, integral) of
# the homomorphisms, directly from the period matrices: A * P = Q * R for
# some complex A iff Q * R * T = 0 with T = [-P0^-1 * P1; I] (P = [P0 P1],
# P0 invertible), since then Q * R = (Q * R)[:, 1:gP] * P0^-1 * P. These are
# gQ * gP complex, i.e. 2 * gP * gQ real equations: half as many as in
# rational_homomorphism_equations (M * JP = JQ * M has rank 2 * gP * gQ as
# well, but 4 * gP * gQ equations), which makes the matrix for LLL smaller.
# Rows = unknowns R[a, b] (row-major, as there), columns = the real and the
# imaginary parts of the entries of Q * R * T.
function _homomorphism_equations(P::AcbMatrix, Q::AcbMatrix)
  gP = nrows(P)
  gQ = nrows(Q)
  CC = base_ring(P)
  RR = ArbField(precision(CC))
  T = vcat(-_solve_precond(P[:, 1:gP], P[:, gP+1:2*gP]), identity_matrix(CC, gP))   # 2gP x gP
  p = 2*gP
  q = 2*gQ
  E = zero_matrix(RR, p*q, 2*gP*gQ)
  for a in 1:q, b in 1:p
    r = (a - 1)*p + b
    for i in 1:gQ, j in 1:gP
      c = Q[i, a] * T[b, j]            # coefficient of R[a, b] in (Q R T)[i, j]
      col = 2*((i - 1)*gP + j) - 1
      E[r, col] = real(c)
      E[r, col + 1] = imag(c)
    end
  end
  # Scale every equation to entries of size <= 1 (the kernel does not change;
  # the entries of P and Q can be large, e.g. 2^70, and the equations are
  # rounded to 10^-d for LLL).
  for col in 1:ncols(E)
    mx = maximum(abs(Nemo.midpoint(E[r, col])) for r in 1:nrows(E))
    if mx > 0
      for r in 1:nrows(E)
        E[r, col] = E[r, col] / mx
      end
    end
  end
  return E
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

  # work at the common precision (P and Q may come from computations at
  # different precisions; the matrices below must have the same parent)
  if precP != precQ
    CCmin = AcbField(min(precP, precQ))
    P = change_base_ring(CCmin, P)
    Q = change_base_ring(CCmin, Q)
    precP = precQ = min(precP, precQ)
  end

  JP = complex_structure(P)
  JQ = complex_structure(Q)

  CC = base_ring(P)
  RR = base_ring(JP)

  b10_prec = floor(ZZRingElem, precP*log(2)/log(10))-2

#Determination of approximate endomorphisms by LLL
  M = _homomorphism_equations(P, Q)
  
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
  return geometric_homomorphism_representation_nf(P, P, F, v, upper_bound)
end 

################################################################################
#
#  ComplexField input (ComplexMatrix period matrices). The working precision
#  is the accuracy of the input (see _input_precision), capped by
#  precision(Balls); the analytic representations are returned as
#  ComplexMatrix.
#
################################################################################

function _endo_input(P::ComplexMatrix, Q::ComplexMatrix)
  p = min(_input_precision(P), _input_precision(Q))
  return _to_acb(P, p), _to_acb(Q, p)
end

function geometric_homomorphism_representation(P::ComplexMatrix, Q::ComplexMatrix)
  Pa, Qa = _endo_input(P, Q)
  return [(_to_complex(A), R) for (A, R) in geometric_homomorphism_representation(Pa, Qa)]
end

geometric_endomorphism_representation(P::ComplexMatrix) = geometric_homomorphism_representation(P, P)

function geometric_homomorphism_representation_nf(P::ComplexMatrix, Q::ComplexMatrix,
                                                  F::NumField, v::Union{PosInf, InfPlc},
                                                  upper_bound::Int = 16)
  Pa, Qa = _endo_input(P, Q)
  return geometric_homomorphism_representation_nf(Pa, Qa, F, v, upper_bound)
end

geometric_endomorphism_representation_nf(P::ComplexMatrix, F::NumField, v::Union{PosInf, InfPlc},
                                         upper_bound::Int = 16) =
  geometric_homomorphism_representation_nf(P, P, F, v, upper_bound)

function tangent_representation(R::ZZMatrix, P::ComplexMatrix, Q::ComplexMatrix)
  Pa, Qa = _endo_input(P, Q)
  A, s0 = tangent_representation(R, Pa, Qa)
  return _to_complex(A), s0
end

tangent_representation(R::ZZMatrix, P::ComplexMatrix) = tangent_representation(R, P, P)

function homology_representation(A::ComplexMatrix, P::ComplexMatrix, Q::ComplexMatrix)
  Pa, Qa = _endo_input(P, Q)
  return homology_representation(_to_acb(A, precision(base_ring(Pa))), Pa, Qa)
end

homology_representation(A::ComplexMatrix, P::ComplexMatrix) = homology_representation(A, P, P)
