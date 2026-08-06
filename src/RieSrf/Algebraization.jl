
@doc raw"""
  algebraize_element(a_CC::AcbFieldElem, K) -> NumFieldElem
Recognize a complex number as an element of the number field K.
"""
function algebraize_element(a_CC::AcbFieldElem, K::NumField, v::Union{PosInf, InfPlc} = infinite_places(K)[1])
  CC = parent(a_CC)
  prec = precision(CC)
  genK = gen(K)
  v = v.embedding

  degK = degree(K)
  M = [ evaluate(genK^i, v, prec) for i in (0:(degK - 1)) ]
  push!(M, -a_CC)
  M = transpose(matrix(CC,[M]))

  Ker, test_ker = integral_left_kernel(M)
  row = Ker[1,:] 
  den = row[end]

  if den != 0
    a = sum([ row[i + 1]*genK^i for i in (0:(degK - 1)) ]) //den
    if contains(a_CC, evaluate(a, v, prec))
        return a
    end
  end
  error("No element found.")
end

@doc raw"""
  approximate_minimal_polynomial(a_CC::AcbFieldElem, K::NumField, v::Union{PosInf, InfPlc}, 
  lower_bound::Int= 1, upper_bound::Int= 16, degree_divides::Int= -1) -> MPolyRingElem{NumFieldElem}

Recognize the minimal polynomial of the element a_CC in K[x] under the embedding of a_CC
into K using the specified place v.

The optional arguments lower_bound and upper_bound determine the minimal and maximal degree
we should search for. The optional argument degree_divides can be used if it is known the degree of
the minimal polynomial is divisible by a certain integer. This will speed up the computation.

"""
function approximate_minimal_polynomial(a_CC::AcbFieldElem, K::NumField, v::Union{PosInf, InfPlc}, 
  lower_bound::Int= 1, upper_bound::Int= 16, degree_divides::Int= -1)
  #nsavedrows = 2
  degK = degree(K)
  R, x = polynomial_ring(K)
  genK =  gen(K) 
  CC = parent(a_CC)
  prec = precision(CC)
  RR = ArbField(prec)

  powersgenCC = [ evaluate(genK^i, v.embedding, prec) for i in (0:(degK - 1)) ]

  poweraCCsc = 1 
  degf = 0
  MLine = [ powergenCC * poweraCCsc for powergenCC in powersgenCC ]

  while degf < upper_bound
    degf += 1
    poweraCCsc *= a_CC
    MLine = vcat(MLine,  [ powergenCC * poweraCCsc for powergenCC in powersgenCC ])
    M = transpose(matrix(CC, [MLine] ))
    test = degree_divides == -1
    if !test
      test = mod(degree_divides, degf) == 0
    end
    if test
      Ker, test_ker = integral_left_kernel(M)

      if test_ker
        row = Ker[1,:] 
        ht = maximum([ abs(c) for c in row ])
        f = sum([ sum([ row[i*degK + j + 1]*genK^j for j in (0:(degK - 1)) ]) * x^i for i in (0:degf) ])
        f /= leading_coefficient(f)
        f_CC = embed_poly(f, v, prec)

        #If this test succeeds I assume we already have the correct result. 
        if contains(f_CC(a_CC), zero(CC))
            return f
        end
      end
    end
  end
error("Failed to find minimal polynomial using LLL. Try increasing the precision.")
end


@doc raw"""
  approximate_number_field(aCCs::Vector{AcbFieldElem}, K::NumField, v::Union{PosInf, InfPlc}, 
  lower_bound::Int= 1, upper_bound::Int= 16, degree_divides::Int= -1) 
   -> NumField, Vector{NumFieldElem}, Union{PosInf, InfPlc}, NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}

Try to find the smallest field extension of K containing all the elements of a_CC in under the embedding
of the a_CC into K using the specified place v.

The optional arguments upper_bound determine the maximal degree of the possible subextensions we
we should search for. The optional argument degree_divides can be used if it is known the degree of
the minimal polynomial is divisible by a certain integer. This will speed up the computation.

The output consists of the number field L, an array of elements a of L corresponding to the input aCCs,
the corresponding new embedding such that v(a[i]) = aCCs[i] and an inclusion homomorphism h: K -> L.

"""
function approximate_number_field(aCCs::Vector{AcbFieldElem}, K::NumField, v::Union{PosInf, InfPlc},  
  upper_bound::Int= 16, degree_divides::Int= -1)
  if length(aCCs) == 0 
    return K, identity_map(K)
  end 
  L = K
  h = identity_map(K)

  tupsa = []
  for aCC in aCCs
  Lnew, tupsa, v, hnew = extend_number_field_step(L, tupsa, v, aCC, upper_bound, degree_divides)
    if Lnew != L 
      h = h*hnew
    end
    L = Lnew
  end
  return L, [ tupa[1] for tupa in tupsa ], v,  h
end

#Helper function for approximate_number_field
function extend_number_field_step(K, tupsa, v, anewCC, upper_bound=16, degree_divides =-1)
  #Determine min_poly over K
  gK = approximate_minimal_polynomial(anewCC, K, v, 1, upper_bound, degree_divides)
  
  CC = parent(anewCC)
  #Case where the min_poly has degree 1
  if degree(gK) == 1 
    anew = -coeff(gK, 0)/coeff(gK, 1)
    push!(tupsa, (anew, anewCC))
    return K, tupsa, v, identity_map(K)
  end

  L_rel, a = number_field(gK)
  L, h = absolute_simple_field(L_rel)
  hm = inv(h)

  anew = hm(a)
  f = minimal_polynomial(gen(K))
  R_L, t = polynomial_ring(L)
  f_L = sum([ hm(L_rel(coeff(f, i)))*t^i for i in (0:(degree(f))) ])
  rt_f = roots(f_L)[1]
  phi = hom(K, L, rt_f)
  v_candidates = extend(v.embedding, phi)

  for v in v_candidates
    if contains(anewCC - v(anew), zero(CC))
      newa = (anew, anewCC)
      tupsa = [ (phi(tupa[1]), tupa[2]) for tupa in tupsa ]
      push!(tupsa, newa)
      return L, tupsa, infinite_place(v), phi
    end
  end
  error("Could not extend number field.")
end