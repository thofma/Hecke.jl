function algebraize_element(a_CC::AcbFieldElem, K)
  CC = parent(a_CC)
  prec = precision(CC)
  genK = gen(K)
  v = infinite_places(K)[1].embedding

  degK = degree(K)
  M = [ evaluate(genK^i, v, prec) for i in (0:(degK - 1)) ]
  push!(M, -a_CC)
  M = transpose(matrix(CC,[M]))

  Ker, test_ker = integral_left_kernel(M)
  row = Ker[1,:] 
  den = row[end]

  if den != 0
    a = sum([ row[i + 1]*genK^i for i in (0:(degK - 1)) ]) //den
    #Might need to check if this is the correct test
    if contains(a_CC, evaluate(a, v, prec))
        return a
    end
  end
  error("No element found.")
end


function approximate_minimal_polynomial(a_CC::AcbFieldElem, K, v, lower_bound = 1, upper_bound = 16, degree_divides = -1)
  #nsavedrows = 2
  degK = degree(K)
  R, x = polynomial_ring(K)
  genK =  gen(K) 
  CC = parent(a_CC)
  prec = precision(CC)
  RR = ArbField(prec)
  #b10_prec = floor(ZZRingElem, prec*log(2)/log(10))-2
  #height_bound = RR(ZZ(3)^(30+(div(b10_prec,4))))

  powersgenCC = [ evaluate(genK^i, v.embedding, prec) for i in (0:(degK - 1)) ]

  poweraCCsc = 1 
  degf = 0
  MLine = [ powergenCC * poweraCCsc for powergenCC in powersgenCC ]

  #savedrows = []
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

        # Test based on height bound. Not sure if this is necessary. 
        #  if ht < height_bound
        #    return f
        #  elseif length(savedrows) == n
        #    testrepeat = true
            # Test that checks if the polynomial changed after iteration. Not sure if this is necessary.
        #    for i in (1:nsavedrows)
        #      row_old = hcat(savedrows[i],[ 0 for j in (1:(nsavedrows - i + 1)*degK) ])
         #     if !(row == row_old)
         #       testrepeat = false
         #       break
         #     end
         #   end
         #   if testrepeat
         #     return f
         #   end
         # end

         # if length(savedrows) != n
         #   push!(savedrows, row)
         # else 
         #   for i in (2:nsavedrows)
         #     savedrows[i - 1] = savedrows[i]
         #   end
         #   savedrows[nsavedrows] = row
         # end
        #end
      end
    end
  end
error("Failed to find minimal polynomial using LLL. Try increasing the precision.")
end



function approximate_number_field(aCCs::Vector{AcbFieldElem}, K, v,  upper_bound = 16, degree_divides = -1)
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