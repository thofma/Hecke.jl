###############################################################################
#
#  Rational Point Search
#
#
#  (C) 2022 Jeroen Hanselman
#
###############################################################################

export find_points



function find_points(coefficients::Array{fmpz}, bound::fmpz)

  #N is size of chunks in which we subdivide
  N = 2^12
  #Number of parts
  H_parts = Int(div(bound, N))
  rest = rem(bound, N)

  primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
             31, 41, 43, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131]
       
  #H[m][n] contains sieving info for the residue class k-1 mod m 
  H = Vector{BitVector}[]      
  for p in primes
    p_sieve = prime_check_arrays(coefficients, p, N)
    push!(H, p_sieve)
  end
  
  #For all denumerators b
  for b in (1:bound)
    #Initiate candidate list as chunks of BitArrays of size N with true everywhere
    candidates = fill(trues(N), H_parts)
    #Remaining part if N does not divide bound exactly
    push!(candidates, BitArray(x <= rest for x = 1:N))
    
    
    for i in (1:length(primes))
      p = primes[i]
      if p < N
        shift = -rem(N, p)
      else
        shift = N
      end
    
     k = Int(mod(b, p))
     
     #Need to shift by 1 as H[i][k] corresponds to k-1 mod p
     p_sieve = H[i][k + 1]
     
     shifter = trues(length(p_sieve))

     for j in (1:H_parts +1)
      #Storing the shifted p_sieve into shifter is apparently faster
      circshift!(shifter, p_sieve, (j-1)*shift)
      
      #Do a broadcasted & on the candidate list with the shifted p_sieve
      candidates[j] = candidates[j] .& (shifter[1:N])

      end
    end
    
    #Print potential rational points
    for i in (1: length(candidates))
      if candidates[i]!= falses(N)
        S = findall(candidates[i])
        for s in S
          println(((i-1)*N + s - 1)//b) 
        end
      end
    end
    
  end
  
end

#Equation y^2 = an*x^n + a_{n-1}*x^(n-1)*z + ... + a1*x*z^(n - 1) + a0*z^n
function prime_check_arrays(coeff::Array{fmpz}, p::Int, N)

  F = GF(p)
  # a contains n+1 elemts : a0, ...., an
  n = length(coeff) - 1
  
  a = map(F, coeff)
  
  p_part = Array{BitArray}(undef, p)
  for t in (0:p - 1)
    z = F(t)
    #a[i+1] correponds to a_i above
    chunk = BitArray(issquare(sum([a[i + 1]*x^i*z^(n - i) for i in (0:n)])) for x in F)
    
    #Pad the BitArray to have chunks that are at least big enough to do a broadcasted & with
    if p<N
      p_chunks = div(N, p)
      p_rest = rem(N, p)
      temp = chunk
      for t in (1:p_chunks - 1)
        chunk = vcat(chunk, temp)
      end
      
      chunk = vcat(chunk, temp[1:p_rest])
    end
    p_part[t+1] = chunk
  end
  
  return p_part
  
end
