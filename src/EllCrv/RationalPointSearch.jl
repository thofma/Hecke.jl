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

  N = 2^12
  H_parts = Int(div(bound, N))
  rest = rem(bound, N)

  primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
             31, 41, 43, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131]
       
  #H[m][n] contains sieving info for the residue class k mod m
  H = Vector{BitVector}[]      
  for p in primes
    p_sieve = prime_check_arrays(coefficients, p, N)
    push!(H, p_sieve)
  end
  
  
  for b in (1:bound)
    candidates = fill(trues(N), H_parts)
    push!(candidates, BitArray(x <= rest for x = 1:N))
    for i in (1:length(primes))
      p = primes[i]
      if p < N
        shift = -rem(N, p)
      else
        shift = N
      end
    
     k = Int(mod(b, p))
     
     p_sieve = H[i][k + 1]
     
     shifter = trues(length(p_sieve))

     for j in (1:H_parts +1)
      circshift!(shifter, p_sieve, (j-1)*shift)
      candidates[j] = candidates[j] .& (shifter[1:N])

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
    chunk = BitArray(issquare(sum([a[i + 1]*x^i*z^(n - i) for i in (0:n)])) for x in F)
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
