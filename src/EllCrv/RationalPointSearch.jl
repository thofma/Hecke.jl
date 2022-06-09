###############################################################################
#
#  Rational Point Search
#
#
#  (C) 2022 Jeroen Hanselman
#
###############################################################################

export find_points



function find_points(coefficients::Array{fmpz}, bound::Union{Integer, fmpz}, N = 2^14, P = 40, Pfirst = 30)

  #N is size of chunks in which we subdivide
  #P is the number of primes we consider for sieving
  #Pfirst is the number of optimal primes we consider 

  #Number of parts
  H_parts = Int(div(2*bound + 1, N))
  
  rest = rem(2*bound + 1, N)

  primes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,
 107,109,113,127,131, 137,139,149,151,157,163,167,173,179,181,191,193,197,199,
 211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,
 317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,
 439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,
 569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,
 677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,
 821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,
 947,953,967,971,977,983,991,997,1009,1013,1019,1021]
 
 primes = primes[1:P]
 
 #Take the Pfirst primes that are most optimal for sieving
 best_primes = []
 for p in primes
   F = GF(p)
   order = Hecke.order_via_exhaustive_search(map(F, coefficients))
   push!(best_primes, (p, order//p^2))
 end
 
 sort!(best_primes, by = last)
 
 primes = [p for (p,q) in best_primes[1:Pfirst]]
   
       
  #H[m][n] contains sieving info for the residue class k-1 mod m 
  H = Vector{BitVector}[]      
  p_starts = []
  for p in primes
    p_sieve = prime_check_arrays(coefficients, p, N)
    push!(H, p_sieve)
    push!(p_starts, mod(-bound, p))
  end
  #candidates = fill(trues(N), H_parts)
  candidates = [trues(N) for i in 1:H_parts]
  ce = BitArray(x <= rest for x = 1:N)
  push!(candidates, copy(ce))
  

  #Currently only doesn't have infinity.
  res = Vector{fmpq}[]

  n = length(coefficients)
  #Determine the set of denumerators b
  
  B = fmpz[]
  
  #if the polynomial is odd we can restrict the possible denominators to the ones of the form a*b^2 
  #where a is a non-square-free divisor of the leading coefficent
  if isodd(n - 1)
    leadingcoeff = coefficients[n]
    q = Hecke.squarefree_part(leadingcoeff)
    d = divisors(q)
    sqrt_bound = fmpz(floor(sqrt(bound)))
    for a in d
      append!(B, [a*b^2 for b in (1:sqrt_bound)])
    end
    filter(t -> t <= bound, B) 
  else
    B = (1:bound)
  end
  
  for b in B
    #Initiate candidate list as chunks of BitArrays of size N with true everywhere
    #candidatesn = fill(trues(N), H_parts)
    ###Remaining part if N does not divide bound exactly
    #push!(candidatesn, BitArray(x <= rest for x = 1:N))
    #@show typeof(candidates)

    # Reset the candidates
    for i in 1:H_parts
      fill!(candidates[i], true)
    end
    candidates[end] = copy(ce)
    
    for i in 1:length(primes)
      p = primes[i]
      if p < N
        shift = -rem(N, p)
      else
        shift = -N
      end
      
      offset = p_starts[i]
      k = Int(mod(b, p))

      #Need to shift by 1 as H[i][k] corresponds to k-1 mod p
      p_sieve = H[i][k + 1]
      #@show p_sieve
      shifter = trues(length(p_sieve))
      fill!(shifter, true)
      #@assert length(p_sieve) == N
      #@assert length(shifter) == length(p_sieve)

      for j in 1:(H_parts +1)
        #Storing the shifted p_sieve into shifter is apparently faster

        circshift!(shifter, p_sieve, (j-1)*shift - offset)
        #Do a broadcasted & on the candidate list with the shifted p_sieve
        candidates[j] .= candidates[j] .& shifter[1:N]
      end
    end
    
    #Print potential rational points
    for i in 1:length(candidates)
      #if candidates[i]!= falses(N)
      S = findall(candidates[i])
      for s in S
        a = fmpz((i - 1)*N + s - bound - 1)
        if gcd(a, b) == 1
          append!(res, points_with_x(coefficients, a//b)) 
        end
      end
    end
  end
  return res
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
      temp = chunk
      for t in (1:p_chunks)
        chunk = vcat(chunk, temp)
      end
    end
    p_part[t+1] = chunk
  end
  
  return p_part
end

function Hecke.order_via_exhaustive_search(coeff::Array{T}) where T<:FinFieldElem
  F = parent(coeff[1])
  order = FlintZZ(0)
  for x in F
    ys = points_with_x(coeff, x)
    order += length(ys)
  end
  return order
end

function points_with_x(coeff::Array{fmpz}, x::fmpq)
  n = length(coeff) - 1
  test, y = is_square_with_sqrt(sum([coeff[i + 1]*x^i for i in (0:n)]))
  pts = []
  if test
    pts = [[x, y], [x, -y]]
  end
  return pts
end


function points_with_x(coeff::Array{T}, x::T) where T
  n = length(coeff) - 1
  test, y = is_square_with_sqrt(sum([coeff[i + 1]*x^i for i in (0:n)]))
  pts = []
  if test
    pts = [[x, y], [x, -y]]
  end
  return pts
end

