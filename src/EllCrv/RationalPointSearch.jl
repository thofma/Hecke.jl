###############################################################################
#
#  Rational Point Search
#
#
#  (C) 2022 Jeroen Hanselman
#
###############################################################################

export find_points, negative_intervals, _find_points_greater_than, NegativityCertificate

const _primes_for_sieve =
 [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,
 107,109,113,127,131, 137,139,149,151,157,163,167,173,179,181,191,193,197,199,
 211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,
 317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,
 439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,
 569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,
 677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,
 821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,
 947,953,967,971,977,983,991,997,1009,1013,1019,1021]

function find_points(coefficients::Vector{fmpz}, bound::IntegerUnion, N = 2^14, P = 40, Pfirst = 30)
  # This function is table unstable, but it does not matter
  # We just assemble the values with a minimal type,
  # and it will specialize in the inner function _find_points
  if bound isa fmpz && fits(Int, bound)
    _bound = Int(bound)
  else
    _bound = bound
  end

  if all(x -> fits(Int, x), coefficients)
    _coefficients = Int.(coefficients)
  else
    _coefficients = coefficients
  end

  return _find_points(_coefficients, _bound, N, P, Pfirst)
end

function _find_points(coefficients::Vector, bound::Union{Integer, fmpz}, N = 2^14, P = 40, Pfirst = 30)

  #N is size of chunks in which we subdivide
  #P is the number of primes we consider for sieving
  #Pfirst is the number of optimal primes we consider
  
  

  #Number of parts
  H_parts = Int(div(2*bound + 1, N))

  rest = rem(2*bound + 1, N)

  primes = _primes_for_sieve[1:P]

  # Define the polynomial because we like to evaluate it
  f = Hecke.Globals.Qx(coefficients)

 #Take the Pfirst primes that are most optimal for sieving
  best_primes = Tuple{Int, fmpq}[]
  for p in primes
    F = GF(p, cached = false)
    order = Hecke.order_via_exhaustive_search(map(F, coefficients))
    push!(best_primes, (p, order//p))
  end

  #sort!(best_primes, by = last)

  #primes = Int[p for (p,q) in best_primes[1:Pfirst]]

  #primes = _primes_for_sieve[1:5]

  #H[m][n] contains sieving info for the residue class k-1 mod m
  H = Vector{Vector{Bool}}[]
  p_starts = Int[]
  for p in primes
    p_sieve = prime_check_arrays(coefficients, p, N)
    push!(H, p_sieve)
    push!(p_starts, mod(-bound, p))
    
  end
  #candidates = fill(trues(N), H_parts)
  candidates = Vector{Bool}[ones(Bool, N) for i in 1:H_parts]
  ce = Bool[x <= rest for x = 1:N]
  push!(candidates, copy(ce))


  #Currently only doesn't have infinity.
  res = Tuple{fmpq, fmpq}[]

  n = length(coefficients)
  #Determine the set of denumerators b

  #if the polynomial is odd we can restrict the possible denominators to the ones of the form a*b^2
  #where a is a non-square-free divisor of the leading coefficent
  if isodd(n - 1)
    BB = Int[]
    leadingcoeff = coefficients[n]
    q = Hecke.squarefree_part(leadingcoeff)
    d = divisors(q)
    sqrt_bound = isqrt(bound)
    for a in d
      append!(BB, (a*b^2 for b in 1:sqrt_bound))
    end
    B = collect(filter!(t -> t <= bound, BB))
  else
    B = collect(1:bound)
  end

  shifter = ones(Bool, N)

  shif = view(shifter, 1:N)

  neg_intervals = negative_intervals(f)

  left_bound = neg_ints[1][1]
  right_bound = neg_ints[3][1]
  
  
  if left_bound != []
    append!(res, _find_points_in_interval(coefficients, primes, H, B, left_bound, bound, N))
  end
  
  if right_bound != []
    append!(res, _find_points_greater_than(coefficients, primes, H, B, -bound, right_bound, N))
  end
  
  for I in neg_ints[2]
    append!(res, _find_points_greater_than(coefficients, primes, H, B, I[1], I[2], N))
  end
  
  #=
  for b in B
    #Initiate candidate list as chunks of BitArrays of size N with true everywhere
    #candidatesn = fill(trues(N), H_parts)
    ###Remaining part if N does not divide bound exactly
    #push!(candidatesn, BitArray(x <= rest for x = 1:N))
    #@show typeof(candidates)

    # Reset the candidates
    @inbounds for i in 1:H_parts
      fill!(candidates[i], true)
    end
    candidates[end] .= ce

    for i in 1:length(primes)
      p = @inbounds primes[i]
      if p < N
        shift = -rem(N, p)
      else
        shift = -N
      end

      offset = @inbounds p_starts[i]
      k = mod(b, p)

      #Need to shift by 1 as H[i][k] corresponds to k-1 mod p
      p_sieve = @inbounds H[i][k + 1]
      #@show p_sieve
      resize!(shifter, length(p_sieve))
      fill!(shifter, true)
      #shifter = trues(length(p_sieve))
      #@show length(p_sieve)
      #fill!(shifter, true)
      #@assert length(p_sieve) == N
      #@assert length(shifter) == length(p_sieve)


      for j in 1:(H_parts + 1)
        #Storing the shifted p_sieve into shifter is apparently faster

        circshift!(shifter, p_sieve, (j-1)*shift - offset)
        #Do a broadcasted & on the candidate list with the shifted p_sieve
        # shif is view(shifter, 1:N) aka shifter[1:N]
        @inbounds candidates[j] .&= shif
      end
    end

    _b = fmpz(b)

    #Print potential rational points
    for i in 1:length(candidates)
      #if candidates[i]!= falses(N)
      S = findall(candidates[i])
      if length(S) > 0
        _a = (i - 1) * N - bound - 1
        for s in S
          a = _a + s
          if gcd(a, b) == 1
            points_with_x!(res, coefficients, a//_b, f)
          end
        end
      end
    end
  end=#
  return res
end

Hecke.squarefree_part(x::Int) = Int(squarefree_part(fmpz(x)))

function _find_points_in_interval(coefficients::Vector, primes, H, B, left_bound::fmpq, right_bound::fmpq, N = 2^14)

  res = Tuple{fmpq, fmpq}[]
  shifter = ones(Bool, N)
  shif = view(shifter, 1:N)
  
  f = Hecke.Globals.Qx(coefficients)
  
  for b in B
    start_interval = max(ceil(fmpz, b*right_bound), -bound)
    end_interval = min(floor(fmpz, b*right_bound), bound)
    
    numerator_range = 1 + bound - start_interval
    
    H_parts = Int(div(numerator_range, N))
    
    rest = rem(numerator_range, N)
    
    candidates = Vector{Bool}[ones(Bool, N) for i in 1:H_parts]
    ce = Bool[x <= rest for x = 1:N]
    push!(candidates, copy(ce))
    
    for i in 1:length(primes)
      p = @inbounds primes[i]
      
      if p < N
        shift = -rem(N, p)
      else
        shift = -N
      end

      offset = @inbounds Int(mod(start_interval, p))
      
      k = mod(b, p)

      #Need to shift by 1 as H[i][k] corresponds to k-1 mod p
      p_sieve = @inbounds H[i][k + 1]

      resize!(shifter, length(p_sieve))
      fill!(shifter, true)

      for j in 1:(H_parts + 1)
        #Storing the shifted p_sieve into shifter is apparently faster

        circshift!(shifter, p_sieve, (j-1)*shift - offset)
        #Do a broadcasted & on the candidate list with the shifted p_sieve
        # shif is view(shifter, 1:N) aka shifter[1:N]
        @inbounds candidates[j] .&= shif
      end
    end

    _b = fmpz(b)

    #Print potential rational points
    for i in 1:length(candidates)
      #if candidates[i]!= falses(N)
      S = findall(candidates[i])
      if length(S) > 0
        _a = (i - 1) * N + start - 1
        for s in S
          a = _a + s
          if gcd(a, b) == 1
            points_with_x!(res, coefficients, a//_b, f)
          end
        end
      end
    end
  end
  return res
end

#Equation y^2 = an*x^n + a_{n-1}*x^(n-1)*z + ... + a1*x*z^(n - 1) + a0*z^n
function prime_check_arrays(coeff::Vector{<: IntegerUnion}, p::Int, N)

  F = GF(p, cached = false)
  # a contains n+1 elemts : a0, ...., an
  n = length(coeff) - 1

  a = map(F, coeff)

  p_part = Vector{Vector{Bool}}(undef, p)
  az = Vector{elem_type(F)}(undef, n + 1)
  _chunk = Vector{Bool}(undef, length(F))
  for t in (0:p - 1)
    z = F(t)
    zpowers = powers(z, n)
    #a[i+1] correponds to a_i above
    for i in 0:n
      az[i + 1] = a[i + 1] * zpowers[n - i + 1]
    end
        
    chunk = _chunk
    #for (j, x) in enumerate(F)
    #  @inbounds chunk[j] = issquare(sum([az[i + 1]*x^i for i in (0:n)]))
    #end
    chunk = Bool[issquare(sum([az[i + 1]*x^i for i in (0:n)])) for x in F]

    #Pad the BitArray to have chunks that are at least big enough to do a broadcasted & with
    if p<N
      p_chunks = div(N, p)
      if p_chunks == 1
        chunk = append!(copy(chunk), chunk)
      else
        chunk = reduce(vcat, [chunk for tt in 1:p_chunks + 1])
      end
      #temp = chunk
      #l = length(temp)
      #for tt in 1:p_chunks
      #  #chunk = vcat(chunk, temp)
      #  append!(chunk, @view chunk[1:l])
      #end
    end
    p_part[t+1] = chunk
  end

  return p_part
end

#Equation y^2 = an*x^n + a_{n-1}*x^(n-1)*z + ... + a1*x*z^(n - 1) + a0*z^n
function mod16_check_arrays(coefficients::Array{fmpz})

  R = ResidueRing(ZZ, 16)
  # a contains n+1 elemts : a0, ...., an
  n = length(coefficients) - 1

  a = map(R, coefficients)

  part_16 = Array{Int}(undef, 16)
  for t in (0:15)
    z = R(t)
    #a[i+1] correponds to a_i above
    chunk = BitArray(sum([a[i + 1]*x^i*z^(n - i) for i in (0:n)]) in map(R, [0,1,4,9]) for x in R)
    @show chunk
    if chunk == falses(16)
      part_16[t+1] = 0
    else
      evens = [chunk[i] for i in (1:2:16)]
      odds = [chunk[i] for i in (2:2:16)]
      if odds == falses(8)
        part_16[t+1] = 2
      elseif evens == falses(8)
        part_16[t+1] = 1
      else
        part_16[t+1] = 4
      end
    end

  end

  return part_16
end


#Equation y^2 = an*x^n + a_{n-1}*x^(n-1)*z + ... + a1*x*z^(n - 1) + a0*z^n
function modn_check_arrays(coefficients::Array{fmpz}, m)

  R = ResidueRing(ZZ, m)
  # a contains n+1 elemts : a0, ...., an
  n = length(coefficients) - 1

  a = map(R, coefficients)

  part_16 = Array{Int}(undef, m)
  for t in (0:m-1)
    z = R(t)
    #a[i+1] correponds to a_i above
    chunk = BitArray(sum([a[i + 1]*x^i*z^(n - i) for i in (0:n)]) in map(R, [0,1,4,9]) for x in R)
    @show chunk
    if chunk == falses(m)
      part_16[t+1] = 0
    else
      evens = [chunk[i] for i in (1:2:m)]
      odds = [chunk[i] for i in (2:2:m)]
      if odds == falses(8)
        part_16[t+1] = 2
      elseif evens == falses(8)
        part_16[t+1] = 1
      else
        part_16[t+1] = 4
      end
    end

  end

  return part_16
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

function points_with_x!(res, coeff::Vector{<: IntegerUnion}, x::fmpq, f)
  test, y = is_square_with_sqrt(evaluate(f, x))
  if test
    push!(res, (x, y), (x, -y))
  end
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

################################################################################
#
#  Intervals for negativity
#
################################################################################

# There are three return values l, i, r
# f is negative on (-oo, l[1]] if l != []
# f is negative on [j[1], j[2]] for j in i
# f is negative on [r[1], oo) if r != []
function negative_intervals(f::fmpq_poly)
  return negative_intervals(NegativityCertificate(f))
end


mutable struct NegativityCertificate
  f::fmpq_poly
  is_negative::Bool
  is_negative_at_negative::Bool
  leftmost_negative::fmpq
  is_negative_at_positive::Bool
  rightmost_negative::fmpq
  intervals::Vector{Tuple{fmpq, fmpq}}

  function NegativityCertificate(f::fmpq_poly)
    z = new(f)

    if n_real_roots(f) == 0 && f(0) < 0
      z.is_negative = true
      return z
    else
      z.is_negative = false
    end

    rr = roots(f, AcbField(64, cached = false))
    r = map(real, filter!(isreal, rr))

    # Let's first consider what happens between two roots
    root_intervals = []
    for i in 1:length(r)
      (a, b) = _get_interval(r[i])
      if i < length(r)
        @assert !contains(r[i + 1], b)
      end
      if i > 1
        @assert !contains(r[i - 1], a)
      end
      push!(root_intervals, (a, b))
    end

    signs = [Int(numerator(sign(f(a)))) for (a, b) in root_intervals]
    signs_2 = [Int(numerator(sign(f(b)))) for (a, b) in root_intervals]

    ints = Tuple{fmpq, fmpq}[]

    if signs[1] == -1 #
      z.is_negative_at_negative = true
      z.leftmost_negative = root_intervals[1][1]
    else
      z.is_negative_at_negative = false
    end

    if signs_2[end] == -1
      z.is_negative_at_positive = true
      z.rightmost_negative = root_intervals[end][2]
    else
      z.is_negative_at_positive = false
    end

    for i in 1:(length(root_intervals) - 1)
      if signs_2[i] == -1
        push!(res, (root_intervals[i][2], root_intervals[i + 1][1]))
      end
    end
    z.is_negative_at_negative
    z.intervals = ints

    return z
  end
end

function is_negative_definite(N::NegativityCertificate)
  return N.is_negative
end

function negative_intervals(N::NegativityCertificate)
  if is_negative_definite(N)
    return [zero(fmpq)], Tuple{fmpq, fmpq}[], [zero(fmpq)]
  end
  l = N.is_negative_at_negative ? [N.leftmost_negative] : fmpq[]
  r = N.is_negative_at_positive ? [N.rightmost_negative] : fmpq[]
  return l, N.intervals, r
end

function _get_interval(x::arb)
  a = fmpz()
  b = fmpz()
  e = fmpz()

  ccall((:arb_get_interval_fmpz_2exp, libarb), Nothing, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}, Ref{arb}), a, b, e, x)
  ee = Int(e)
  @assert ee <= 0
  d = one(fmpz) << -ee
  return a//d, b//d
end

# Return a collection I = [(a1, a2), ..., ]
# such that whenever x in (a1, a2) for some element of I, then f(x) < 0


