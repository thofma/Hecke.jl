###############################################################################
#
#  Rational Point Search
#
#
#  (C) 2022 Tommy Hofmann
#  (C) 2022 Jeroen Hanselman
#
###############################################################################

#Algorithm based on ratpoints by Michael Stoll

#Things Stoll does that we (may not) have yet (or may not want):
# - Sieving a second round. After the initial sieving round
#   Stoll sieves the surviving chunks a second time using a different set of primes
# - Use gcd and Jacobi symbol routines that rely (almost) entirely on differences and
#   shifts. (Not sure if we have this already (or need this)
# - Compute the residue classes of b modulo the various sieving primes by addition of the
#   difference from the last b and then correcting by subtracting p a number of times if necessary
# - Implement most of the testing of ‘forbidden divisors’ of b using bit arrays similar to those used
#   for sieving the numerators

const _primes_for_sieve =
 [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,
 107,109,113,127,131, 137,139,149,151,157,163,167,173,179,181,191,193,197,199,
 211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,
 317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,
 439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,
 569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,
 677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,
 821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,
 947,953,967,971,977,983,991,997,1009,1013,1019,1021]

@doc raw"""
    find_points((coefficients::Vector{ZZRingElem}, bound::IntegerUnion) -> ArbField

Given a list of coefficients [a_0, a_1, ..., a_n] and a bound,
return a list of points (x, y) satisfying
y^2 = a_0 + a_1*x + ... +a_n*x^n
where writing x = a//b with gcd(a, b) = 1 the points are bounded by
max(|a|, |b|) <= bound.
"""
function find_points(coefficients::Vector{ZZRingElem}, bound::IntegerUnion, N = 2^14, P = 40, Pfirst = 30)
  # This function is table unstable, but it does not matter
  # We just assemble the values with a minimal type,
  # and it will specialize in the inner function _find_points
  if bound isa ZZRingElem && fits(Int, bound)
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

@doc raw"""
    find_points(E::EllipticCurve{QQFieldElem}, bound::IntegerUnion) -> ArbField

Given an elliptic curve E over QQ with integral coefficients and
a bound, return a list of points (x: y: 1) on the curve
where writing x = a//b with gcd(a, b) = 1 the points are bounded by
max(|a|, |b|) <= bound.
"""
function find_points(E::EllipticCurve{QQFieldElem}, bound::IntegerUnion, N = 2^14, P = 40, Pfirst = 30)
  @req is_integral_model(E) "Elliptic Curve needs to be integral"
  a1, a2, a3, a4, a6 = a_invariants(E)
  transform = false
  if a1 != 0 || a3!= 0
    b2, b4, b6 = b_invariants(E)
    coeffs = [b6, b4, b2, 4]
    transform = true
  else
    coeffs = [a6, a4, a2, 1]
  end
  coeffs = map(numerator, coeffs)
  points = _find_points(coeffs, bound, N, P, Pfirst)

  if transform
    map!(t-> transform_ys(t, a1, a3), points, points)
  else
    #Only transform point at infinity back to normal coordinates on an elliptic curve
    points[1] = (zero(QQ), one(QQ), zero(QQ))
  end
  return map(t -> E(collect(t)), points)

end


#Using transform ys is pretty inefficient. In principle one could test the x-coordinates directly on
#E as the transformation to b only affects the y coordinate. On the other hand.. the set of points will probably be pretty small, so it won't matter that much.
function transform_ys(P::Tuple{QQFieldElem, QQFieldElem, QQFieldElem}, a1::QQFieldElem, a3::QQFieldElem)
  if P[3]== 0
    return (zero(QQ), one(QQ), zero(QQ))
  end
  return (P[1], (P[2] - a1*P[1] - a3)//2, 1)
end

function _find_points(coefficients::Vector, bound::Union{Integer, ZZRingElem}, N = 2^14, P = 40, Pfirst = 30)

  #N is size of chunks in which we subdivide
  #P is the number of primes we consider for sieving
  #Pfirst is the number of optimal primes we consider

  @req coefficients[end] != 0 "Leading coefficient needs to be non-zero"

  # Cache for some BitVector operations
  C = Vector{Bool}(undef, Base.bitcache_size)

  # Cache for _findall of BitVector
  I = Vector{Int}(undef, N)

  # Maximal number of parts
  H_parts = Int(div(2*bound + 1, N))

  rest = rem(2*bound + 1, N)

  primes = _primes_for_sieve[1:P]

  # Define the polynomial because we like to evaluate it

  # First decide whether to reverse the polynomial or not

  n = length(coefficients)
  #Degree of polynomial is n - 1
  odd_degree_original = iseven(n)
  reverse_polynomial = false
  f = Hecke.Globals.Qx(coefficients)

  # If f is of odd degree and the constant term is smaller than the leading
  # coefficient. Reverse the polynomial unless it would result in the polynomial
  # being of odd degree.
  if odd_degree_original
    if coefficients[1] < coefficients[n]
      tempcoeff = coefficients
      while tempcoeff[1] == 0
        popfirst!(tempcoeff)
      end

      if isodd(length(tempcoeff)) && tempcoeff[1] < coefficients[n]
        reverse_polynomial = true
        coefficients = reverse!(tempcoeff)
      end
    end
  #If f is of even degree, reverse the polynomial if it would lead to better results
  else
    #First compute the coefficients of the reciprocal polynomial
    potential_coefficients = reverse(coefficients)
    while potential_coefficients[end] == 0
      pop!(potential_coefficients)
    end

    #If the reciprocal polynomial has odd degree we reverse
    if iseven(length(potential_coefficients))
      reverse_polynomial = true
      coefficients = potential_coefficients
    else
    #Store the leading coefficients for later comparison
      old_lead = coefficients[end]
      new_lead = potential_coefficients[end]
    end
  end

  g = Hecke.Globals.Qx(coefficients)

  n = length(coefficients)
  odd_degree = iseven(n)
  lead_coeff = coefficients[end]

  # Now first compute the primes we will use for sieving
  # We use those primes such that mod p there are few points

  # Take the Pfirst primes that are most optimal for sieving
  best_primes = Tuple{Int, QQFieldElem}[]
  exclude_denom= Int[]
  exclude_denom_new = Int[]

  for p in primes
    F = GF(p, cached = false)
    order = Hecke.order_via_exhaustive_search(map(F, coefficients))
    push!(best_primes, (p, order//p))

    if !odd_degree
      if !is_square(F(old_lead))
        push!(exclude_denom, p)
      end
      if !is_square(F(new_lead))
        push!(exclude_denom_new, p)
      end
    end
  end

  if !odd_degree
  #We are going to exclude the denominators b divided by p for which the
  #squarefree part of the leading coefficient is a non-square mod p.
  #To maximize the number of denominators we use the euler_phi function as
  #a heuristic.

  #Maybe simply compute the size of B for both potential leading coefficients?
  #This test doesn't include the effect of prime divisors of leading coefficient
    old_d = prod(exclude_denom;init = one(ZZRingElem))
    new_d = prod(exclude_denom_new;init = one(ZZRingElem))
    old_score = euler_phi(old_d)//old_d
    new_score = euler_phi(new_d)//new_d
    #The smaller the score the better
    if old_score > new_score
      reverse_polynomial = true
      coefficients = potential_coefficients

      exclude_denom = exclude_denom_new
    end
  end
  sort!(best_primes, by = last)

  primes = Int[p for (p,q) in best_primes[1:Pfirst]]

  n = length(coefficients)

  lead_coeff = coefficients[n]

  #H[m][n] contains sieving info for the residue class k-1 mod m
  H = Vector{BitVector}[]
  H_temp = BitVector[]
  H2_adic_odd = Vector{BitVector}[]
  H2_adic_even = Vector{BitVector}[]

  p_starts = Int[]
  for p in primes
    p_sieve, p_sieve_odd, p_sieve_even = prime_check_arrays_2(coefficients, p, N, C)
    push!(H2_adic_odd, p_sieve_odd)
    push!(H2_adic_even,p_sieve_even)
    push!(H, p_sieve)
    push!(H_temp, copy(p_sieve[1]))
    push!(p_starts, mod(-bound, p))
  end

  two_adic_info = mod16_check_arrays(coefficients)

  #candidates = fill(trues(N), H_parts)
  candidates = BitVector[trues(N) for i in 1:(H_parts + 1)]


  res = Tuple{QQFieldElem, QQFieldElem, QQFieldElem}[]

  #Determine the set of denumerators b

  #if the polynomial is odd we can restrict the possible denominators to the ones of the form a*b^2
  #where a is a non-square-free divisor of the leading coefficient
  if odd_degree
    BB = Int[]
    q = Hecke.squarefree_part(lead_coeff)
    d = divisors(q)
    sqrt_bound = isqrt(bound)
    for a in d
      append!(BB, (a*b^2 for b in 1:sqrt_bound))
    end
    B = collect(filter!(t -> t <= bound, BB))
  else
    #Exclude denominators divisible py p^k for which the leading coefficient is not a
    #square mod p^k. (k minimal in this way)
    for p in prime_divisors(lead_coeff)
      vp = valuation(lead_coeff, p)
      if isodd(vp)
        push!(exclude_denom, p^(vp + 1))
      else
        a = divexact(lead_coeff, p^vp)
        F = GF(p, cached = false)
        if !is_square(F(a))
          push!(exclude_denom, p^(vp + 1))
        end
      end
    end
    B = filter!(collect(1:bound)) do b
      for d in exclude_denom
        if is_divisible_by(b,d)
          return false
        end
      end

      gcdb = gcd(b, 2*lead_coeff)

      while gcdb != 1
        b = divexact(b, gcd(b, 2*lead_coeff))
        gcdb = gcd(b, 2*lead_coeff)
      end

      if jacobi_symbol(lead_coeff, b) != 1
        return false
      end

      return true
    end
  end

  neg_ints = negative_intervals(g)

  left = neg_ints[1]
  intervals = neg_ints[2]
  right = neg_ints[3]

  interval_bounds = QQFieldElem[]

  if !isempty(left)
    push!(interval_bounds, max(-bound, left[1]))
  else
    push!(interval_bounds, -bound)
  end

  for I in intervals
    push!(interval_bounds, I[1])
    push!(interval_bounds, I[2])
  end

  if !isempty(right)
    push!(interval_bounds, min(bound, right[1]))
  else
    push!(interval_bounds, bound)
  end

  #Delete any intervals that are already out of bounds
  out_of_bounds = interval_bounds[2] < -bound
  while out_of_bounds

    popfirst!(interval_bounds)
    popfirst!(interval_bounds)
    out_of_bounds = interval_bounds[2] < -bound
  end

  out_of_bounds = interval_bounds[end - 1] > bound
  while out_of_bounds

    pop!(interval_bounds)
    pop!(interval_bounds)
    out_of_bounds = interval_bounds[end - 1] < bound
  end

   #Add point(s) at infinity of desingularized projective closure
   #If the degree of f is odd we have y^2 = a(n-1)*x^(n - 1)*z + ... + a0*z^n, so (1:0:0) is a point
   if odd_degree_original
     push!(res, (one(QQFieldElem), zero(QQFieldElem), zero(QQFieldElem)))
   #If the degree of f is even we have y^2 = an*x^n + ... + a0*z^n, so (1:1:0) and (1:-1:0) are points if and only if an is a square
   elseif is_square(leading_coefficient(f))
     push!(res, (one(QQFieldElem), one(QQFieldElem), zero(QQFieldElem)))
     push!(res, (one(QQFieldElem), -one(QQFieldElem), zero(QQFieldElem)))
   end

   if reverse_polynomial
     points_with_x!(res, zero(QQFieldElem), f)
   end

  for i in (1:2:length(interval_bounds))
    _find_points_in_interval!(res, f, coefficients, primes, (H, H2_adic_even, H2_adic_odd), H_temp, two_adic_info, B, interval_bounds[i], interval_bounds[i + 1], reverse_polynomial, bound, N, candidates, C, I)
  end
  return res
end

Hecke.squarefree_part(x::Int) = Int(squarefree_part(ZZRingElem(x)))

function _find_points_in_interval!(res, f, coefficients::Vector, primes, H_triple, H_temp, two_adic_info, B, left_bound, right_bound, reverse_polynomial::Bool, bound, N, candidates, C, I)

  for b in B
    case = two_adic_info[Int(mod(b, 16))+1]

    #If there are no solutions we simply move on
    if case == 0
      continue
    else
      H = H_triple[case]
    end

    #Compute the start of the interval and the end of the interval, but make sure it is within height bounds
    start_interval = min(max(ceil(ZZRingElem, b*left_bound), -bound), bound)
    end_interval = max(min(floor(ZZRingElem, b*right_bound), bound), -bound)


    # If we only consider odd or even numerators
    if case > 1

      #Make sure starting bit corresponds to even numerator if case = 2 and odd if case = 3
      if isodd(start_interval + case)
        start_interval += 1
      end

      #Range is divided by 2 when we only consider odd or even numerators
      numerator_range = ceil(Int, (1  - start_interval + end_interval)// 2)
    else
      numerator_range = 1 + - start_interval + end_interval
    end
    H_parts = Int(div(numerator_range, N))

    rest = rem(numerator_range, N)

    for i in 1:H_parts
      fill!(candidates[i], true)
    end
    candidates[H_parts + 1] = BitVector(x <= rest for x in 1:N)

    for i in 1:length(primes)
      p = @inbounds primes[i]

      if p < N
        shift = -rem(N, p)
      else
        shift = -N
      end

      k = mod(b, p)
      if case == 1
        offset = Int(mod(start_interval, p))
      elseif case == 2
        temp =  Int(mod(start_interval, p))
        if iseven(temp)
          offset = divexact(temp, 2)
        else
          offset = div(p, 2) + 1 + div(temp, 2)
        end
      elseif case == 3
        temp =  Int(mod(start_interval, p))
        if iseven(temp)
          offset = mod(div(p, 2)  + divexact(temp, 2), p)
        else
          offset = div(temp, 2)
        end
      end
      k = mod(b, p)

      #Need to shift by 1 as H[i][k] corresponds to k-1 mod p
      p_sieve = @inbounds H[i][k + 1]
      p_sieve_temp = @inbounds H_temp[i]


      for j in 1:(H_parts + 1)
        c = candidates[j]
        # circshift!(x, y,...) is allocating for x === y
        circshift!(p_sieve_temp, p_sieve, (j - 1)*shift - offset)
        # p_sieve_temp is slightly to long, so & only up to the length of c
        _and_with_first_chunks!(c, p_sieve_temp)
        #@assert candidates[j] == c
      end
    end

    _b = ZZRingElem(b)

    #Test all points that haven't been excluded by the sieve
    #Consider all integers
    if case == 1
      for i in 1:(H_parts + 1)
        ci = candidates[i]
        cnt = count(ci)
        if cnt > 0
          I = _findall!(I, ci, cnt)
          _a = (i - 1) * N + start_interval - 1
          for j in 1:cnt
            a = _a + I[j]
            if gcd(a, b) == 1
              if reverse_polynomial
                if a != 0
                  x = QQFieldElem(b//a)
                else
                  continue
                end
              else

                x = QQFieldElem(a//b)
              end
              points_with_x!(res, x, f)
            end
          end
        end
      end
    #Consider only even integers or only odd integers
    else
      for i in 1:(H_parts + 1)
        #if candidates[i]!= falses(N)
        ci = candidates[i]
        cnt = count(ci)
        if cnt > 0
          I = _findall!(I, ci, cnt)
          _a = (i - 1) * 2 * N + start_interval
          for j in 1:cnt
            a = _a + 2*(I[j] - 1)
            if gcd(a, b) == 1
              if reverse_polynomial
                if a != 0
                  x = QQFieldElem(b//a)
                else
                  continue
                end
              else
                x = QQFieldElem(a//b)
              end
              points_with_x!(res, x, f)
            end
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
  # a contains n+1 elements : a0, ...., an
  n = length(coeff) - 1

  a = map(F, coeff)

  p_part = Vector{Vector{Bool}}(undef, p)
  p_part_odd = Vector{Vector{Bool}}(undef, p)
  p_part_even = Vector{Vector{Bool}}(undef, p)


  az = Vector{elem_type(F)}(undef, n + 1)
  _chunk = Vector{Bool}(undef, length(F))
  for t in (0:p - 1)
    z = F(t)
    zpowers = powers(z, n)
   #a[i+1] corresponds to a_i above
    for i in 0:n
      az[i + 1] = a[i + 1] * zpowers[n - i + 1]
    end

    chunk = _chunk
    #for (j, x) in enumerate(F)
    #  @inbounds chunk[j] = is_square(sum([az[i + 1]*x^i for i in (0:n)]))
    #end
    chunk = Bool[is_square(sum([az[i + 1]*x^i for i in (0:n)])) for x in F]
    chunk_odd = vcat(chunk[2:2:p], chunk[1:2:p])
    chunk_even = vcat(chunk[1:2:p], chunk[2:2:p])

    #Pad the BitArray to have chunks that are at least big enough to do a broadcasted & with
    if p<N
      p_chunks = div(N, p)
      if p_chunks == 1
        chunk = append!(copy(chunk), chunk)
        chunk_odd = append!(copy(chunk_odd), chunk_odd)
        chunk_even = append!(copy(chunk_even), chunk_even)
      else
        chunk = reduce(vcat, [chunk for tt in 1:p_chunks + 1])
        chunk_odd = reduce(vcat, [chunk_odd for tt in 1:p_chunks + 1])
        chunk_even = reduce(vcat, [chunk_even for tt in 1:p_chunks + 1])
      end
      #temp = chunk
      #l = length(temp)
      #for tt in 1:p_chunks
      #  #chunk = vcat(chunk, temp)
      #  append!(chunk, @view chunk[1:l])
      #end
    end
    p_part[t+1] = chunk
    p_part_odd[t+1] = chunk_odd
    p_part_even[t+1] = chunk_even
  end

  return p_part, p_part_odd, p_part_even
end

#Original equation y^2 = an*x^n + a_{n-1}*x^(n-1) + ... + a1*x + a0
#We take the projective closure in P^(1, 2g+2, 1) for a curve of genus g, i.e.
#If n is odd:
#y^2 = an*x^n*z + a_{n-1}*x^(n-1)*z^2 + ... + a1*x*z^(n) + a0*z^(n +1)
#If n is even:
#y^2 = an*x^n + a_{n-1}*x^(n-1)*z + ... + a1*x*z^(n - 1) + a0*z^n
function prime_check_arrays_2(coeff::Vector{<: IntegerUnion}, p::Int, N, C)

  F = Native.GF(p, cached = false)
  # a contains n+1 elements : a0, ...., an
  n = length(coeff) - 1

  a = map(F, coeff)

  p_part = Vector{BitVector}(undef, p)
  p_part_odd = Vector{BitVector}(undef, p)
  p_part_even = Vector{BitVector}(undef, p)

  temp = BitVector(undef, p)

  if p < N
    p_chunks = div(N, p)
  else
    p_chunks = 0
  end

  az = Vector{elem_type(F)}(undef, n + 1)

  collF = collect(F)

  temp = BitVector(undef, p)
  temp2 = BitVector(undef, p)
  temp3 = BitVector(undef, p)
  temp4 = Vector{Bool}(undef, p)

  # Compute the indices of the squares once and for all
  squares = zeros(Bool, p)
  for t in 0:p-1
    squares[powermod(t, 2, p) + 1] = true
  end

  # Take of the projective closure for odd n
  isoddn = Int(isodd(n)) # 0 if even, 1 if odd

  for t in (0:p - 1)
    z = collF[t + 1]

    # Precompute the z
    # compute z,...,z^{n+1} if z is even and
    #         1,...,z^n if n is even
    zpowers = _powers(z, isoddn, n)

    #a[i+1] corresponds to a_i above
    for i in 0:n
      az[i + 1] = a[i + 1] * zpowers[n - i + 1]
    end

    for i in 1:p
      temp4[i] = squares[_sum_up(az, collF[i], n).data + 1]
    end

    fill_bitarray_from_itr_cyle!(temp, temp4, length(temp), C)
    #chunk = BitVector(squares[_sum_up(az, x, n).data] for x in collF)
    temp2 = BitVector(Iterators.flatten(((temp4[i] for i in 2:2:p), (temp4[i] for i in 1:2:p))))
    temp3 = BitVector(Iterators.flatten(((temp4[i] for i in 1:2:p), (temp4[i] for i in 2:2:p))))

    #chunk_odd = BitVector(Iterators.flatt((chunk[i] for i in 2:2:p, chunk[i] for i in 1:2:p)))
    #chunk_even = BitVector(Iterators.flatt((chunk[i] for i in 1:2:p, chunk[i] for i in 2:2:p)))

    #Pad the BitArray to have chunks that are at least big enough to do a broadcasted & with
    if p < N
      # I need p_chunks + 1
      chunk = _repeated_bitvector(temp, p_chunks + 1)
      chunk_odd = _repeated_bitvector(temp2, p_chunks + 1)
      chunk_even = _repeated_bitvector(temp3, p_chunks + 1)
    else
      chunk = copy(temp)
      chunk_odd = copy(temp2)
      chunk_even = copy(temp3)
    end
    p_part[t+1] = chunk
    p_part_odd[t+1] = chunk_odd
    p_part_even[t+1] = chunk_even
  end

  return p_part, p_part_odd, p_part_even
end

function _powers(z, i::Int, n::Int)
  res = Vector{typeof(z)}(undef, n + 1)
  a = z^i
  j = 1
  res[j] = a
  while j <= n
    j += 1
    a = a * z
    res[j] = a
  end
  return res
end

@inline function _sum_up(az, x, n)
  #ss = sum([az[i + 1]*x^i for i in (0:n)])
  s = zero(parent(x))
  y = one(parent(x))
  @inbounds for i in 0:n
    s += az[i + 1] * y
    y *= x
  end
  #@assert s == ss
  return s
end

#Original equation y^2 = an*x^n + a_{n-1}*x^(n-1) + ... + a1*x + a0
#We take the projective closure in P^(1, 2g+2, 1) for a curve of genus g, i.e.
#If n is odd:
#y^2 = an*x^n*z + a_{n-1}*x^(n-1)*z^2 + ... + a1*x*z^(n) + a0*z^(n +1)
#If n is even:
#y^2 = an*x^n + a_{n-1}*x^(n-1)*z + ... + a1*x*z^(n - 1) + a0*z^n
#Return Array part_16 where part_16[i] =
#       0 if no solutions
#       1 if all possible solutions
#       2 if only even solutions
#       3 if only odd solutions
function mod16_check_arrays(coefficients::Vector{<: IntegerUnion})

  R = residue_ring(ZZ, 16)[1]
  # a contains n+1 elements : a0, ...., an
  n = length(coefficients) - 1

  a = map(R, coefficients)

  part_16 = Array{Int}(undef, 16)

  if isodd(n)
      d = 1
    else
      d = 0
    end

  # t odd
  for t in (1:2:15)
    z = R(t)

    #Projective closure

    #a[i+1] corresponds to a_i above
    chunk = BitArray(sum([a[i + 1]*x^i*z^(n - i + d) for i in (0:n)]) in map(R, [0,1,4,9]) for x in R)
    if chunk == falses(16)
      part_16[t+1] = 0
    else
      evens = [chunk[i] for i in (1:2:16)]
      odds = [chunk[i] for i in (2:2:16)]

      #Only even solutions
      if odds == falses(8)
        part_16[t+1] = 2
      #Only odd solutions
      elseif evens == falses(8)
        part_16[t+1] = 3
      else
        #All possible solutions
        part_16[t+1] = 1
      end
    end
  end

  for t in (0:2:15)
    z = R(t)
    #a[i+1] corresponds to a_i above
    chunk = BitArray(sum([a[i + 1]*x^i*z^(n - i + d) for i in (0:n)]) in map(R, [0,1,4,9]) for x in R)
    if chunk == falses(16)
      part_16[t+1] = 0
    else
      odds = [chunk[i] for i in (2:2:16)]
      #No solutions
      if odds == falses(8)
        part_16[t+1] = 0
      else
      #Only odd solutions
        part_16[t+1] = 3
      end
    end
  end
  return part_16
end

function Hecke.order_via_exhaustive_search(coeff::Array{T}) where T<:FinFieldElem
  F = parent(coeff[1])
  order = FlintZZ(0)
  for x in F
    ys = points_with_x_coordinate(coeff, x)
    order += length(ys)
  end
  return order
end

function points_with_x!(res, x::QQFieldElem, f)
  test, y = is_square_with_sqrt(evaluate(f, x))
  if test
    if y == 0
      push!(res, (x, y, one(QQFieldElem)))
    else
      push!(res, (x, y, one(QQFieldElem)), (x, -y, one(QQFieldElem)))
    end
  end
end

function points_with_x_coordinate(coeff::Array{T}, x::T) where T
  n = length(coeff) - 1
  test, y = is_square_with_sqrt(sum([coeff[i + 1]*x^i for i in (0:n)]))
  pts = []
  if test
   if y == 0
      pts = [[x, y, 1]]
    else
      pts = [[x, y, 1], [x, -y, 1]]
    end
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
function negative_intervals(f::QQPolyRingElem)
  return negative_intervals(NegativityCertificate(f))
end

mutable struct NegativityCertificate
  f::QQPolyRingElem
  is_negative::Bool
  is_positive::Bool
  is_negative_at_negative::Bool
  leftmost_negative::QQFieldElem
  is_negative_at_positive::Bool
  rightmost_negative::QQFieldElem
  intervals::Vector{Tuple{QQFieldElem, QQFieldElem}}

  function NegativityCertificate(f::QQPolyRingElem)
    z = new(f)

    z.is_negative = false
    z.is_positive = false
    z.is_negative_at_negative = false
    z.is_negative_at_positive = false

    if n_real_roots(f) == 0
      if f(0) < 0
        z.is_negative = true
        return z
      else
        z.is_positive = true
        return z
      end
    end


    rr = roots(AcbField(64, cached = false), f)
    r = sort!(map(real, filter!(isreal, rr)))

    # Let's first consider what happens between two roots
    root_intervals = Tuple{QQFieldElem, QQFieldElem}[]
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

    ints = Tuple{QQFieldElem, QQFieldElem}[]

    l = length(root_intervals)

    for i in 1:l
      if signs[i] == 0 # f(a) = 0
        if i == 1
          signs[1] = Int(numerator(sign(f(root_intervals[1][1] - 1))))
        else
          signs[i] = Int(numerator(sign(f((root_intervals[i][1] + root_intervals[i - 1][2])//2))))
        end
      end

      if signs_2[i] == 0 # f(b) = 0
        if i == l
          signs_2[l] = Int(numerator(sign(f(root_intervals[l][2] + 1))))
        else
          signs_2[i] = Int(numerator(sign(f((root_intervals[i + 1][1] + root_intervals[i][2])//2))))
        end
      end
    end

    if signs[1] == -1 #
      z.is_negative_at_negative = true
      z.leftmost_negative = root_intervals[1][1]
    elseif signs[1] == 1
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
        push!(ints, (root_intervals[i][2], root_intervals[i + 1][1]))
      end
    end
    z.intervals = ints

    return z
  end
end

function is_negative_definite(N::NegativityCertificate)
  return N.is_negative
end

function is_positive_definite(N::NegativityCertificate)
  return N.is_positive
end

function negative_intervals(N::NegativityCertificate)
  if is_negative_definite(N)
    return [zero(QQFieldElem)], Tuple{QQFieldElem, QQFieldElem}[], [zero(QQFieldElem)]
  end

  if is_positive_definite(N)
    return QQFieldElem[], Tuple{QQFieldElem, QQFieldElem}[], QQFieldElem[]
  end

  l = N.is_negative_at_negative ? [N.leftmost_negative] : QQFieldElem[]
  r = N.is_negative_at_positive ? [N.rightmost_negative] : QQFieldElem[]
  return l, N.intervals, r
end

function _get_interval(x::ArbFieldElem)
  a = ZZRingElem()
  b = ZZRingElem()
  e = ZZRingElem()

  if isinteger(x)
    fl, y = unique_integer(x)
    @assert fl
    return y//1, y//1
  end

  ccall((:arb_get_interval_fmpz_2exp, libarb), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ArbFieldElem}), a, b, e, x)
  ee = Int(e)
  @assert ee <= 0
  d = one(ZZRingElem) << -ee
  return a//d, b//d
end

# Return a collection I = [(a1, a2), ..., ]
# such that whenever x in (a1, a2) for some element of I, then f(x) < 0

################################################################################
#
#  BitVector utils
#
################################################################################

# from julia/base/bitarray.jl
# non-allocating findall function
function _findall!(I, B, nnzB)
    nnzB == 0 && return I
    nnzB == length(B) && (Base.allindices!(I, B); return I)
    Bc = B.chunks
    Bs = size(B)
    Bi = i1 = i = 1
    irest = ntuple(one, ndims(B) - 1)
    c = Bc[1]
    @inbounds while true
        while c == 0
            Bi == length(Bc) && return I
            i1 += 64
            Bi += 1
            c = Bc[Bi]
        end

        tz = trailing_zeros(c)
        c = Base._blsr(c)

        i1, irest = Base._overflowind(i1 + tz, irest, Bs)
        I[i] = Base._toind(i1, irest)
        i += 1
        i1 -= tz
    end
end

function _and_with_first_chunks!(c, cc)
  for i in 1:length(c.chunks)
    @inbounds c.chunks[i] &= cc.chunks[i]
  end
end


# Given B a BitVector, repeat itr_orig (iterator yielding Bool) to fill up
# the first n values of B
function fill_bitarray_from_itr_cyle!(B::BitArray, itr_orig, n = length(B), C = Vector{Bool}(undef, Base.bitcache_size)
)
    Bc = B.chunks
    ind = 1
    cind = 1
    ind2 = 1
    itr = Iterators.cycle(itr_orig)
    y = iterate(itr)
    while y !== nothing && ind2 <= n
        ind2 += 1
        x, st = y
        @inbounds C[ind] = x
        ind += 1
        if ind > Base.bitcache_size
            Base.dumpbitcache(Bc, cind, C)
            cind += Base.bitcache_chunks
            ind = 1
        end
        y = iterate(itr, st)
    end
    if ind > 1
        @inbounds C[ind:Base.bitcache_size] .= false
        Base.dumpbitcache(Bc, cind, C)
    end
    return B
end

function _repeated_bitvector(A::BitVector, k)
    nargs = k
    nrows = length(A) * k
    n = length(A)
    B = similar(A, nrows)
    pos = 1
    for k=1:nargs
        p1 = pos+n-1
        B[pos:p1, :] = A
        pos = p1+1
    end
    return B
end
