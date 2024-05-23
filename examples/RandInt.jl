

#from https://pages.cs.wisc.edu/~cs812-1/pfrn.pdf
# SIAM J. COMPUT.
# Vol. 17, No. 2, April 1988
#HOW TO GENERATE FACTORED RANDOM NUMBERS
#ERIC BACH

module RandFacInt
using Hecke
import Nemo

import Base.*

#uses rand(1:128)/128.0 as a uniform random real in (0,1) for comparisons

*(a::BigFloat, b::QQFieldElem) = a*BigFloat(b)

function Delta(N::ZZRingElem, e::Int, p::ZZRingElem)
  #to only do the is_prime_power ONCE
  q = p^e
  return Base.log(p)/Base.log(N) * BigFloat((floor(N//q) - ceil(N//(2*q)) + 1)//N)
end

function is_pr_prime_power(q::ZZRingElem; proof::Bool = true)
  e, p = Nemo._maximal_integer_root(q)
  if proof
    return is_prime(p), e, p
  else
    return is_probable_prime(p), e, p
  end
end

function process_F(N::ZZRingElem; proof::Bool = true)
  while true
    j = rand(1:nbits(N)-1)
    q =ZZ(2)<<j + rand(1:(ZZ(2)<<j)-1)

    if q <= N
      fl, e, p = is_pr_prime_power(q; proof)
      if fl && rand(1:128) < 128*Delta(N, e, p)*BigFloat(2)^j
        return e, p
      end
    end
  end
end

function Base.log(x::Fac{ZZRingElem})
  if length(x.fac) == 1
    return Base.log(ZZ(1))
  end
  return sum(e*Base.log(p) for (p, e) = x.fac)
end

"""
    rand_fac_int(N::ZZRingElem; proof::Bool = true)

Returns a uniform-random integer in (N/2..N) in factored form, based on 
Bach's paper above.

"proof" controls if the primality of the factors is proven.
"""
function rand_fac_int(N::ZZRingElem; proof::Bool = true)
  if N < 1
    N = ZZ(1)
  end
  if N <= 10^6
    return factor(rand(max(1, div(N, 2)):N))
  end
  while true
    e, p = process_F(N; proof)
    q = p^e
    g = rand_fac_int(div(N, q); proof)
    push!(g.fac, p=>e)
    if rand(1:128) < Base.log(N//2)/Base.log(g)*128
      return g
    end
  end
end

export rand_fac_int

end #module

using .RandFacInt
export rand_fac_int




