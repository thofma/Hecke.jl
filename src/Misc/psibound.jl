import Nemo.setcoeff!, Nemo.exp, Base.start, Base.next, Base.done, Nemo.lift, Hecke.lift, Nemo.rem
export start, next, done, SetPrimes, psi_lower, psi_upper

#function setcoeff!(g::fmpz_mod_rel_series, i::Int64, a::Nemo.GenRes{Nemo.fmpz})
#  setcoeff!(g, i, lift(a))
#end

function bernstein(h::Int, it::Any, Q = FlintQQ, cl = ceil, a::Int = 776)
  #use 771 and cl = floor to get decent upper bounds
  # more on the choice of 776 and 771 in Dan's paper

  #println("in bernstein with a=$a and cl(0.5) = $(cl(0.5))")
  R,t = PowerSeriesRing(Q, a*h+1, "t")

  #implements https://cr.yp.to/papers/psi.pdf
  # for smoothness for ideals, replace next_prime by the list of the norms of the prime
  # ideals
  # the sums of the coefficients of exp(g) are bounds for psi

  st = start(it) 
  p, st = next(it, st)
  g = R(0)
  tp = R(0)
  lpp = Int(cl(Float64(log(p))/log(2)*a))


  function do_single!(g::SeriesElem, pp::Int, np::Int)
    i = pp
    nu = Q(np)*Q(pp)
    while i <= a*h
      A = coeff(g, i)
      A += divexact(nu, Q(i))
      setcoeff!(g, i, A)
      i += pp 
    end
  end

  while true
    pp = lpp
    np = 0
    while pp == lpp && !done(it, st)
      np += 1
      p, st = next(it, st)
      lpp = Int(cl(Float64(log(p))/log(2)*a))
      if done(it, st)
        break
      end
    end

    if done(it, st) && pp == lpp
      np += 1
    end
    
    do_single!(g, pp, np)

    if done(it, st)
      if pp != lpp
        do_single!(g, lpp, 1)
      end
      return g
    end
  end
end

function _exp(a::fmpz_mod_rel_series)
  R = base_ring(parent(a))
  Rx,x = PolynomialRing(R)
  A = Rx()
  for i=0:length(a)-1
    setcoeff!(A, i, coeff(a, i))
  end
  E = Rx()
  ccall((:nmod_poly_exp_series, :libflint), Void, (Ptr{nmod_poly}, Ptr{nmod_poly}, Int64), &E, &A, length(a))
  r = parent(a)()
  for i=0:length(E)-1
    setcoeff!(r, i, coeff(E, i))
  end
  return r
end

immutable SetPrimes{T}
  from::T
  to::T
  mod::T # if set (i.e. >1), only primes p % mod == a are returned
  a::T
  sv::UInt
  function SetPrimes(f::T, t::T)
    r = SetPrimes(f, t, T(1), T(0))
    return r
  end
  function SetPrimes(f::T, t::T, mod::T, val::T)
    sv = UInt(1)
    p = UInt(2)
    while sv < 2^30
      if mod % p != 0
        sv *= p
      end
      p = next_prime(p, false)
    end
    if gcd(mod, val) != 1
      error("modulus and value need to be coprime")
    end  
    r = new(f, t, mod, val, sv)
    return r
  end
end

function SetPrimes{T}(f::T, t::T)
  return SetPrimes{T}(f, t)
end

function SetPrimes{T}(f::T, t::T, mod::T, val::T)
  return SetPrimes{T}(f, t, mod, val)
end

function rem(a::fmpz, b::UInt)
  return ccall((:fmpz_fdiv_ui, :libflint), UInt, (Ptr{fmpz}, UInt), &a, b)
end

function start{T<: Integer}(A::SetPrimes{T})
  curr = A.from 
  c = curr % A.mod
  if A.mod >1 && c != A.a
    curr += A.mod - c + A.a
  end
  c_U = curr % A.sv
  c_M = A.mod % A.sv
  i = UInt(0)
  while gcd(c_U +i*c_M, A.sv) != UInt(1) || !isprime(curr)
    curr += A.mod
    i += UInt(1)
  end
  return curr
end

function start(A::SetPrimes{fmpz})
  curr = A.from 
  c = curr % A.mod
  if A.mod >1 && c != A.a
    curr += A.mod - c + A.a
  end

  c_U = curr % A.sv
  c_M = A.mod % A.sv
  i = UInt(0)
  while gcd(c_U +i*c_M, A.sv) != UInt(1) || !isprime(curr)
    curr += A.mod
    i += UInt(1)
  end
  return curr
end


function next{T<: Union{Integer, fmpz}}(A::SetPrimes{T}, st::T)
  p = st
  if A.mod >1
    m = A.mod
  else
    if p==2
      st = T(3)
      return p, st
    end
    m = T(2)
  end
  st = p+m
  i = UInt(0)
  c_U = st % A.sv
  c_M = m % A.sv
  while gcd(c_U +i*c_M, A.sv) != UInt(1) || !isprime(st)
    st += m
    i += UInt(1)
  end

  return p, st
end

function done{T <: Union{Integer, fmpz}}(A::SetPrimes{T}, st::T)
  return A.to != -1 && st > A.to
end

eltype{T <: Union{Integer, fmpz}}(::SetPrimes{T}) = T

function lift(R::FmpzRelSeriesRing, f::fmpz_mod_rel_series)
  r = R()
  for i=0:length(f)-1
    setcoeff!(r, i, lift(coeff(f, i)))
  end
  return r
end

function psi_lower(N::fmpz, pr, a::Int=776, cl = ceil)
  p = fmpz(next_prime(2^60))
  n = Int(ceil(log(N)/log(2)))
#  println("precision of $n")
  f = _exp(bernstein(n, pr, ResidueRing(FlintZZ, p), cl, a))
  Rt, t = PowerSeriesRing(FlintZZ, n*a+1, "t")
  f = lift(Rt, f)
  pp = p
  while pp < N
    p = next_prime(p)
#    println("p: $p, pp: $pp N:$N")
    g = _exp(bernstein(n, pr, ResidueRing(FlintZZ, p), cl, a))
    @assert length(g) == length(f)
    for i=0:length(f)
      setcoeff!(f, i, crt(coeff(f, i), pp, lift(coeff(g, i)), p))
    end
    pp *= p
  end
  res = []
  s = 0
  j = 0
  for i=0:n
    while j <= i*a && j < length(f)
      s += coeff(f, j)
      j += 1
    end
    push!(res, s)
    if j >= length(f) break; end
  end
  return res, f  # res[i] <= psi(2^(i-1), B)
end

function psi_lower(N::fmpz, B::Int, a::Int = 776, cl = ceil)
  return psi_lower(fmpz(N), SetPrimes{Int}(2, B), a, cl)
end

function psi_lower(N::Integer, B::Int, a::Int = 776, cl = ceil)
  return psi_lower(fmpz(N), SetPrimes{Int}(2, B), a, cl)
end

function psi_upper(N::fmpz, B::Int, a::Int=771, fl = floor) 
  return psi_lower(N, SetPrimes{Int}(2, B), a, fl)
end

function psi_upper(N::Integer, B::Int, a::Int=771, fl = floor)
  return psi_lower(fmpz(N), SetPrimes{Int}(2, B), a, fl)
end

function psi_lower(N::Integer, B::Hecke.NfFactorBase, a::Int=776, cl = ceil)
  lp = sort(fmpz[norm(x) for x=B.ideals])
  return psi_lower(fmpz(N), lp, a, cl)
end

function psi_lower(N::fmpz, B::Hecke.NfFactorBase, a::Int=776, cl = ceil)
  lp = sort(fmpz[norm(x) for x=B.ideals])
  return psi_lower(N, lp, a, cl)
end

function psi_upper(N::Integer, B::Hecke.NfFactorBase, a::Int=771, cl = floor)
  lp = sort(fmpz[norm(x) for x=B.ideals])
  return psi_lower(fmpz(N), lp, a, cl)
end

function psi_upper(N::fmpz, B::Hecke.NfFactorBase, a::Int=771, cl = floor)
  lp = sort(fmpz[norm(x) for x=B.ideals])
  return psi_lower(N, lp, a, cl)
end


