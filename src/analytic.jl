import Base: ceil, log, -, <, <=, vcat, sum, ^, &, +, /

#= source: https://cr.yp.to/bib/1996/bach-semismooth.pdf

  idea is that
  n = prod n_i
  and n_1>= n_2 >= ...
  Psi(x, B) = #{ 0<n<x | n is B-smooth} = #{ n | n_1<= B}
  Psi(x, A, B) = # {0<n<x | n_1 <= A, n_2 <= B}

  then

  Psi(x, x^1/u) = x*dickman_rho(u)
  Psi(x, x^1/u, x^1/v) = x * bach_rho(v, u)

  OK, the "=" is an approximation

  bach_rho can be used to estimate the large-prime-variant

  The explicit 55 should be linked to the actual precision desired.
  It should be enough for dickman_rho to guarantee doubles (53 bits)
  In the paper Bach used 21 for the bach_rho function

  In the values tested, the results agree with Magma (DickmanRho) and
  the paper for bach_rho

  The program is terribly inefficient in the bash_rho (bach_J) part.
  Lots of powers are computed over and over again.
=#

function rho_coeff(x::T, prec::Int = 55; all::Bool = false) where T<: Number
  a = analytic_func{T}()
  k = ceil(x)
  all_a = Vector{analytic_func{T}}()

  a.coeff = vcat([ 1-log(T(2))] ,
                [1/(i*T(2)^i) for i=1:prec])
  a.valid=(1,2)
  if all
    push!(all_a, deepcopy(a))
  end

  while k>a.valid[2]
    d = [ sum([a.coeff[j+1]/(i*(a.valid[2]+1)^(i-j)) for j=0:(i-1) ])  for i=1:prec]
    d = vcat([1/(a.valid[2]) * sum([d[j]/(j+1) for j=1:prec ])] , d)
    a.coeff = d
    a.valid = (a.valid[1]+1, a.valid[2]+1)
    if all
      push!(all_a, deepcopy(a))
    end
  end
  if all
    return all_a
  end
  return a
end

function analytic_eval(a::analytic_func{T}, b::T) where T<:Number
  s = T(0)
  for i=length(a.coeff):-1:1
    s = s*b + a.coeff[i]
  end
  return s
end

@doc raw"""
    dickman_rho(x::Number, prec::Int=55) Number

Evaluates the Dickman-$\rho$ function at $x$.
"""
function dickman_rho(x::Number, prec::Int=55)
  if x < 0
    error("argument must be positive")
  end

  if x<= 1
    return typeof(x)(1)
  end

  if x <= 2
    return 1-log(x)
  end

  k = ceil(x)
  return analytic_eval(rho_coeff(x, prec), k-x)
end

@doc raw"""
    dickman_rho(x::Number, e::AbstractUnitRange{Int}, prec::Int=55) Number[]

Evaluates the Dickman-$\rho$ function at $i*x$ for all $i\in e$.
"""
function dickman_rho(b::Number, e::AbstractUnitRange{Int}, prec::Int = 55)
  if b < 0
    error("argument must be positive")
  end

  x = b*last(e)
  k = ceil(x)
  rc = rho_coeff(x, prec, all = true)
  val = Array{typeof(b)}(undef, length(e))

  x = b*first(e)
  if x <= 1
    val[1] = one(b)
  elseif x <= 2
    val[1] = 1-log(x)
  else
    k = ceil(x)
    f = findall(x->x.valid[2] == k, rc)
    @assert length(f)==1
    val[1] = analytic_eval(rc[f[1]], k-x)
  end
  vi = 2
  for l in (first(e)+1):last(e)
    x += b
    if x <= 1
      val[vi] = one(b)
    elseif x <= 2
      val[vi] = 1-log(x)
    else
      k = ceil(x)
      f = findall(x->x.valid[2] == k, rc)
      @assert length(f)==1
      val[vi] = analytic_eval(rc[f[1]], k-x)
    end
    vi += 1
  end
  return val
end

function bach_F(x::T) where T<: Number
  return dickman_rho(1/x)
end

function bach_rho(a::T, b::T, prec = 21) where T<:Number
  if b>a || a<0 || b <0
    error("wrong values")
  end
  if a <1
    return T(1)
  end
  return dickman_rho(a, prec) + bach_J(a, b, a, prec)
end

function bach_G(a,b)
  return bach_rho(1/a, 1/b)
end

function bach_J(u::T, v::T, w::T, prec) where T <: Number
  k = ceil(w-w/u)
  function xi(t)#(t::T)
    return k-w+w/t
  end

  if xi(v) <= 1
    local A = w/v+k-w
    local B = w/u+k-w
    local C = k-w
    function H_i(u, v, w, i)#u::T, v::T, w::T, i::Int)
      return C^i*(log(u/v) + sum([(A/C)^j/j for j=1:i]) -
                             sum([(B/C)^j/j for j=1:i]))
    end
    a = rho_coeff(k*1.0, prec)
#H_i(...., 0) is zero as it is the empty sum. Lets omit this
    return sum([a.coeff[i+1] * H_i(u, v, w, i) for i=1:(length(a.coeff)-1)])
  else
#    println("recurse: k = ", Int(k))
    return bach_J(w/(w-k+1), v, w, prec) + bach_J(u, w/(w-k+1), w, prec)
  end
end

#the function Ei = -integral(-x, infty, exp(-t)/t dt)

@doc raw"""
    exponential_integral(x::AbstractFloat) -> AbstractFloat

Compute the exponential integral function.
"""
function exponential_integral(x::BigFloat)
  z = BigFloat()
  ccall((:mpfr_eint, :libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Int32), z, x, __get_rounding_mode())
  return z
end

function exponential_integral(x::T) where T<:AbstractFloat
  return T(exponential_integral(BigFloat(x)))
end

#the function li = integral(0, x, dt/log(t))
#             li(x) = Ei(log(x)) according to wiki and ?
@doc raw"""
    logarithmic_integral(x::AbstractFloat) AbstractFloat
    li(x::AbstractFloat) AbstractFloat

Compute the logarithmic integral function. Used as an approximation
for the number of primes up to $x$.
"""
function logarithmic_integral(x::AbstractFloat)
  return exponential_integral(log(x))
end

# They are already in Nemo/arb ?!?!
#const ei = exponential_integral
#const li = logarithmic_integral


#=
From Feller:An Introduction to Probability Theory and Its Applications vol1
Chapter IX, Question 18
The formula (for n=365) is in the solutions.
=#

@doc raw"""
    rels_from_partial(n::Int, k::Int) -> Int

Estimates the number of collisions in $k$ samples among $n$ possibilities. Used
to estimate the number of full relations to be expected from $k$ partial
relations involving $n$ (large) primes.
"""
function rels_from_partial(n::Int, k::Int)
  N = ZZRingElem(n)
  return Int(round(N*(1-(N-1)^k//N^k-k*(N-1)^(k-1)//N^k)))
end


#=
Let p_i,j = 1 if the i-th and j-th person have the same birthday and 0
otherwise.
We need
  W = E(sum p_i,j)
the expectation of the sum, how many birthdays are common.
Then
  lambda = k(k-1)/(2n)
  the expectation is lambda as this should be Poisson distributed
  P(W=x) = exp(-l)l^x/x!
=#

#= computes (hopefully) the
  vol(prod x_i <= b meet [0,1]^n)
an easy exercise in induction...
  vol = b(sum_0^{n-1} (-1)^k/k! log(b)^k)
     b exp(log(1/b)) = 1 very rapidly for n-> infty
=#
function vol(n::Int, b::T) where T<:Number
  lb = log(b)
  s = [T(1)]
  t = T(1)
  for k = 1:n-1
    t  = -t/T(k) * lb
    push!(s, t)
  end
  return b*sum(s)
end

@doc raw"""
    psi_guess(x::Number, B::Int) Number

Uses the dickman_rho function to estimate $\psi(x, B)$ the number
of $B$-smooth integers bounded by $x$.
"""
function psi_guess(x::Number, B::Int)
  return x*dickman_rho(log(x)/log(B))
end

@doc raw"""
    psi_guess(x::Number, e::AbstractUnitRange, B::Int) Number

Uses the dickman_rho function to estimate $\psi(x^i, B)$ the number
of $B$-smooth integers bounded by $x^i$ for $i \in e$.
"""
function psi_guess(x::Number, B::Int, e::AbstractUnitRange)
  val = typeof(x)[x^first(e)]
  for i=(first(e) + 1):last(e)
    push!(val, val[end]*x)
  end
  d = dickman_rho(log(x)/log(B), e)
  @assert length(val) == length(d)
  return typeof(x)[d[i]*val[i] for i = 1:length(e)]
end


function class_group_expected(O::AbsSimpleNumFieldOrder, B::Integer, samples::Int = 100)
  d = isqrt(abs(discriminant(O)))
  return class_group_expected(d, degree(O), Int(B), samples)
end

function class_group_expected(O::AbsSimpleNumFieldOrder, B::ZZRingElem, samples::Int = 100)
  d = isqrt(abs(discriminant(O)))
  return class_group_expected(d, degree(O), Int(B), samples)
end

function class_group_expected(c::ClassGrpCtx, samples::Int = 100)
  id = c.FB.ideals
  O = order(id[1])
  B = norm(id[1])
  return class_group_expected(O, B, samples)
end

function class_group_expected(d::ZZRingElem, deg::Int, B::Int, samples::Int = 100)
  #d is the norm of elements we can sample, typically, sqrt(disc)
  #B is the factor base bound
  #we want
  # 1/sum (delta(psi)/delta(x)) * delta(vol)

  d = max(d, ZZRingElem(100))
  d1 = BigFloat(d)

  pg = psi_guess(d1^(1/samples), B, 1:samples)
  x = log(d1)/samples
  xi = [ exp(i*x) for i=1:samples]
  vo = [vol(deg, exp(i*x)/d1) for i=1:samples]
  @assert length(pg) == samples
  @assert length(xi) == samples
  @assert length(vo) == samples
  c = ceil(1/sum([(pg[i+1]-pg[i])/(xi[i+1]-xi[i])*(vo[i+1]-vo[i]) for i=1:(samples-1)]))
  if c > 2^60
    @warn "Computation is unlikely to finish, the success probability is 1 in $c"
    return 2^60
  else
    Int(c)
  end
end

#= D is supposed to be the discriminant
   n the dimension
   B1 the bound for the factor base
   B2 the bound for the large primes
   steps the number of steps in the integration

Computes s.th. like
  sum (vol(l^i) - vol(l^-1)) rho(

The idea is that we basically generate elements of small, bounded, T2 norm
in the number field. The naive estimate (Arithmetic-geometric) shows that
we expect a norm <= sqrt(D).
But frequently this is smaller.
We re-scalee the fundamental epiped to be [0,1]^n and assume the
norm is still prod x_i (which is "true" for totally real and need
though otherwise). The we try to count elements of norm <= l^i
for l^i = 1..sqrt D by assuming the proportion is thus the volume
of above.
The dickman_rho or bach_rho functions are then used to estimate the
number of smooth elements among those.

Idea due to Steve Donnelly

experimentally: this might be true, but it depends very much on the sampling
tool:
  for a (fixed) (lll) basis of max real 512 and lin. comb of
  n elements with coeff. in 0,1
  the norms are (roughly) normally distributed with the centre
  less than (2*sqrt(n))^128
  I assume that comes in part from the distribution of the
  conjugates themselves. They are bounded by 2, but the mean is less...

  The norm is the product of the conjugates. If the conjugates are reasonably
  distributed then the central limit theorem should imply that the norms
  are normally distributed.

  Steve's idea is (probably) correct if one samples in the entire lattice,
  represented by taking few elements of a basis and then changing the basis
=#

function expected_yield(D::ZZRingElem, n::Int, B1::Integer, B2::Integer=0, steps::Int=20)
  lD = log(abs(D))/2
  l = lD/steps

  lB1 = log(B1)
  if B2 != 1
    lB2 = log(B2)
  end

  v_l1 = 0
  yield = 0
  s = []
  for i=1:steps
    v_l = vol(n, exp(i*l-lD))
    b = i*l/lB1
    if b<1
      b = typeof(b)(1)
    end
    if b > 15
      println(" argument to dickmann too largee to make sense")
      break
    end
    if B2 == 0
     #elts have norm <= exp(i*l)
      r = dickman_rho(b)
    else
      b2 = i*l/lB2
      if b2<1
        b2 = typeof(b)(1)
      end
#      println("Calling bach with", Float64(b), " and ", Float64(b2))
      r = bach_rho(b, b2)
    end

    push!(s, (v_l-v_l1)*r)
    v_l1 = v_l
  end
  @show typeof(s)
  return s
end
