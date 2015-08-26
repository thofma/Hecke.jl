import Base: ceil, log, -, <, <=, vcat, sum, ^, &, +, /

export dickman_rho, bach_rho, bach_G, bach_F

#= source: http://cr.yp.to/bib/1996/bach-semismooth.pdf

  idea is that
  n = prod n_i
  and n_1>= n_2 >= ...
  Psi(x, B) = #{ 0<n<x | n is B-smooth} = #{ n | n_1<= B}
  Psi(x, A, B) = # {0<n<x | n_1 <= A, n_2 <= B}

  then

  Psi(x, x^1/u) = x*dickman_rho(u)
  Psi(x, x^1/u, x^1/v) = x * bach_rho(u, v)

  OK, the "=" is an approximation

  bach_rho can be used to estimate the large-prime-variant

  The explicit 55 should be linked to the actual precision desired.
  It should be enough for dickman_rho to guarantee doubles (53 bits)
  In the paper Bach used 21 for the bash_rho function

  I have no example where the recursion (splitting of the integral)
  occurs

  In the values tested, the results agree with Magma (DickmanRho) and
  the paper for bach_rho

  The program is terribly inefficient in the bash_rho (bach_J) part.
  Lots of powers are computed over and over again.
=#

type analytic_func{T<:Number}
  coeff::Array{T, 1}
  valid::Tuple{T, T}
  function analytic_func()
    return new()
  end
end


function rho_coeff{T<: Number}(x::T)
  a = analytic_func{T}()
  k = ceil(x)
  a.coeff = vcat([ 1-log(T(2))] ,
                [1/(i*T(2)^i) for i=1:55])
  a.valid=(1,2)
  while k>a.valid[2]
    d = [ sum([a.coeff[j+1]/(i*(a.valid[2]+1)^(i-j)) for j=0:(i-1) ])  for i=1:55]
    d = vcat([1/(a.valid[2]) * sum([d[j]/(j+1) for j=1:55 ])] , d)
    a.coeff = d
    a.valid = (a.valid[1]+1, a.valid[2]+1)
  end
  return a
end

function analytic_eval{T<:Number}(a::analytic_func{T}, b::T)
  s = T(0)
  for i=length(a.coeff):-1:1
    s = s*b + a.coeff[i]
  end
  return s
end

function dickman_rho(x::Number)
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
  return analytic_eval(rho_coeff(x), k-x)
end

function bach_F{T<: Number}(x::T)
  return dickman_rho(1/x)
end

function bach_rho{T<:Number}(a::T, b::T)
  if b>a || a<0 || b <0
    error("wrong values")
  end
  return dickman_rho(a) + bach_J(a, b, a)
end

function bach_G(a,b)
  return bach_rho(1/a, 1/b)
end

function bach_J{T<:Number}(u::T, v::T, w::T)
  k = ceil(w-w/u)
  function xi(t::T)
    return k-w+w/t
  end

  if xi(v) >= 0 && xi(u) <= 1
    local A = w/v+k-w,
          B = w/u+k-w,
          C = k-w
    function H_i(u::T, v::T, w::T, i::Int)
      return C^i*(log(u/v) + sum([(A/C)^j/j for j=1:i]) -
                             sum([(B/C)^j/j for j=1:i]))
    end
    a = rho_coeff(k*1.0)
    return sum([a.coeff[i+1] * H_i(u, v, w, i) for i=0:(length(a.coeff)-1)])
  else
    println("recurse")
    return bach_J(w/(w-k+1), v, w) + bach_J(u, w/(w-k+1), w)
  end
end

