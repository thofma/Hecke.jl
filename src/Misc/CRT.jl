import Hecke.rem!, Nemo.crt, Nemo.zero, Nemo.iszero, Nemo.isone

isone(a::Int) = (a==1)

function zero!(a::fmpz)
  ccall((:fmpz_zero, :libflint), Void, (Ptr{fmpz}, ), &a)
end

function zero(a::PolyElem)
  return zero(parent(a))
end

function rem!(a::fmpz, b::fmpz, c::fmpz)
  ccall((:fmpz_mod, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Ptr{fmpz}), &a, &b, &c)
end

function rem!(a::fmpz_mod_poly, b::fmpz_mod_poly, c::fmpz_mod_poly)
  ccall((:fmpz_mod_poly_rem, :libflint), Void, (Ptr{fmpz_mod_poly}, Ptr{fmpz_mod_poly}, Ptr{fmpz_mod_poly}), &a, &b, &c)
end

type crt_env{T}
  pr::Array{T, 1}
  id::Array{T, 1}
  tmp::Array{T, 1}
  t1::T
  t2::T
  n::Int
  function crt_env(p::Array{T, 1})
    pr = copy(p)
    id = Array{T, 1}()
    i = 1
    while 2*i <= length(pr)
      a = pr[2*i-1]
      b = pr[2*i]
      g, u, v = gcdx(a, b)
      @assert isone(g)
      push!(id, v*b , u*a )
      push!(pr, a*b)
      i += 1
    end
    r = new()
    r.pr = pr
    r.id = id

    r.tmp = Array{T, 1}()
    n = length(p)
    for i=1:div(n+1, 2)
      push!(r.tmp, zero(p[1]))
    end
    r.t1 = zero(p[1])
    r.t2 = zero(p[1])

    r.n = n
    return r
  end
end

doc"""
***
   crt_env(p::Array{T, 1}) -> crt_env{T}

> Given coprime moduli in some euclidean ring (FlintZZ, nmod_poly, 
  fmpz_mod_poly), prepare data for fast application of the chinese
  remander theorem for those moduli.
"""
function crt_env{T}(p::Array{T, 1})
  return crt_env{T}(p)
end

function show{T}(io::IO, c::crt_env{T})
  print(io, "CRT data for moduli ", c.pr[1:c.n])
end

doc"""
***
   crt{T}(a::crt_env{T}, b::Array{T}) -> T

> Given values in b and the environment prepared by crt_env, return the 
  unique (modulo the product) solution to $x \equiv b_i \bmod p_i$.
"""  
function crt{T}(a::crt_env{T}, b::Array{T})
  @assert a.n == length(b)
  bn = div(a.n, 2)
  if isodd(a.n)
    zero!(a.tmp[1])
    add!(a.tmp[1], a.tmp[1], b[end])
    off = 1
  else
    off = 0
  end

  for i=1:bn
    mul!(a.t1, b[2*i-1], a.id[2*i-1])
    mul!(a.t2, b[2*i], a.id[2*i])
    add!(a.tmp[i+off], a.t1, a.t2)
    rem!(a.tmp[i+off], a.tmp[i+off], a.pr[a.n+i])
  end

  if isodd(a.n)
    bn += 1
  end

  id_off = a.n - off
  pr_off = a.n + bn - off
#  println(a.tmp, " id_off=$id_off, pr_off=$pr_off, off=$off, bn=$bn")
  while bn>1
    if isodd(bn)
      off = 1
    else
      off = 0
    end
    bn = div(bn, 2)
    for i=1:bn
      mul!(a.t1, a.tmp[2*i-1], a.id[id_off + 2*i-1])
      mul!(a.t2, a.tmp[2*i], a.id[id_off + 2*i])
      add!(a.tmp[i + off], a.t1, a.t2)
      rem!(a.tmp[i + off], a.tmp[i + off], a.pr[pr_off+i])
    end
    if off == 1
      a.tmp[1], a.tmp[2*bn+1] = a.tmp[2*bn+1], a.tmp[1] 
    end
    id_off += 2*bn
    pr_off += bn
    bn += off
#    println(a.tmp, " id_off=$id_off, pr_off=$pr_off, off=$off, bn=$bn")
  end
  return deepcopy(a.tmp[1])
end
    
#explains the idea, but is prone to overflow.
# idea: the tree CRT ..
# given moduli p1 .. pn, we first do (p1, p2), (p2, p3), ...
# then ((p1, p2), (p3, p4)), ...
# until done.
# In every step we need the cofactors, the inverse of pi mod pj
# thus we build a parallel array id for the cofactors
# in id[2i-1], id[2i] are the cofactors for pr[2i-1], pr[2i]
# To recombine, we basically loop through the cofactors:
# use id[1], id[2] to combine b[1], b[2] AND append to b
# The product pr[1]*pr[2] was appended to pr, thus we can walk through the 
# growing list till the end
# For the optimized version, we have tmp-array to hold the CRT results
# plus t1, t2 for temporaty products.
function crt(a::crt_env{Int}, b::Array{Int, 1})
  i = a.n+1
  j = 1
  while 2*j <= length(b)
    push!(b, (b[2*j-1]*a.id[2*j-1] + b[2*j]*a.id[2*j]) % a.pr[i])
    j += 1
    i += 1
  end
  return b[end]
end

function crt_test(a::crt_env{fmpz}, b::Int)
  z = [fmpz(0) for x=1:a.n]
  for i=1:b
    b = rand(0:a.pr[end]-1)
    for j=1:a.n
      rem!(z[j], b, a.pr[j])
    end
    if b != crt(a, z)
      println("problem: $b and $z")
    end
    @assert b == crt(a, z)
  end
end

