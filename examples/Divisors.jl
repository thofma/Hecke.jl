module DivisorsMod

using Hecke
using Base.Iterators
using AbstractAlgebra
using Markdown

export eulerphi_inv, eulerphi_inv_fac_elem

@doc Markdown.doc"""
    Divisors{T}

An iterator for the divisors of a given object.
Create using 
    Divisors(A, power::Int = 1)
where A is either a FacElem or a direct element. Power can be used
to restrict to objects B s.th. B^power still divides A, e.g. 
    Divisors(12, powers = 2)
will produce square divisors.

For rings where this makes sense, ie. where the unit group is finite,
```units = true``` can be passed in to also take into accound
the units.
"""
mutable struct Divisors{T} 
  n::T
  lf::MSet{T}
  s#::Iterator
  f::Function
  U::GrpAbFinGen
  function Divisors(a::T; units::Bool = false, power::Int = 1) where {T}
    r = new{T}()
    r.n = a
    r.lf = MSet{T}()
    for (p, k) = factor(a).fac
      k = div(k, power)
      if k > 0 
        push!(r.lf, p, k)
      end
    end
    r.f = x -> length(x) == 0 ? one(parent(a)) : prod(x)
    r.s = Hecke.subsets(r.lf)
    if units
      U, mU = unit_group(parent(a))
      r.U = U
      g = r.f
      r.f = x->mU(x[1]) * g(x[2])
      r.s = Base.Iterators.ProductIterator((U, r.s))
    end
   return r
  end
  function Divisors(a::NfOrdIdl; units::Bool = false, power::Int = 1)
    r = new{NfOrdIdl}()
    r.n = a
    r.lf = MSet{NfOrdIdl}()
    for (p, k) = factor(a)
      k = div(k, power)
      if k > 0 
        push!(r.lf, p, k)
      end
    end
    r.f = x -> length(x) == 0 ? one(parent(a)) : prod(x)
    r.s = Hecke.subsets(r.lf)
    return r
  end
  function Divisors(a::FacElem{NfOrdIdl}; units::Bool = false, power::Int = 1)
    r = new{NfOrdIdl}()
    r.n = evaluate(a)
    r.lf = MSet{NfOrdIdl}()
    for (p, k) = factor(a)
      k = div(k, power)
      if k > 0 
        push!(r.lf, p, k)
      end
    end
    r.f = x -> length(x) == 0 ? one(parent(a)) : prod(x)
    r.s = Hecke.subsets(r.lf)
    return r
  end

  function Divisors(a::FacElem{fmpz, FlintIntegerRing}; units::Bool = false, power::Int = 1) 
    r = new{fmpz}()
    r.n = evaluate(a)
    r.lf = MSet{fmpz}()
    for (p, k) = factor(a).fac
      k = div(k, power)
      if k > 0 
        push!(r.lf, p, k)
      end
    end
    r.f = x -> length(x) == 0 ? one(parent(r.n)) : prod(x)
    r.s = Hecke.subsets(r.lf)
    if units
      U, mU = unit_group(parent(a))
      r.U = U
      g = r.f
      r.f = x->mU(x[1]) * g(x[2])
      r.s = Base.Iterators.ProductIterator((U, r.s))
    end
   return r
  end
  function Divisors(a::Fac{fmpz}; units::Bool = false, power::Int = 1)
    return Divisors(FacElem(a), units = units, power = power)
  end
end
Base.IteratorSize(::Divisors) = Base.HasLength() 
Base.length(D::Divisors) = length(D.s)                                                    

function Base.iterate(D::Divisors)
  x = iterate(D.s)
  if x == nothing
    return x
  end
  return D.f(x[1]), x[2]
end

function Base.iterate(D::Divisors, i)
  x = iterate(D.s, i)
  if x == nothing
    return x
  end
  return D.f(x[1]), x[2]
end

function Base.show(io::IO, D::Divisors)
  print(io, "Divisors of $(D.n) = $(D.lf)")
  if isdefined(D, :U)
    print(io, " times $(D.U)")
  end
  print(io, "\n")
end

@doc Markdown.doc"""
    unit_group(::FlintIntegerRing) -> GrpAbFinGen, Map

> The unit group of Z, ie. C_2 and the map translating between the group and Z.    
"""
function Hecke.unit_group(::FlintIntegerRing)
  G = Hecke.DiagonalGroup([2])
  exp = function(z::GrpAbFinGenElem)
    return isodd(z[1]) ? fmpz(-1) : fmpz(1)
  end
  log = function(z::fmpz)
    return z == -1 ? G[1] : G[0]
  end
  return G, Hecke.MapFromFunc(exp, log, G, FlintZZ)
end

@doc Markdown.doc"""
    unit_group(::Integers{T}) -> GrpAbFinGen, Map

> The unit group of , ie. C_2 and the map translating between the group and Z.    
"""
function Hecke.unit_group(R::AbstractAlgebra.Integers{T}) where {T}
  G = Hecke.DiagonalGroup([2])
  exp = function(z::GrpAbFinGenElem)
    return isodd(z[1]) ? T(-1) : T(1)
  end
  log = function(z::T)
    return z == -1 ? G[1] : G[0]
  end
  return G, Hecke.MapFromFunc(exp, log, G, R)
end

#Nemo.GaloisField = nmod?
# PolyRing

#basically from
#http://people.math.gatech.edu/~ecroot/shparlinski_final.pdf
#Contini, Croot, Shparlinski: Complexity of inverting the Euler function
@doc Markdown.doc"""
    eulerphi_inv_fac_elem(n::fmpz)
> The inverse of the Euler totient functions: find all $x$ s.th. $phi(x) = n$
> holde. The elements are returned in factored form.
"""
function eulerphi_inv_fac_elem(n::fmpz)
  lp = []
  for d = Divisors(n)
    if isprime(d+1)
      push!(lp, d+1)
    end
  end
#  println("possible primes: ", lp)

  E = []
  res = []
  for p = lp
    v = valuation(n, p)
    for i=0:v
      push!(E, ((p-1)*p^i, [(p, i+1)]))
      if E[end][1] == n
        push!(res, FacElem(Dict(E[end][2])))
      end
    end
  end
  while true
    F = []
    for e = E
      nn = divexact(n, e[1])
      x = e[2]
      pm = x[end][1]
      for p = lp
        if p <= pm
          continue
        end
        if nn % (p-1) == 0
          v = valuation(nn, p)
          for i = 0:v
            push!(F, (e[1]*(p-1)*p^i, vcat(e[2], [(p, i+1)])))
            if F[end][1] == n
              push!(res, FacElem(Dict(F[end][2])))
            end
          end
        end
      end
    end
    if length(F) == 0
      return res
    end
    E = F
  end
end

function Hecke.eulerphi(x::Fac{fmpz})
  return prod((p-1)*p^(v-1) for (p,v) = x.fac)
end

function Hecke.eulerphi(x::FacElem{fmpz, FlintIntegerRing})
  x = factor(x)
  return prod((p-1)*p^(v-1) for (p,v) = x.fac)
end

function eulerphi(n::T) where {T <: Integer}
  return T(eulerphi(fmpz(n)))
end

@doc Markdown.doc"""
    eulerphi_inv(n::Integer) -> Array{fmpz, 1}
> The inverse of the Euler totient functions: find all $x$ s.th. $phi(x) = n$
> holds.
"""
function eulerphi_inv(n::Integer)
  return eulerphi_inv(fmpz(n))
end

@doc Markdown.doc"""
    eulerphi_inv(n::fmpz) -> Array{fmpz, 1}
> The inverse of the Euler totient functions: find all $x$ s.th. $phi(x) = n$
> holds.
"""
function eulerphi_inv(n::fmpz)
  return [ evaluate(x) for x = eulerphi_inv_fac_elem(n)]
end

function Hecke.factor(a::FacElem{fmpz, FlintIntegerRing})
  b = simplify(a)
  c = Dict{fmpz, Int}()
  s = fmpz(1)
  for (p,k) = b.fac
    lp = factor(p)
    s *= lp.unit
    for (q,w) = lp.fac
      c[q] = w*k
    end
  end
  l = Fac{fmpz}()
  l.fac = c
  l.unit = s
  return l
end

function Hecke.FacElem(a::Fac{fmpz})
  f = FacElem(a.fac)
  if a.unit == -1
    return a.unit * f
  end
  return f
end

@doc Markdown.doc"""
    eulerphi(A::NfOrdIdl) -> fmpz
> The ideal verision of the totient functionm returns the size of the unit group
> of the residue ring modulo the ideal.
"""
Hecke.eulerphi(A::NfOrdIdl) = Hecke.eulerphi(factor(A))
Hecke.eulerphi(A::FacElem{NfOrdIdl}) = Hecke.eulerphi(factor(A))
function Hecke.eulerphi(A::Dict{NfOrdIdl, Int})
  return prod((norm(p)-1)*norm(p)^(k-1) for (p,k) = A if k < 0 error("ideal not integral"))
end

#same algo as above...
@doc Markdown.doc"""
    eulerphi_inv_fac_elem(n::fmpz, zk::NfAbsOrd{AnticNumberField, nf_elem})
> The inverse of the ideal totient funcction: all ideals $A$ s.th the unit group of the 
> residue ring has the required size. Here, the ideals are returned in factorisaed form.
"""
function eulerphi_inv_fac_elem(n::fmpz, zk::NfAbsOrd{AnticNumberField, nf_elem})
  lp = []
  for d = Divisors(n)
    k, p = ispower(d+1)
    if isprime(p)
      ll = prime_decomposition(zk, p)
      for P = ll
        if degree(P[1]) == k
           push!(lp, P[1])
         end
       end
    end
  end
#  println("possible primes: ", lp)

  E = []
  res = []
  for p = lp
    v = valuation(n, norm(p))
    for i=0:v
      push!(E, ((norm(p)-1)*norm(p)^i, [(p, i+1)]))
      if E[end][1] == n
        push!(res, FacElem(Dict(E[end][2])))
      end
    end
  end
  
  while true
    F = []
    for e = E
      nn = divexact(n, e[1])
      x = e[2]
      pm = x[end][1]
      start = true
      for p = lp
        start && p != pm && continue
        start = false
        p == pm && continue
        if nn % (norm(p)-1) == 0
          v = valuation(nn, norm(p))
          for i = 0:v
            push!(F, (e[1]*(norm(p)-1)*norm(p)^i, vcat(e[2], [(p, i+1)])))
            if F[end][1] == n
              push!(res, FacElem(Dict(F[end][2])))
            end
          end
        end
      end
    end
    if length(F) == 0
      return res
    end
    E = F
  end
end

@doc Markdown.doc"""
    eulerphi_inv(n::fmpz, zk::NfAbsOrd{AnticNumberField, nf_elem}) -> Array{NfOrdIdl, 1}
> The inverse of the ideal totient funcction: all ideals $A$ s.th the unit group of the 
> residue ring has the required size. 
"""
eulerphi_inv(n::fmpz, zk::NfAbsOrd) = [ numerator(evaluate(x)) for x = eulerphi_inv_fac_elem(n, zk)]
eulerphi_inv(n::Integer, zk::NfAbsOrd) = [ numerator(evaluate(x)) for x = eulerphi_inv_fac_elem(fmpz(n), zk)]

end

#= for torsion units:

   [maximum([maximum(vcat([fmpz(-1)], eulerphi_inv(x))) for x = Divisors(fmpz(n))]) for n = 1:20]

=# 
