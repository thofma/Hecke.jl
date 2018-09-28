module DivisorsMod

using Hecke
using Base.Iterators
using AbstractAlgebra

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
Base.IteratorSize(::Divisors) = Base.SizeUnknown()  # a lie: subsets has a length, so if unit has one
                                                    # we can use it.

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

function eulerphi_inv(n::Integer)
  return eulerphi_inv(fmpz(n))
end

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

Hecke.eulerphi(A::NfOrdIdl) = Hecke.eulerphi(factor(A))
Hecke.eulerphi(A::FacElem{NfOrdIdl}) = Hecke.eulerphi(factor(A))
function Hecke.eulerphi(A::Dict{NfOrdIdl, Int})
  return prod((norm(p)-1)*norm(p)^(k-1) for (p,k) = A)
end


end

#= for torsion units:

   [maximum([maximum(vcat([fmpz(-1)], eulerphi_inv(x))) for x = Divisors(fmpz(n))]) for n = 1:20]

=# 
