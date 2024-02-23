module FrancyExample

using Hecke, Francy

import Base.*
*(x::Hecke.RingElem) = x

function divisors(n::ZZRingElem)
  lf = factor(n).fac
  z = Base.Iterators.ProductIterator(Tuple([[p^i for i=0:k] for (p,k) = lf]))
  l = ZZRingElem[]
  for x = z
    push!(l, prod(x))
  end
  return l
end

function graphic_divisors(n::ZZRingElem)
  c = canvas("Divisors of $n")
  I = Francy.id(c)
  d = divisors(n)
  no = [node(string(d[i])) for i=1:length(d)]
  for n = 1:length(no)
    push!(no[n], menu("Prime?", callback("FrancyExample.is_prime", "(:" * I * ", $(d[n]))")))
    push!(no[n], menu("Odd?", callback("FrancyExample.isodd", "(:" * I * ", $(d[n]))")))
  end
  g = graph()
  for n = no
    push!(g, n)
  end
  for i=1:length(d)
    for j=1:length(d)
      if i==j
        continue
      end
      if divides(d[i], d[j])[1]
        push!(g, link(no[i], no[j], length = div(d[j], d[i])))
      end
    end
  end
  push!(c, g)
  return c
end

function is_prime(t::Tuple)
  n = ZZRingElem(t[2])
  f = Hecke.is_prime(n)
  c = canvas(t[1])
  push!(c, message("$n is prime: $f"))
  display(Francy.FrancyMimeString, c)
  return true
end

function isodd(t::Tuple)
  n = ZZRingElem(t[2])
  f = Hecke.isodd(n)
  c = canvas(t[1])
  push!(c, message("$n is odd $f"))
  display(Francy.FrancyMimeString, c)
  return true
end

export graphic_divisors

function graphic_subgroups(A::FinGenAbGroup)
  s = collect(subgroups(A))
  g = graph()
  n = [node("$i: $(length(s[i][1]))") for i = 1:length(s)]
  for x = n
    push!(g, x)
  end
  for i=1:length(s)
    for j=i+1:length(s)
      if is_subgroup(s[i][1], s[j][1])[1]
        push!(g, link(n[i], n[j]))
      end
    end
  end
  c = canvas("subgroups")
  push!(c, g)
  return c
end

end

using Main.FrancyExample

#=
Hecke.example("Francy.jl")

graphic_divisors(ZZRingElem(12))

=#

