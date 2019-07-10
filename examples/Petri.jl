module PetriNet

using Hecke, Francy

mutable struct Data
  name::Symbol
  data::Dict{Symbol, Any}
  id::Symbol
  function Data(n::Symbol)
    r = new()
    r.name = n
    r.data = Dict{Symbol, Any}()
    return r
  end
  function Data(n::Symbol, d::Pair{Symbol, <:Any}...)
    r = new()
    r.name = n
    r.data = Dict(d...)
    return r
  end
end

mutable struct Transition
  name::Symbol
  action::Array{Function, 1}
  possible::Array{Function, 1}
  id::Symbol
  In::Array{Symbol, 1}
  Out::Array{Symbol, 1}
  Read::Array{Symbol, 1}
  function Transition(n::Symbol)
    r = new()
    r.name = n
    return r
  end
end

mutable struct Petri
  d::Dict{Symbol, Data}
  t::Dict{Symbol, Transition}
  change::Set{Symbol}
  function Petri()
    r = new()
    r.d = Dict{Symbol, Data}()
    r.t = Dict{Symbol, Transition}()
    return r
  end
end

function Base.push!(p::Petri, d::Data)
  p.d[d.name] = d
end
function Base.push!(p::Petri, t::Transition)
  p.t[t.name] = t
end

function consume(d::Data, s::Symbol)
  a = d.data[s]
  if isa(a, Array)
    return pop!(a)
  else
    delete!(d.data, s)
    return a
  end
end

function consume(P::Petri, s::Symbol, t::Symbol = s)
  push!(P.change, s)
  return consume(P.d[s], t)
end

function Base.length(d::Data, s::Symbol)
  return length(d.data[s])
end

function read(d::Data, s::Symbol)
  return d.data[s]
end

function put(d::Data, s::Symbol, a::Any)
  if !haskey(d.data, s)
    d.data[s] = a
  else
    push!(d.data[s], a)
  end
end

function put(P::Petri, s::Symbol, t::Symbol, a::Any)
  push!(P.change, s)
  return put(P.d[s], t, a)
end

function put(P::Petri, s::Symbol, a::Any)
  return put(P, s, s, a)
end

function _try()  #parallel(?) sum(1:10)
  P = Petri()
  push!(P, Data(:p, :p =>collect(1:10)))
  push!(P, Data(:r, :r =>[]))
  push!(P, Data(:s, :s =>[]))
  push!(P, Data(:c1, :c => 1))
  push!(P, Data(:c2))

  T = Transition(:T)
  T.action = [() -> put(P, :s, consume(P, :p)),
              () -> put(P, :c2, :c, consume(P, :c1, :c))]
  T.possible = [()-> length(P.d[:p], :p)>0,
                () -> haskey(P.d[:c1].data, :c)]
  T.In = [:p, :c1]
  T.Out = [:s, :c2]
  push!(P, T)

  T = Transition(:S)
  T.action = [() -> put(P, :r, consume(P, :p)),
              () -> put(P, :c1, :c, consume(P, :c2, :c))]
  T.possible = [()-> length(P.d[:p].data[:p])>0,
                () -> haskey(P.d[:c2].data, :c)]
  T.In = [:p, :c2]
  T.Out = [:r, :c1]
  push!(P, T)

  T = Transition(:+)
  T.action = [ () -> put(P, :p, consume(P, :s) + consume(P, :r))]
  T.possible = [ () -> length(P.d[:r].data[:r]) > 0 && length(P.d[:s].data[:s]) > 0]
  T.In = [:s, :r]
  T.Out = [:p]
  push!(P, T)

  return P
end


function fire(P::Petri)
  P.change = Set{Symbol}()
  p = [k for k = keys(P.t) if all(i->i(), P.t[k].possible)]
  for k = p
    [x() for x = P.t[k].action]
  end
#  println(stderr, p)
#  println(stderr, P.d)
end  

function fire()
  global pe, M, c, pe
  fire(pe)
  for (k,v) = M
    delete!(c.c[:messages], v.m[:id])
  end

  for d = values(pe.d)
    if false && haskey(d.data, d.name)
      m = message("$(d.name): $(d.data[d.name])")
      push!(c, m)
      M[d.name] = m
    else
      m = message("$(d.name): $(d.data)")
      push!(c, m)
      M[d.name] = m
    end
  end
  display(Francy.FrancyMimeString, c)
end

function fire(t::Symbol)
  global pe, M, c, pe, T, D
  pe.change = Set{Symbol}()
  if all(i->i(), pe.t[t].possible)
    for i = pe.t[t].action
      i()
    end
  end
  for (k,v) = M
    delete!(c.c[:messages], v.m[:id])
  end

  for d = values(pe.d)
    if false && haskey(d.data, d.name)
      m = message("$(d.name): $(d.data[d.name])")
      push!(c, m)
      M[d.name] = m
    else
      m = message("$(d.name): $(d.data)")
      push!(c, m)
      M[d.name] = m
    end
  end
  for (k,v) in T
    if all(i -> i(), pe.t[k].possible)
      v.s[:color] = :green
    else
      v.s[:color] = :blue
    end
  end
  for (d, n) in D
    if haskey(pe.d[d].data, d)
      da = pe.d[d].data[d]
      if length(da) == 0
        n.s[:title] = "$(string(d)):[]"
      else
        n.s[:title] = "$(string(d)):[..$(da[end])]"
      end
    else
      k = keys(pe.d[d].data)
      if length(k) == 0
        n.s[:title] = "$(string(d)):"
      else
        n.s[:title] = "$(string(d)):$(first(k))"
      end
    end
  end
  display(Francy.FrancyMimeString, c)
end


function petri(P::Petri)
  global c,A, n, g, pe, M, T, D
  pe = P
  c = canvas("Petri")
  g = graph()
  D = Dict{Symbol, Francy.Node}()
  T = Dict{Symbol, Francy.Node}()
  M = Dict{Symbol, Francy.Message}()
  for d = keys(P.d)
    n = D[d] = node(string(d), :circle)
    if haskey(P.d[d].data, d)
      da = P.d[d].data[d]
      if length(da) == 0
        n.s[:title] = "$(string(d)):[]"
      else
        n.s[:title] = "$(string(d)):..$(da[end])]"
      end
    else
      k = keys(P.d[d].data)
      if length(k) == 0
        n.s[:title] = "$(string(d)):"
      else
        n.s[:title] = "$(string(d)):$(first(k))"
      end
    end
    push!(g, n)
  end
  for d = keys(P.t)
    n = T[d] = node(string(d), :square)
    push!(n, callback("PetriNet.fire", ":($d)"))
    if all(i->i(), P.t[d].possible)
      n.s[:color] = :green
    else
      n.s[:color] = :blue
    end
    push!(g, n)
  end

  for t = values(P.t)
    for i = t.In
      push!(g, link(D[i], T[t.name], length = 5))
    end
    for i = t.Out
      push!(g, link(T[t.name], D[i], length = 5))
    end
  end
  for d = values(P.d)
    if false && haskey(d.data, d.name)
      m = message("$(d.name): $(d.data[d.name])")
      push!(c, m)
      M[d.name] = m
    else
      m = message("$(d.name): $(d.data)")
      push!(c, m)
      M[d.name] = m
    end
  end
#  push!(n[2], callback("PetriNet.trigger", "(:"*n[2].s[:id]*", 1)"))
  push!(c, g)
  return c 
end

node_index(s::Symbol) = findfirst(x -> x.s[:id] == String(s), n)

function in_nodes(s::Symbol)
  global g
  res = []
  for i = values(g.g[:links])
    if i[:target] == String(s)
      push!(res, Symbol(i[:source]))
    end
  end
  return res
end

function out_nodes(s::Symbol)
  global g
  res = []
  for i = values(g.g[:links])
    if i[:source] == String(s)
      push!(res, Symbol(i[:target]))
    end
  end
  return res
end

function trigger(t::Tuple)
  global c, n, g

  for i in in_nodes(t[1])
    j = node_index(i)
    n[j].s[:title] = string(Char(Int(n[j].s[:title][1])-1))
  end
  for i in out_nodes(t[1])
    j = node_index(i)
    n[j].s[:title] = string(Char(Int(n[j].s[:title][1])+1))
  end
    
  display(Francy.FrancyMimeString, c)
end

end
