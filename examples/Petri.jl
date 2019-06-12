module PetriNet

using Hecke, Francy

function petri()
  global c, n, g
  c = canvas("Petri")
  g = graph()
  n = [node("3", :circle), node("T", :square), node("0", :circle), node("2", :circle),
       node("S", :square), node("0", :circle)]

  for i=n
     push!(g, i)
  end
  n[1].s[:color] = :green
  push!(n[2], callback("PetriNet.trigger", "(:"*n[2].s[:id]*", 1)"))
  push!(n[5], callback("PetriNet.trigger", "(:"*n[5].s[:id]*", 2)"))
  push!(g, link(n[1], n[2], length = 5))
  push!(g, link(n[1], n[2], length = 5))
  push!(g, link(n[2], n[3], length = 5))
  push!(g, link(n[4], n[2], length = 5))
  push!(g, link(n[3], n[5], length = 5))
  push!(g, link(n[1], n[5], length = 5))
  push!(g, link(n[5], n[6], length = 5))
  push!(g, link(n[5], n[6], length = 5))
  push!(c, g)
  push!(c, message("message in C, $(collect(1:10))"))
  push!(c, message("message in C, $(collect(1:10))"))
  push!(n[5], message("message in N, \n$(collect(1:4))"))
  push!(n[5], message("message in N, \n$(collect(1:4))"))
  push!(g, message("message in G"))

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
