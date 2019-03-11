module Francy

export canvas, graph, shape, link, menu, callback

using JSON
Base.istextmime(::MIME"application/vnd.francy+json") = true

function Base.show(io::IO, ::MIME"application/vnd.francy+json", s::String)
  print(io, s)
end


id_cnt = 0
function create_id()
  global id_cnt += 1
  return "Id$id_cnt"
end

mutable struct Canvas
  c::Dict
end

function Base.show(io::IO, t::MIME"application/vnd.francy+json", c::Canvas)
  show(io, t, JSON.json(c.c))
end

function canvas(t::String)
  return Canvas(Dict(:version => "1.0.4",
       :mime => "application/vnd.francy+json",
       :canvas =>
    Dict(:width => 800,
         :id => create_id(),
         :height => 600,
         :title => t,
         :zoomToFit => true,
         :texTypesetting => false,
         :menus => Dict(),
         :graph => Dict()
    )))
end

function graph()
  return Dict(:type => :directed,
              :id => create_id(),
              :simulation => true,
              :collapsed => true,
              :links => Dict(),
              :nodes => Dict(),
              :messages => Dict(), 
              )
end

function shape(n::String, type::Symbol = :circle)
  return Dict(:type => type,
              :id => create_id(),
              :size => 10,
              :x => 0,
              :y => 0,
              :title => n,
              :layer => 0,
              :color => "",
              :parent => "",
              :menus => Dict(),
              :messages => Dict(),
              :callbacks => Dict()
              )
end

function link(s::Dict, t::Dict)
  return Dict(:id => create_id(),
              :source => s[:id],
              :target => t[:id],
              :length => 0,
              :weight => 0,
              :color => "",
              :invisible => false
              )
end

function add_node(g::Dict, n::Dict)
  g[:nodes][n[:id]] = n
end

function add_link(g::Dict, l::Dict)
  g[:links][l[:id]] = l
end


function callback(f::String, a::String)
  return Dict(:id => create_id(),
              :func => f,
              :trigger => :click,
              :knownArgs => a,
              :requiredArgs => Dict()
              )
end

function menu(t::String, c::Dict)
  return Dict(:id => create_id(),
              :title => t,
              :callback => c)
end

function add_menu(a::Dict, m::Dict)
  a[:menus][m[:id]] = m
end

function add_callback(n::Dict, c::Dict)
  n[:callbacks][c[:id]] = c
end


end

#=
Hecke.example("Francy.jl")
using Main.Francy

c = canvas("test");

g = graph();

n1 = shape("1");
cb = callback("console.error(1)", "");
m = Francy.menu("maybe", cb)
Francy.add_menu(n1, m);
Francy.add_menu(n1, Francy.menu("or not", cb))

n2 = shape("2");
l = link(n1, n2);
Francy.add_node(g, n1);
Francy.add_node(g, n2);
Francy.add_link(g, l);
c.c[:canvas][:graph] = g;


display("application/vnd.francy+json", c)

=#

