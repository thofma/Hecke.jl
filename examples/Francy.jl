module Francy

export canvas, graph, shape, link, menu, callback

using JSON, IJulia
Base.istextmime(::MIME"application/vnd.francy+json") = true

#once..
IJulia.register_mime(MIME("application/vnd.francy+json"));

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

canvas_cache = Dict{String, WeakRef}()

function canvas(t::String)
  C = Canvas(Dict(:version => "1.0.4",
       :mime => "application/vnd.francy+json",
       :canvas =>
    Dict(:width => 800,
         :id => create_id(),
         :height => 600,
         :title => t,
         :zoomToFit => true,
         :texTypesetting => false,
         :menus => Dict(),
         :messages => Dict(),
         :graph => Dict()
    )))
  
  global canvas_cache
  canvas_cache[C.c[:canvas][:id]] = WeakRef(C)
  global last_c
  last_c = C
  return C
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

function shape(n::String, type::Symbol = :circle; callbacks = Dict())
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
              :callbacks => callbacks
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

function add_message(a::Dict, m::Dict)
  a[:messages][m[:id]] = m
end

function add_callback(n::Dict, c::Dict)
  n[:callbacks][c[:id]] = c
end

function message(s::String)
  return Dict(:id => create_id(),
              :type => :info,
              :title => s,
              :value => ""
              )
end

using Hecke
function divisors(n::fmpz)
  lf = factor(n).fac
  z = Base.Iterators.ProductIterator(Tuple([[p^i for i=0:k] for (p,k) = lf]))
  l = fmpz[]
  for x = z
    push!(l, prod(x))
  end
  return l
end

function graphic_divisors(n::fmpz)
  c = canvas("Divisors of $n")
  d = divisors(n)
  no = [shape(string(d[i])) for i=1:length(d)]
  for n = 1:length(no)
    add_callback(no[n], callback("isprime", "(:" * c.c[:canvas][:id] * ", $(d[n]))"))
  end
  g = graph()
  for n = no
    add_node(g, n)
  end
  for i=1:length(d)
    for j=1:length(d)
      if i==j
        continue
      end
      if divides(d[i], d[j])[1]
        add_link(g, link(no[i], no[j]))
      end
    end
  end
  c.c[:canvas][:graph] = g
  return c
end

function canvas(s::Symbol)
  global canvas_cache
  return canvas_cache[string(s)].value
end

function Main.isprime(t::Tuple)
  n = fmpz(t[2])
  f = isprime(n)
  c = canvas(t[1])
  add_message(c.c[:canvas], message("$n is prime: $f"))
  display("application/vnd.francy+json", c)
  return true
end

function Trigger(a::String)
  b = JSON.parse(a)
#  global last_c
  c = b["func"] * "(" * b["knownArgs"] * ")"
  res = eval(Meta.parse(c))
#  add_message(last_c.c[:canvas], message("2:res is $c"))
#  display("application/vnd.francy+json", last_c)
end  

export Trigger

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

