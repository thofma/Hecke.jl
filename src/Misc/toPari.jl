function toPari(io::IO, f::Generic.Poly{nf_elem})
  Zy, y = PolynomialRing(FlintQQ, "y", cached = false)
  k = base_ring(f)
  kt = parent(f)
  s_k = k.S
  s_kt = kt.S
  #important to pari: the top poly needs to have x, so the field should be y...

  k.S = :t
  kt.S = :x

  print(io, "k = nfinit($(k.pol(y)));\n")
  print(io, "f = $f;\n")

  k.S = s_k
  kt.S = s_kt
  nothing
end

function toPari(s::String, f::Generic.Poly{nf_elem})
  g = open(s, "w")
  toPari(g, f)
  close(g)
end

# gp> #
# gp> read("bla");
# gp> nffactor(k, f);
#=

x-1
x^2-19
x^3-x^2+6
x^4 - 2*x^3 - 7*x^2 - 7*x + 3
x^5 - 3*x^3 - 2*x^2+8*x-10


Zx, x = PolynomialRing(FlintZZ)
g1 = swinnerton_dyer(7, x);
g2 = swinnerton_dyer(7, x);

k, a = number_field()
kt, t = k["t"]

g = (g1*g2)(t-a)
@time length(factor(g))

set_verbose_level(:PolyFactor, 1)

=#
