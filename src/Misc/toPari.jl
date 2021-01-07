function toPari(io::IO, f::Generic.Poly{nf_elem})
  Zy, y = PolynomialRing(FlintQQ, "y", cached = false)
  k = base_ring(f)
  kt = parent(f)
  s_k = k.S
  s_kt = kt.S
  #important to pari: the top poly needs to have x, so the field should be y...

  k.S = :y
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

function toPari(f::IO, m::fmpz_mat)
  print(f, "A = [")
  for i=1:nrows(A)
    if i>1
      print(f, "; ")
    end
    for j=1:ncols(A)-1
      print(f, A[i,j], ",")
    end; print(f, A[i, ncols(A)])
  end
  print(f, "];")
end

function toPari(s::String, m::fmpz_mat)
  g = open(s, "w")
  toPari(g, m)
  close(g)
end


# gp> #
# gp> read("bla");
# gp> nffactor(k, f);
#=

from 
  https://www.math.u-bordeaux.fr/~kbelabas/research/vanhoeij.pdf
  p 26, polys h_1, ..., h_10 (so far)
x-1
x^2-19
x^3-x^2+6
x^4 - 2*x^3 - 7*x^2 - 7*x + 3
x^5 - 3*x^3 - 2*x^2+8*x-10
x^6 - 5*x^4 - x^3 + 10*x^2 - 11*x + 5
x^7-x^6-32*x^5-100*x^4-130*x^3-70*x^2+ 4*x+ 23
x^8-8*x^6-x^5+x^3+ 3*x^2-7*x+ 2
x^9-x^8-42*x^7-180*x^6-375*x^5-452*x^4-327*x^3-133*x^2-31*x-11
x^10-2*x^9+ 5*x^8+ 8*x^7+ 5*x^6+ 8*x^5-9*x^4-6*x^3+ 7*x^2+ 4*x+ 8


Zx, x = PolynomialRing(FlintZZ)
g1 = swinnerton_dyer(7, x);
g2 = swinnerton_dyer(8, x);

k, a = number_field()
kt, t = k["t"]

g = (g1*g2)(t-a)
@time length(factor(g))

needs prec_scale of 40 rather than 20. Why I don't know (yet)

set_verbose_level(:PolyFactor, 1)

=#
