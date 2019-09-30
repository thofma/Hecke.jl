
using Hecke

Qp = PadicField(7,10)
R, x = PolynomialRing(Qp,"x")

K,a = Hecke.EisensteinField(x^6-7, "a")


f = x^5 - 7*x + 4
fK = change_base_ring(f,K)

X = gen(parent(fK))
