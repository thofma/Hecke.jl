
using Hecke

### Functions I need to rewrite because of NEMO


Qp = PadicField(7,10)
R, x = PolynomialRing(Qp,"x")

K,θ = Hecke.EisensteinField(x^6-7, "θ")


f = x^5 - 7*x + 4
fK = change_base_ring(f,K)


Ql = QadicField(17,3,10)
S, y = PolynomialRing(Ql, "y")
L,a = Hecke.EisensteinField(y^3-17*y^2+17*y-17, "a")

g = change_base_ring(L.pol, L)
Y = change_base_ring(y,L)

nothing


