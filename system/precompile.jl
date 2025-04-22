using Test
k, a = quadratic_field(10)
@test degree(k) == 2
k, a = cyclotomic_field(11)
G, mG = automorphism_group(k)
@test order(G) == 10
kt, t = k["t"]
factor(t^2-a)
factor(t^5-a)
k, a = wildanger_field(3, 13)
h = hilbert_class_field(k)
@test degree(h) == 9
K = number_field(h)
@test degree(K) == 9
L = simple_extension(K)[1]
@test degree(L) == 9
absolute_simple_field(L)
discriminant(maximal_order(K))
norm_equation(k, 27)
is_GLZ_conjugate(ZZ[0 1; 0 0], ZZ[0 2; 0 0])
II = matrix(ZZ,8,8, [-21 12 17 -3 -3 15 10 -8; -6 3 5 -1 -4 5 4 -2; -36 18 29 -5 7 25 16 -16; -72 36 58 -11 13 52 33 -33; 0 0 0 0 -9 3 2 0; 0 0 0 0 -21 0 5 4; 0 0 0 0 -9 0 2 2; 0 0 0 0 -36 0 8 7])
J = matrix(ZZ,8,8,[0 3 0 -1 0 0 0 0; -3 0 1 0 0 0 0 0; 0 0 0 1 0 0 0 0;-9 0 2 0 0 0 0 0; 0 0 0 0 -63 48 51 -13; 0 0 0 0 -84 63 68 -17; 0 0 0 0 -36 27 29 -7; 0 0 0 0 -144 108 116 -29])
is_GLZ_conjugate(II, J)
QA, A = polynomial_ring(Hecke.QQ, "A")
K, a = number_field(A^3 - 2, "a")
Kxyz, (x, y, z, t) = polynomial_ring(K, ["x", "y", "z", "t"])
@test length(factor((3*a*y*z*x^2+z-a)*(7*x+a*z^3*y))) == 2
