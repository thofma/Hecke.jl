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
@test degree(h) == 9
L = simple_extension(K)[1]
@test degree(L) == 9
absolute_simple_field(L)
discriminant(maximal_order(K))
norm_equation(k, 27)
isGLZ_conjugate(ZZ[0 1; 0 0], ZZ[0 2; 0 0])
