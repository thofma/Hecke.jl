using Hecke

Q = quaternion_algebra(QQ, -1, -1)

_, i, j, k = basis(Q)

i^2 == -1 && j^2 == -1 && i * j == k

alpha = 1 + 2*i + 3*j

alpha == Q([1, 2, 3, 0])

K, sqrt2 = quadratic_field(2)
Q = quaternion_algebra(K, sqrt2, K(3))
alpha = Q([sqrt2, 1, 0, 1])

coefficients(alpha)

tr(alpha), norm(alpha)

trred(alpha), normred(alpha)

conjugate(alpha)

normred(alpha) == conjugate(alpha) * alpha

_, i, j, k = basis(Q);

divexact_right(k, j)

k == i * j

divexact_left(k, j)

k == j * (-i)

Q = quaternion_algebra(QQ, -1, -1)
_, i, j, k = basis(Q)
Qx, x = Q[:x]
f = i * x^2 + j * x
g = i * x

divexact_right(f, g) == x + k

divexact_left(f, g) == x + (- k)

Hecke.divrem_right(f, g)

Hecke.gcd_right(f, g)

Q = quaternion_algebra(QQ, -1, -1)
is_split(Q)

Q = quaternion_algebra(QQ, 1, -1)
is_split(Q)

is_split_with_zero_divisor(Q)

K, sqrt2 = quadratic_field(2)

fl, a = is_norm(K, 2);

fl

a

b = evaluate(a)

norm(b) == 2

norm_equation(K, 2)

K = QQ;

a1, a2 = 2, 3

b1, b2 = 3, 4

q = quadratic_space(K, diagonal_matrix(K, [a1, a2, -b1, b2]));

is_isotropic(q)

fl, v = is_isotropic_with_vector(q)

d = v[1]^2 * a1 + v[2]^2 * a2

v[1]^2 * a1 + v[2]^2 * a2 == v[3]^2 * b1 + v[4]^2 * b2
