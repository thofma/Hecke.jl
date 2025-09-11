```@meta
EditURL = "quaternion.jl"
```

This file is also available as a jupyter notebook and a julia file:

[![download](https://img.shields.io/badge/download-notebook-blue)](https://docs.hecke.thofma.com/dev/tutorials/build/quaternion.ipynb)
[![nbviewer](https://raw.githubusercontent.com/jupyter/design/master/logos/Badges/nbviewer_badge.svg)](https://nbviewer.jupyter.org/url/docs.hecke.thofma.com/dev/tutorials/build/quaternion.ipynb)
[![download](https://img.shields.io/badge/download-script-blue)](https://docs.hecke.thofma.com/dev/tutorials/build/quaternion.jl)

````@setup bla
using Hecke
nothing
````

# Quaternion algebras

## Creation

````@repl bla
Q = quaternion_algebra(QQ, -1, -1)
````

Construct the standard basis:

````@repl bla
_, i, j, k = basis(Q)
````

Verifying the relations:

````@repl bla
i^2 == -1 && j^2 == -1 && i * j == k
````

Construction of elements:

````@repl bla
alpha = 1 + 2*i + 3*j
````

Or via directly supplying the coordinates as a vector:

````@repl bla
alpha == Q([1, 2, 3, 0])
````

This works for also for number fields:

````@repl bla
K, sqrt2 = quadratic_field(2)
Q = quaternion_algebra(K, sqrt2, K(3))
alpha = Q([sqrt2, 1, 0, 1])
````

## Properties of elements

Get the coefficients with respect to the canonical basis:

````@repl bla
coefficients(alpha)
````

Trace and norm (also reduced version)

````@repl bla
tr(alpha), norm(alpha)
````

````@repl bla
trred(alpha), normred(alpha)
````

Image of elements under canonical involution:

````@repl bla
conjugate(alpha)
````

````@repl bla
normred(alpha) == conjugate(alpha) * alpha
````

## Division

For division there are the two functions `divexact_left` and `divexact_right`. If `c = divexact_right(a, b)`, then `a == c * b`. So, `divexact_right(a, b)` returns an element `c`, such that `b` becomes a right-divisor of `a`.

````@repl bla
_, i, j, k = basis(Q);
nothing #hide
````

````@repl bla
divexact_right(k, j)
````

````@repl bla
k == i * j
````

````@repl bla
divexact_left(k, j)
````

````@repl bla
k == j * (-i)
````

## Polynomials

Polynomials behave very much like polynonomials over commutative rings, except that everything related to divisions needs to specifiy the "side".

````@repl bla
Q = quaternion_algebra(QQ, -1, -1)
_, i, j, k = basis(Q)
Qx, x = Q[:x]
f = i * x^2 + j * x
g = i * x
````

````@repl bla
divexact_right(f, g) == x + k
````

````@repl bla
divexact_left(f, g) == x + (- k)
````

````@repl bla
Hecke.divrem_right(f, g)
````

````@repl bla
Hecke.gcd_right(f, g)
````

# Splitting of quaternion algebras

````@repl bla
Q = quaternion_algebra(QQ, -1, -1)
is_split(Q)
````

````@repl bla
Q = quaternion_algebra(QQ, 1, -1)
is_split(Q)
````

````@repl bla
is_split_with_zero_divisor(Q)
````

# Solving norm equations

Let's solve a norm equation. We want to check whether $2$ is a norm of $\mathbf{Q}(\sqrt{2})$.

````@repl bla
K, sqrt2 = quadratic_field(2)
````

````@repl bla
fl, a = is_norm(K, 2);
nothing #hide
````

````@repl bla
fl
````

Since elements with given norm are in general large, they are represented in special "factored" form:

````@repl bla
a
````

We can turn this into an ordinary elements using `evaluate`:

````@repl bla
b = evaluate(a)
````

````@repl bla
norm(b) == 2
````

If we know that a norm equation has a solution, we can directly ask for it:

````@repl bla
norm_equation(K, 2)
````

# Representation by binary quadratic forms

Assume that we have two diagonal quadratic forms $q_1 = \langle a_1, a_2 \rangle$ and $q_2 = \langle b_1, b_2 \rangle$ over a field $K$.
We want to find an element $d$, which is represented both by $q_1$ and $q_2$.

````@repl bla
K = QQ;
nothing #hide
````

````@repl bla
a1, a2 = 2, 3
````

````@repl bla
b1, b2 = 3, 4
````

We form the quadratic form $q = \langle a_1, a_2, -b_1, -b_2\rangle$. Then the task becomes finding an isotropic vector.

````@repl bla
q = quadratic_space(K, diagonal_matrix(K, [a1, a2, -b1, b2]));
nothing #hide
````

Checking whether such an isotropic vector exists:

````@repl bla
is_isotropic(q)
````

````@repl bla
fl, v = is_isotropic_with_vector(q)
````

To extract the element $d$, we need to evaluate the quadratic form:

````@repl bla
d = v[1]^2 * a1 + v[2]^2 * a2
````

````@repl bla
v[1]^2 * a1 + v[2]^2 * a2 == v[3]^2 * b1 + v[4]^2 * b2
````

