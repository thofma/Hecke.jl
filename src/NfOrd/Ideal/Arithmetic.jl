################################################################################
#
# NfOrd/Ideal/Arithmetic.jl : Arithmetic for ideals in orders of absolute
#                             number fields
#
# This file is part of Hecke.
#
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
#
#  Copyright (C) 2015, 2016, 2017 Tommy Hofmann
#  Copyright (C) 2015, 2016, 2017 Claus Fieker
#
################################################################################

################################################################################
#
#  Ideal addition / GCD
#
################################################################################

doc"""
***
    +(x::NfOrdIdl, y::NfOrdIdl)

> Returns $x + y$.
"""
function +(x::NfOrdIdl, y::NfOrdIdl)
  d = degree(order(x))
  H = vcat(basis_mat(x), basis_mat(y))
  g = gcd(minimum(x), minimum(y))
  if isone(g)
    return ideal(order(x), g)
  end
  H = sub(_hnf_modular_eldiv(H, g, :lowerleft), (d + 1):2*d, 1:d)
  return ideal(order(x), H)
end

################################################################################
#
#  Intersection / LCM
#
################################################################################

doc"""
    intersection(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdIdl
    lcm(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdIdl

> Returns $x \cap y$.
"""
function intersection(x::NfOrdIdl, y::NfOrdIdl)
  d = degree(order(x))
  H = vcat(basis_mat(x), basis_mat(y))
  K = _kernel(H)
  g = lcm(minimum(x),minimum(y))
  return ideal(order(x), _hnf_modular_eldiv(sub(K, 1:d, 1:d)*basis_mat(x), g, :lowerleft))
end

doc"""
    intersection(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdIdl
    lcm(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdIdl

> Returns $x \cap y$.
"""
lcm(x::NfOrdIdl, y::NfOrdIdl) = intersection(x, y)

################################################################################
#
#  Ideal multiplication
#
################################################################################

doc"""
    *(x::NfOrdIdl, y::NfOrdIdl)

> Returns $x \cdot y$.
"""
function *(x::NfOrdIdl, y::NfOrdIdl)
  if ismaximal_known(order(x)) && ismaximal(order(x))
    return mul_maximal(x, y)
  else
    return mul_gen(x, y)
  end
end

function mul_gen(x::NfOrdIdl, y::NfOrdIdl)
  order(x) != order(y) && error("Not compatible")
  O = order(x)
  d = degree(O)
  l = minimum(x, Val{false})*minimum(y, Val{false})
  z = fmpz_mat(degree(O)*degree(O), degree(O))
  z.base_ring = FlintZZ
  X = basis(x, Val{false})
  Y = basis(y, Val{false})
  t = O()
  for i in 1:d
    for j in 1:d
      mul!(t, X[i], Y[j])
      assure_has_coord(t)
      for k in 1:d
        z[(i - 1)*d + j, k] = t.elem_in_basis[k]
      end
    end
  end
  # This is a d^2 x d matrix
  return ideal(O, sub(_hnf_modular_eldiv(z, l, :lowerleft),
                      (d*(d - 1) + 1):d^2, 1:d))
end

# using the 2-normal representation
function prod_via_2_elem_normal(a::NfOrdIdl, b::NfOrdIdl)
  @hassert :NfOrd 1 has_2_elem_normal(a)
  @hassert :NfOrd 1 has_2_elem_normal(b)
  O = order(a)
  a1 = a.gen_one
  b1 = b.gen_one
  m = lcm(a1, b1)
  e, f = ppio(m, a1)
  if f == 1
    a2 = a.gen_two
  else
    # we need to become normal at m, we are normal at a
    # higher powers in a are fine
    # CRT: the 2nd gen of a needs to stay the same at a
    # and should be  1 at f


    #a2 = a.gen_two*f + a1^2
    if !false
      mul!(e, a1, a1)
      a2 = f*a.gen_two
      add!(a2, a2, e)
    else
      g, x, y = gcdx(f, e)

      mul!(e, a1, a1)
      mul!(x, x, f)
      a2 = x*a.gen_two
      mul!(y, y, e)
      add!(a2, a2, y)
     end
    # now (a1, a2) should be m-normal for a
  end

  e, f = ppio(m, b1)
  if f == 1
    b2 = b.gen_two
  else

    #b2 = b.gen_two*f + b1^2
    if !false #Carlo's new method
      mul!(e, b1, b1)
      b2 = f*b.gen_two
      add!(b2, b2, e)
     else
      g, x, y = gcdx(f, e)

      #b2 = b.gen_two*f*x + y*b1^2
      mul!(e, b1, b1)
      mul!(x, x, f)
      b2 = x*b.gen_two
      mul!(y, y, e)
      add!(b2, b2, y)
    end
  end
  C = ideal(O, a1*b1, a2*b2)
  C.norm = norm(a) * norm(b)
#
#CF: too expensive, need norm_mod to compute the norm only modulo...
#
#  if C.norm != gcd(C.gen_one^degree(O), FlintZZ(norm(C.gen_two)))
#    println("a:", a)
#    println("b:", b)
#    println("C:", C)
#    @hassert :NfOrd 1 gcd(a1^degree(O), norm(a2)) == norm(a)
#    @hassert :NfOrd 1 gcd(b1^degree(O), norm(b2)) == norm(b)
##    assert(false)
#  end

  if has_minimum(a) && has_minimum(b)
    ma = minimum(a, Val{false})
    mb = minimum(b, Val{false})

    if gcd(ma, mb) == 1
      C.minimum = ma * mb
    end

    # Otherwise, I don't know the
    # correct value.
  end

  C.gens_normal = m
  C.gens_weakly_normal = true #for the 1-ideal: it will not be normal...

  return C
end

# using the 2-weak-normal representation
function prod_via_2_elem_weakly(a::NfOrdIdl, b::NfOrdIdl)
  @hassert :NfOrd 1 has_2_elem(a)
  @hassert :NfOrd 1 has_2_elem(b)

  O = order(a)
  K = nf(O)
  bas = basis(O)
  n = degree(O)

  norm_c = norm(a) * norm(b)        # we ARE in the maximal order case
  norm_int_c = norm_c
  mod_c = fmpz(1)

  if has_minimum(a)
    mod_c *= minimum(a)
  else
    mod_c *= norm(a)
  end

  if has_minimum(b)
    mod_c *= minimum(b)
  else
    mod_c *= norm(b)
  end

  # Is this a good idea? Bad magic constants

  if mod_c > 250
    r = -500:500  # should still have enough elements...
  else
    r = -Int(div(mod_c, 2)):Int(div(mod_c, 2))
  end

  @vprint :NfOrd 1 "a: $a \nb: $b"
  @vprint :NfOrd 1 "using basis: $bas"

  gen = O()
  gen2 = O()
  t = O()
  s = O()
  u = O()

  cnt = 0
  while true
    cnt += 1
    if cnt % 20 == 0
      assure_2_normal(a)
      assure_2_normal(b)
      return a*b
    end
    rand!(t, O, r) # Nemo.rand_into!(bas, r, t)
    r2 = rand(r)
    rand!(s, O, r) # Nemo.rand_into!(bas, r, s)
    r4 = rand(r)
    mul!(t, t, a.gen_two)      # Nemo.mult_into!(t, a.gen_two, t)
    add!(t, t, r2*a.gen_one)   # Nemo.add_into!(t, r2*a.gen_one, t)
    mul!(s, s, b.gen_two)      # Nemo.mult_into!(s, b.gen_two, s)
    add!(s, s, r4*b.gen_one)   # Nemo.add_into!(s, r4*b.gen_one, s)
    mul!(u, s, t)              # Nemo.mult_into!(s, t, u)
    add!(gen, u, gen)          # Nemo.add_into!(u, gen, gen)
#    gen2 += (r1*K(a.gen_two) + r2*a.gen_one) *
#           (r3*K(b.gen_two) + r4*b.gen_one)
    gen = mod(gen, mod_c^2)    # = element_reduce_mod(gen, O, FlintZZ(mod_c)^2)

    if gcd(norm(gen), norm_int_c^2) == norm_int_c # should be ^n, but for
                                                  # the test ^2 is sufficient
      break
    end
  end

  @vprint :NfOrd 1 "prod_via_2_elem: used $cnt tries\n"

  c = ideal(O, norm_int_c, gen)

  c.norm = norm_c

  if has_minimum(a) && has_minimum(b) && gcd(minimum(a), minimum(b)) == 1
    c.minimum = minimum(a) * minimum(b)
                    # otherwise, I don't know the correct value
  end

  c.gens_weakly_normal = 1

  return c
end

# dispatching
doc"""
***
  *(x::NfMaxIdl, y::NfOrdIdl)

> Returns the ideal x*y.
"""
function mul_maximal(x::NfOrdIdl, y::NfOrdIdl)
  if x.iszero == 1 || y.iszero == 1
    z = ideal(order(x), zero_matrix(FlintZZ, degree(order(x)), degree(order(x))))
    z.iszero = 1
    return z
  end
  if isone(x)
    return y
  elseif isone(y)
    return x
  end
  if has_2_elem_normal(x) && has_2_elem_normal(y)
    return prod_via_2_elem_normal(x, y)
  end
  if has_2_elem(x) && has_2_elem(y)
    return prod_via_2_elem_weakly(x, y)
  end
  # Fall back to the generic algorithm _mul(::NfOrdIdl, ::NfOrdIdl)
  # Could also use invoke
  return mul_gen(x, y)
end

################################################################################
#
#  Addition
#
################################################################################

# Falls back to generic case +(::NfOrd, ::NfOrd)
#for ideals in the maximal order, the gcd is well defined...

doc"""
***
  gcd(A::NfOrdIdl, B::NfOrdIdl) -> NfOrdIdl
> The gcd or sum (A+B).
"""
function gcd(A::NfOrdIdl, B::NfOrdIdl)
  return A+B
end

function gcd_into!(A::NfOrdIdl, B::NfOrdIdl, C::NfOrdIdl)
  return C+B
end

#TODO: write a ppio version that allows for p-powers as well
doc"""
***
  gcd(A::NfOrdIdl, p::fmpz) -> NfOrdIdl
> The gcd or sum (A+ pO).
"""
function gcd(A::NfOrdIdl, p::fmpz)
  if isdefined(A, :minimum)
    if gcd(A.minimum, p) == 1
      return ideal(order(A), fmpz(1))
    end
  end
  if isdefined(A, :norm)
    if gcd(A.norm, p) == 1
      return ideal(order(A), fmpz(1))
    end
  end
  if has_2_elem(A)
    g = gcd(A.gen_one, p)
    @assert !isone(g)
    return ideal(order(A), g, A.gen_two)
  else
    @assert isdefined(A, :basis_mat)
    return A + ideal(order(A), p)
  end
end

################################################################################
#
#  Ad hoc multiplication
#
################################################################################

# multiplication by fmpz, using two normal presentation
function prod_by_int_2_elem_normal(A::NfOrdIdl, a::fmpz)
  @assert has_2_elem(A) && has_2_elem_normal(A)

  # <a,a> is a a-normal presentation
  # we need to have a common presentation for A and a though

  m = lcm(a, A.gen_one)

  e, f = ppio(m, A.gen_one)
  if f == 1
    a2 = A.gen_two
  else
                           # we need to become normal at m, we are normal at a
                           # higher powers in a are fine
                           # CRT: the 2nd gen of a needs to stay the same at a
                           # and should be  1 at f
    a2 = A.gen_two*f + A.gen_one^2 # now (a1, a2) should be m-normal for a
  end

  B = NfOrdIdl(A.gen_one*a, a2*a)
  B.gens_normal = m

  if has_minimum(A)
    B.minimum = A.minimum * a
  end

  if has_norm(A)
    B.norm = A.norm * a^degree(A.parent.order)
  end

  @assert has_2_elem(B) && has_2_elem_normal(B)
  return B
end

function prod_by_int_2_elem(A::NfOrdIdl, a::fmpz)
  @assert has_2_elem(A)

  B = NfOrdIdl(A.gen_one*a, A.gen_two*a)
  B.gens_normal = A.gens_normal

  if has_minimum(A)
    B.minimum = A.minimum * a
  end

  if has_norm(A)
    B.norm = A.norm * a^degree(A.parent.order)
  end

  @assert has_2_elem(B)
  return B
end

doc"""
***
    *(x::NfOrdIdl, y::fmpz) -> NfOrdIdl

> Returns the ideal $x \cdot y$.
"""
function *(x::NfOrdIdl, y::fmpz)
  if ismaximal_known(order(x)) && ismaximal(order(x))
    return mul_maximal(x, y)
  else
    return mul_gen(x, y)
  end
end

function mul_maximal(x::NfOrdIdl, y::fmpz)
  if y == 1 || y == -1
    return x
  end

  if has_2_elem(x)
    if has_2_elem_normal(x)
      return prod_by_int_2_elem_normal(x,y)
# this does not make any sense since prod_by_int_2_elem(x, y) works only if has_2_elem_norm(x) == true
#    else
#      return prod_by_int_2_elem(x,y)
    end
  end

  return x*ideal(order(x), y)
end

*(x::fmpz, y::NfOrdIdl) = y * x

doc"""
***
    *(x::NfOrdIdl, y::Integer) -> NfOrdIdl

> Returns the ideal $x \cdot y$.
"""
*(x::NfOrdIdl, y::Integer) = x * fmpz(y)

*(x::Integer, y::NfOrdIdl) = y * x

function *(x::NfOrdElem, y::NfOrdIdl)
  parent(x) != order(y) && error("Orders of element and ideal must be equal")
  return ideal(parent(x), x) * y
end

*(x::NfOrdIdl, y::NfOrdElem) = y * x

function mul_gen(x::NfOrdIdl, y::fmpz)
  z = ideal(order(x), basis_mat(x)*y)
  if isdefined(x, :princ_gen)
    z.princ_gen = x.princ_gen * y
  end
  if isdefined(x, :princ_gen_special)
    z.princ_gen_special = (2, 0, x.princ_gen_special[x.princ_gen_special[1] + 1] * y)
  end
  return z
end

################################################################################
#
#  Idempotents
#
################################################################################

doc"""
    idempotents(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdElem, NfOrdElem

> Returns a tuple `(e, f)` consisting of elements `e in x`, `f in y` such that
> `1 = e + f`.
>
> If the ideals are not coprime, an error is raised.
"""
function idempotents(x::NfOrdIdl, y::NfOrdIdl)
  !(order(x) === order(y)) && error("Parent mismatch")
  O = order(x)
  d = degree(O)

  mx = minimum(x)
  my = minimum(y)

  g, u, v = gcdx(mx, my)
  if isone(g)
    z = O(u*mx)
    @hassert :NfOrd 2 z in x
    @hassert :NfOrd 2 (1 - z) in y
    return z, 1 - z
  end

  # form the matrix
  #
  # ( 1 |  1  | 0 )
  # ( 0 | M_x | I )
  # ( 0 | M_y | 0 )

  V = O.tidempotents

  u = elem_in_basis(one(O))

  V[1, 1] = 1

  for i in 1:d
    V[1, i + 1] = u[i]
  end

  _copy_matrix_into_matrix(V, 2, 2, basis_mat(x))
  _copy_matrix_into_matrix(V, 2 + d, 2, basis_mat(y))

  for i in 1:d
    V[1 + i, d + 1 + i] = 1
  end

  H = hnf(V) # upper right

  for i in 2:(1 + d)
    if H[1, i] != 0
      error("Ideals are not coprime")
    end
  end

  basisofx = basis(x, Val{false})

  z = basisofx[1]*H[1, d + 2]

  for i in 2:d
    z = z + basisofx[i]*H[1, d + 1 + i]
  end

  @hassert :NfOrd 2 -z in x
  @hassert :NfOrd 2 1 + z in y

  ccall((:fmpz_mat_zero, :libflint), Void, (Ptr{fmpz_mat}, ), &V)

  return -z, 1 + z
end

################################################################################
#
#  crt
#
################################################################################
doc"""
   crt(r1::NfOrdElem, i1::NfOrdIdl, r2::NfOrdElem, i2::NfOrdIdl) -> NfOrdElem
> Find $x$ s.th $x \equiv r1 \bmod i1$ and $x \equiv r2 \bmod i2$
using (((idempotents)))
"""
function crt(r1::NfOrdElem, i1::NfOrdIdl, r2::NfOrdElem, i2::NfOrdIdl)
  u, v = idempotents(i1, i2)
  return r1*v + r2*u
end

function crt(a::Array{NfOrdElem, 1}, I::Array{NfOrdIdl, 1})
  if length(a) == 1
    return a[1]
  end
  if length(a) == 2
    return crt(a[1], I[1], a[2], I[2])
  end
  A = [crt(a[2*i-1], I[2*i-1], a[2*i], I[2*i]) for i=1:div(length(a), 2)]
  B = [I[2*i-1]*I[2*i] for i=1:div(length(a), 2)]
  if isodd(length(a))
    push!(A, a[end])
    push!(B, B[end])
  end
  return crt(A, B)
end
################################################################################
#
#  Division
#
################################################################################

divexact(A::NfOrdIdl, b::Integer) = divexact(A, fmpz(b))
doc"""
***
    divexact(A::NfOrdIdl, y::fmpz) -> NfOrdIdl
    divexact(A::NfOrdIdl, y::Integer) -> NfOrdIdl

> Returns $A/y$ assuming that $A/y$ is again an integral ideal.
"""
#TODO: write a divexact! to change the ideal?
#  difficult due to Julia's inability to unset entries...
function divexact(A::NfOrdIdl, b::fmpz)
  zk = order(A)
  if has_2_elem(A)
    B = ideal(zk, divexact(A.gen_one, b), divexact(A.gen_two, b))
    if isdefined(A, :gens_normal)
      B.gens_normal = A.gens_normal
    end
    B.gens_weakly_normal = A.gens_weakly_normal
    if has_basis_mat(A)
      B.basis_mat = divexact(A.basis_mat, b)
    end
    if false && has_basis_mat_inv(A)
      error("not defined at all")
      B.basis_mat_inv = b*A.basis_mat_inv
    end
  else
    B = ideal(zk, divexact(A.basis_mat, b))
    if false && has_basis_mat_inv(A)
      error("not defined at all")
      B.basis_mat_inv = b*A.basis_mat_inv
    end
  end
  if has_minimum(A)
    B.minimum = divexact(A.minimum, b)
  end
  if has_norm(A)
    B.norm = divexact(A.norm, b^degree(zk))
  end
  if has_princ_gen(A)
    B.princ_gen = divexact(A.princ_gen, b)
  end
  #TODO princ_gen_special missing
  return B
end

doc"""
***
    divexact(A::NfOrdIdl, B::NfOrdIdl) -> NfOrdIdl

> Returns $AB^{-1}$ assuming that $AB^{-1}$ is again an integral ideal.
"""
function divexact(A::NfOrdIdl, B::NfOrdIdl)
  # It is assumed that B divides A, that is, A \subseteq B
  t_prod = 0.0
  t_simpl = 0.0
  t_b_mat = 0.0
  t_2_elem_weak = 0.0
  t_2_elem = 0.0

  if norm(A) == norm(B)
    return ideal(order(A), one(FlintZZ), order(A)(1))
  else
    t_prod += @elapsed I = A*inv(B)
    t_simpl += @elapsed simplify_exact!(I)
    #t_b_mat += @elapsed B = basis_mat(I)
    I.den != 1 && error("Division not exact")
    #I = ideal(order(A), B.num)
    #t_2_elem_weak += @elapsed _assure_weakly_normal_presentation(I)
    #t_2_elem += @elapsed assure_2_normal(I)

    #println("  computation for product: $t_prod")
    #println("  simplification         : $t_simpl")
    #println("  basis matrix           : $t_b_mat")
    #println("  2 weak presentation    : $t_2_elem_weak")
    #println("  2 elem presentation    : $t_2_elem")

    return I.num

  end
end


