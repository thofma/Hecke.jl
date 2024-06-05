################################################################################
#
# AbsSimpleNumFieldOrder/Ideal/Arithmetic.jl : Arithmetic for ideals in orders of absolute
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

function check_parent(x::AbsNumFieldOrderIdeal, y::AbsNumFieldOrderIdeal)
   if order(x) !== order(y)
     error("Ideals do not have the same order.")
   end
end

################################################################################
#
#  Ideal addition / GCD
#
################################################################################

#x has a princ gen special
function sum_princ_gen_special(x::AbsNumFieldOrderIdeal, y::AbsNumFieldOrderIdeal)
  OK = order(x)
  genx = x.princ_gen_special[2]+x.princ_gen_special[3]
  if has_2_elem(y)
    if has_minimum(y)
      gen1 = gcd(genx, minimum(y, copy = false))
      if gen1 == minimum(y, copy = false)
        return y
      end
    else
      gen1 = gcd(genx, y.gen_one)
      if gen1 == y.gen_one
        return y
      end
    end
    res = ideal(OK, gen1, y.gen_two)
    fl = false
    if has_minimum(y)
      fl = gen1 == ppio(minimum(y, copy = false), genx)[1]
    else
      fl = gen1 == ppio(y.gen_one, genx)[1]
    end
    if fl
      if has_norm(y)
        res.norm = ppio(norm(y), genx)[1]
      end
      if has_minimum(y)
        res.minimum = ppio(minimum(y), genx)[1]
      end
    end
  else
    M1 = _hnf_modular_eldiv(basis_matrix(y, copy = false), genx, :lowerleft)
    res = ideal(OK, M1; check=false, M_in_hnf=true)
  end
  @hassert :AbsNumFieldOrder 1 res == sum_via_basis_matrix(x, y)
  return res
end

function sum_via_basis_matrix(x::AbsNumFieldOrderIdeal, y::AbsNumFieldOrderIdeal)
  OK = order(x)
  d = degree(OK)
  g = gcd(minimum(x, copy = false), minimum(y, copy = false))
  H = vcat(basis_matrix(x, copy = false), basis_matrix(y, copy = false))
  hnf_modular_eldiv!(H, g, :lowerleft)
  H = view(H, (d + 1):2*d, 1:d)
  res = ideal(OK, H; check=false, M_in_hnf=true)
  if isone(basis(OK, copy = false)[1])
    res.minimum = H[1, 1]
  end
  res.norm = prod_diagonal(H)
  return res
end

#x is a principal ideal
function sum_princ_gen(x::AbsNumFieldOrderIdeal, y::AbsNumFieldOrderIdeal)
  OK = order(x)
  d = degree(OK)
  g = gcd(minimum(y, copy = false), minimum(x, copy = false))
  M = basis_matrix(y, copy = false)
  N = representation_matrix_mod(x.princ_gen, g)
  L = vcat(M, N)
  hnf_modular_eldiv!(L, g, :lowerleft)
  H = view(L, (d + 1):2*d, 1:d)
  res = ideal(OK, H; check=false, M_in_hnf=true)
  if isone(basis(OK, copy = false)[1])
    res.minimum = H[1, 1]
  end
  res.norm = prod_diagonal(H)
  @hassert :AbsNumFieldOrder 1 res == sum_via_basis_matrix(x, y)
  return res
end

function +(x::AbsNumFieldOrderIdeal, y::AbsNumFieldOrderIdeal)
  check_parent(x, y)
  OK = order(x)

  if iszero(x)
    return y
  end
  if iszero(y)
    return x
  end

  if isdefined(x, :gen_one) && isdefined(y, :gen_one) && isone(gcd(x.gen_one, y.gen_one))
    return ideal(OK, 1)
  end
  if isdefined(x, :norm) && isdefined(y, :norm) && isone(gcd(x.norm, y.norm))
    return ideal(OK, 1)
  end
  if has_princ_gen_special(x)
    return sum_princ_gen_special(x, y)
  end
  if has_princ_gen_special(y)
    return sum_princ_gen_special(y, x)
  end
  g = gcd(minimum(x, copy = false), minimum(y, copy = false))
  if isone(g)
    return ideal(order(x), g)
  end
  d = degree(OK)
  if is_simple(nf(OK)) && is_defining_polynomial_nice(nf(OK)) && contains_equation_order(OK) && is_prime(g) && !is_index_divisor(OK, g) && has_2_elem(x) && has_2_elem(y)
    #I can use polynomial arithmetic
    if fits(Int, g)
      R1 = residue_ring(FlintZZ, Int(g), cached = false)[1]
      R1x = polynomial_ring(R1, "x", cached = false)[1]
      ggp_small = gcd(R1x(x.gen_two.elem_in_nf), R1x(y.gen_two.elem_in_nf))
      if isone(ggp_small)
        return ideal(OK, 1)
      end
      Zx = polynomial_ring(FlintZZ, "x", cached = false)[1]
      ggZ = lift(Zx, ggp_small)
    else
      R = residue_ring(FlintZZ, g, cached = false)[1]
      Rx = polynomial_ring(R, "x", cached = false)[1]
      ggp_large = gcd(Rx(x.gen_two.elem_in_nf), Rx(y.gen_two.elem_in_nf))
      if isone(ggp_large)
        return ideal(OK, 1)
      end
      Zx = polynomial_ring(FlintZZ, "x", cached = false)[1]
      ggZ = lift(Zx, ggp_large)
    end
    gen_2 = OK(nf(OK)(ggZ))
    return ideal(OK, g, gen_2)
  end
  if has_princ_gen(x) && !has_basis_matrix(x)
    return sum_princ_gen(x, y)
  end
  if has_princ_gen(y) && !has_basis_matrix(y)
    return sum_princ_gen(y, x)
  end
  return sum_via_basis_matrix(x, y)
end

################################################################################
#
#  Intersection / LCM
#
################################################################################

@doc raw"""
    intersect(x::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, y::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

Returns $x \cap y$.
"""
function intersect(x::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, y::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  check_parent(x, y)
  g = gcd(minimum(x), minimum(y))
  if isone(g)
    #The ideals are coprime, the intersection is equal to the product
    return x*y
  end
  d = degree(order(x))
  H = vcat(basis_matrix(x, copy = false), basis_matrix(y, copy = false))
  K = kernel(H, side = :left)
  g = lcm(minimum(x),minimum(y))
  return ideal(order(x), _hnf_modular_eldiv(view(K, 1:d, 1:d)*basis_matrix(x, copy = false), g, :lowerleft); check=false, M_in_hnf=true)
end

lcm(x::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, y::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) = intersect(x, y)

################################################################################
#
#  Ideal multiplication
#
################################################################################

function *(x::S, y::S) where S <: AbsNumFieldOrderIdeal
  check_parent(x, y)
  @hassert :AbsNumFieldOrder 1 is_consistent(x)
  @hassert :AbsNumFieldOrder 1 is_consistent(y)
  OK = order(x)
  if is_maximal_known_and_maximal(OK)
    z = mul_maximal(x, y)
  else
    z = mul_gen(x, y)
  end
  @hassert :AbsNumFieldOrder 1 is_consistent(z)
  return z
end

function mul_gen(x::S, y::S) where S <: AbsNumFieldOrderIdeal
  check_parent(x, y)
  if iszero(x) || iszero(y)
    I1 = ideal(order(x), 0)
    I1.iszero = 1
    return I1
  end
  O = order(x)
  d = degree(O)
  l = minimum(x, copy = false)*minimum(y, copy = false)
  if has_2_elem(x) && has_basis_matrix(y)
    M1 = representation_matrix_mod(x.gen_two, l)
    Mf = vcat(minimum(x, copy = false)*basis_matrix(y, copy = false), basis_matrix(y, copy = false)*M1)
    hnf_modular_eldiv!(Mf, l, :lowerleft)
    J = ideal(O, view(Mf, (d+1):2*d, 1:d); check=false, M_in_hnf=true)
    if is_coprime(minimum(x, copy = false), minimum(y, copy = false))
      J.minimum = minimum(x, copy = false)*minimum(y, copy = false)
    end
    return J
  end
  if has_2_elem(y) && has_basis_matrix(x)
    M1 = representation_matrix_mod(y.gen_two, l)
    Mf = vcat(minimum(y, copy = false)*basis_matrix(x, copy = false), basis_matrix(x, copy = false)*M1)
    hnf_modular_eldiv!(Mf, l, :lowerleft)
    J = ideal(O, view(Mf, (d+1):2*d, 1:d); check=false, M_in_hnf=true)
    if is_coprime(minimum(x, copy = false), minimum(y, copy = false))
      J.minimum = minimum(x, copy = false)*minimum(y, copy = false)
    end
    return J
  end
  z = zero_matrix(FlintZZ, 2*degree(O), degree(O))
  z1 = zero_matrix(FlintZZ, 2*degree(O), degree(O))
  X = basis(x, copy = false)
  Y = basis_matrix(y, copy = false)
  for i in 1:d
    M1 = representation_matrix_mod(X[i], l)
    _copy_matrix_into_matrix(z1, 1, 1, M1)
    hnf_modular_eldiv!(z1, minimum(x, copy = false), :lowerleft)
    mul!(M1, Y, M1)
    _copy_matrix_into_matrix(z, 1, 1, M1)
    hnf_modular_eldiv!(z, l, :lowerleft)
    if view(z1, d+1:2*d, 1:d) == basis_matrix(x, copy = false)
      break
    end
  end
  # This is a d^2 x d matrix
  J = ideal(O, view(hnf_modular_eldiv!(z, l, :lowerleft),
                      (d+1):2*d, 1:d); check=false, M_in_hnf=true)
  if is_coprime(minimum(x, copy = false), minimum(y, copy = false))
    J.minimum = minimum(x, copy = false)*minimum(y, copy = false)
  end
  return J
end

# using the 2-normal representation
function prod_via_2_elem_normal(a::S, b::S) where S <: AbsNumFieldOrderIdeal
  check_parent(a, b)
  @hassert :AbsNumFieldOrder 1 has_2_elem_normal(a)
  @hassert :AbsNumFieldOrder 1 has_2_elem_normal(b)
  O = order(a)
  a1 = a.gen_one
  if has_minimum(a)
    a1 = minimum(a, copy = false)
  end
  b1 = b.gen_one
  if has_minimum(b)
    b1 = minimum(b, copy = false)
  end
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
    mul!(e, a1, a1)
    a2 = f*a.gen_two
    add!(a2, a2, e)
    # now (a1, a2) should be m-normal for a
  end

  e, f = ppio(m, b1)
  if f == 1
    b2 = b.gen_two
  else
    #b2 = b.gen_two*f + b1^2
    mul!(e, b1, b1)
    b2 = f*b.gen_two
    add!(b2, b2, e)
  end
  C = ideal(O, a1*b1, a2*b2)
  C.norm = norm(a) * norm(b)

  if has_minimum(a) && has_minimum(b)
    ma = minimum(a, copy = false)
    mb = minimum(b, copy = false)

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
function prod_via_2_elem_weakly(a::S, b::S) where S <: AbsNumFieldOrderIdeal
  check_parent(a, b)
  @hassert :AbsNumFieldOrder 1 has_2_elem(a)
  @hassert :AbsNumFieldOrder 1 has_2_elem(b)

  O = order(a)
  K = nf(O)
  bas = basis(O)
  n = degree(O)

  norm_c = norm(a, copy = false) * norm(b, copy = false)        # we ARE in the maximal order case
  first_gen_new = ZZRingElem(1)
  if has_minimum(a)
    first_gen_new *= minimum(a, copy = false)
  else
    first_gen_new *= gcd(a.gen_one, norm(a, copy = false))
  end
  if has_minimum(b)
    first_gen_new *= minimum(b, copy = false)
  else
    first_gen_new *= gcd(b.gen_one, norm(b, copy = false))
  end
  norm_int_c = norm_c
  mod_c = ZZRingElem(1)

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

  @vprintln :AbsNumFieldOrder 1 "a: $a \nb: $b"
  @vprintln :AbsNumFieldOrder 1 "using basis: $bas"

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

  @vprintln :AbsNumFieldOrder 1 "prod_via_2_elem: used $cnt tries"

  c = ideal(O, first_gen_new, gen)

  c.norm = norm_c

  if has_minimum(a) && has_minimum(b) && gcd(minimum(a), minimum(b)) == 1
    c.minimum = minimum(a) * minimum(b)
                    # otherwise, I don't know the correct value
  end

  c.gens_weakly_normal = true

  return c
end

# dispatching
function mul_maximal(x::S, y::S) where S <: AbsNumFieldOrderIdeal
  check_parent(x, y)
  if iszero(x) || iszero(y)
    z = ideal(order(x), 0)
    z.iszero = 1
    return z
  end
  if isone(x)
    return y
  elseif isone(y)
    return x
  end
  if has_princ_gen_special(x)
    return princ_gen_special(x)*y
  end
  if has_princ_gen_special(y)
    return princ_gen_special(y)*x
  end
  if has_2_elem_normal(x) && has_2_elem_normal(y)
    return prod_via_2_elem_normal(x, y)
  end
  if has_2_elem(x) && has_2_elem(y)
    return prod_via_2_elem_weakly(x, y)
  end
  # Fall back to the generic algorithm _mul(::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  # Could also use invoke
  return mul_gen(x, y)
end

################################################################################
#
#  Addition
#
################################################################################

# Falls back to generic case +(::AbsSimpleNumFieldOrder, ::AbsSimpleNumFieldOrder)
#for ideals in the maximal order, the gcd is well defined...

function gcd(A::S, B::S) where S <: AbsNumFieldOrderIdeal
  check_parent(A, B)
  return A+B
end

function gcd_into!(A::AbsNumFieldOrderIdeal, B::AbsNumFieldOrderIdeal, C::AbsNumFieldOrderIdeal)
  return C+B
end

#TODO: write a ppio version that allows for p-powers as well
@doc raw"""
    gcd(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, p::ZZRingElem) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

The gcd or sum (A + pO).
"""
function gcd(A::AbsNumFieldOrderIdeal, p::ZZRingElem)
  if isdefined(A, :minimum)
    if gcd(minimum(A, copy = false), p) == 1
      return ideal(order(A), ZZRingElem(1))
    end
  end
  if isdefined(A, :norm)
    if gcd(norm(A, copy = false), p) == 1
      return ideal(order(A), ZZRingElem(1))
    end
  end
  if has_2_elem(A)
    g = gcd(A.gen_one, p)
    return ideal(order(A), g, A.gen_two)
  else
    @assert isdefined(A, :basis_matrix)
    return A + ideal(order(A), p)
  end
end

################################################################################
#
#  Powering
#
################################################################################

function Base.:(^)(A::AbsNumFieldOrderIdeal, e::Int)
  @hassert :AbsNumFieldOrder 1 is_consistent(A)
  OK = order(A)
  if e == 0
    return ideal(OK, 1)
  elseif e == 1
    return A
  end
  if is_maximal_known_and_maximal(OK) && is_simple(nf(OK)) && has_2_elem(A)
    return pow_2_elem(A, e)
  else
    return Base.power_by_squaring(A, e)
  end
end

function pow_2_elem(A::AbsNumFieldOrderIdeal, e::Int)
  OK = order(A)
  if A.is_principal == 1 && isdefined(A, :princ_gen)
    gen = (A.princ_gen::elem_type(OK))^e
    I = ideal(OK, gen)
    if isdefined(A, :norm)
      I.norm = norm(A)^e
    end
    if is_prime_known(A) && is_prime(A)
      eA = A.splitting_type[1]
      I.minimum = minimum(A)^(div(e-1, eA)+1)
    end
    I.is_prime = 2
    return I
  elseif is_prime_known(A) && is_prime(A)
    eA = A.splitting_type[1]
    minim = minimum(A)^(div(e-1, eA)+1)
    gen1 = minim
    gen2 = A.gen_two^e
    I = ideal(OK, gen1, gen2)
    I.minimum = deepcopy(minim)
    if isdefined(A, :norm)
      I.norm = norm(A)^e
    end
    if has_2_elem_normal(A)
      I.gens_normal = A.gens_normal
    end
    I.gens_weakly_normal = has_weakly_normal(A)
    I.is_prime = 2
    return I
  else
    gen1 = A.gen_one^e
    gen2 = A.gen_two^e
    I = ideal(OK, gen1, gen2)
    if isdefined(A, :norm)
      I.norm = norm(A)^e
    end
    if isdefined(A, :minimum) && isone(gcd(minimum(A, copy = false), discriminant(OK)))
      I.minimum = A.minimum^e
    end
    if has_2_elem_normal(A)
      I.gens_normal = A.gens_normal
    end
    I.gens_weakly_normal = has_weakly_normal(A)
    I.is_prime = 2
    return I
  end
end

# To stop the wrong julia behavior for I^2 and I^-2
Base.literal_pow(::typeof(^), A::AbsNumFieldOrderIdeal, ::Val{p}) where {p} = A^p

################################################################################
#
#  Ad hoc multiplication
#
################################################################################

# multiplication by ZZRingElem, using two normal presentation
function prod_by_int_2_elem_normal(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, a::ZZRingElem)
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

  B = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}(A.gen_one*a, a2*a)
  if has_princ_gen_special(A)
    B.princ_gen_special = (2, 0, (A.princ_gen_special[2] + A.princ_gen_special[3])*a)
  end

  if has_princ_gen(A)
    B.is_principal = 1
    B.princ_gen = a*A.princ_gen
  end
  B.gens_normal = m

  if has_minimum(A)
    B.minimum = A.minimum * a
  end

  if has_norm(A)
    B.norm = A.norm * a^degree(order(A))
  end

  @assert has_2_elem(B) && has_2_elem_normal(B)
  return B
end

function prod_by_int_2_elem(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, a::ZZRingElem)
  @assert has_2_elem(A)

  B = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}(A.gen_one*a, A.gen_two*a)
  if has_princ_gen(A)
    B.is_principal = 1
    B.princ_gen = A.princ_gen*a
  end

  if has_princ_gen_special(A)
    B.princ_gen_special = (2, 0, (A.princ_gen_special[2]+A.princ_gen_special[3])*a)
  end

  if has_minimum(A)
    B.minimum = A.minimum * a
  end

  if has_norm(A)
    B.norm = A.norm * a^degree(order(A))
  end

  @assert has_2_elem(B)
  return B
end

function *(x::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, y::ZZRingElem)
  if is_maximal_known_and_maximal(order(x))
    return mul_maximal(x, y)
  else
    return mul_gen(x, y)
  end
end

function mul_maximal(x::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, y::ZZRingElem)
  if iszero(y)
    z = ideal(order(x), 0)
    z.iszero = 1
    return z
  end

  if isone(y) || y == -1
    return x
  end

  if has_2_elem(x)
    if has_2_elem_normal(x)
      return prod_by_int_2_elem_normal(x,y)
    else
      return prod_by_int_2_elem(x,y)
    end
  end

  @hassert :AbsNumFieldOrder 1 has_basis_matrix(x)
  return ideal(order(x), basis_matrix(x, copy = false)*y)
end

*(x::ZZRingElem, y::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) = y * x

*(x::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, y::Integer) = x * ZZRingElem(y)

*(x::Integer, y::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) = y * x

function *(x::AbsSimpleNumFieldOrderElem, y::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  parent(x) !== order(y) && error("Orders of element and ideal must be equal")
  return ideal(parent(x), x) * y
end

*(x::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, y::AbsSimpleNumFieldOrderElem) = y * x

function mul_gen(x::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, y::ZZRingElem)
  if y == 0
    z = ideal(order(x), zero_matrix(FlintZZ, degree(order(x)), degree(order(x))))
    z.iszero = 1
    return z
  end

  z = ideal(order(x), basis_matrix(x, copy = false)*y)
  if isdefined(x, :princ_gen)
    z.princ_gen = x.princ_gen * y
  end
  if isdefined(x, :princ_gen_special)
    z.princ_gen_special = (2, 0, x.princ_gen_special[x.princ_gen_special[1] + 1] * y)
  end
  if isdefined(x, :norm)
    z.norm = x.norm*y^degree(order(x))
  end
  if isdefined(x, :minimum)
    z.minimum = x.minimum*y
  end
  return z
end

################################################################################
#
#  Idempotents
#
################################################################################

@doc raw"""
    idempotents(x::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, y::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> AbsSimpleNumFieldOrderElem, AbsSimpleNumFieldOrderElem

Returns a tuple `(e, f)` consisting of elements `e in x`, `f in y` such that
`1 = e + f`.

If the ideals are not coprime, an error is raised.
"""
function idempotents(x::AbsNumFieldOrderIdeal, y::AbsNumFieldOrderIdeal)
  check_parent(x, y)
  O = order(x)
  d = degree(O)


 if has_2_elem(x) && has_2_elem(y)
    g, ux, vx = gcdx(x.gen_one, y.gen_one)
    if isone(g)
      z = O(ux*x.gen_one)
      @hassert :AbsNumFieldOrder 2 z in x
      @hassert :AbsNumFieldOrder 2 (1 - z) in y
      return z, 1 - z
    end
  end

  mx = minimum(x, copy = false)
  my = minimum(y, copy = false)

  g, ux, vy = gcdx(mx, my)
  if isone(g)
    z = O(ux*mx)
    @hassert :AbsNumFieldOrder 2 z in x
    @hassert :AbsNumFieldOrder 2 (1 - z) in y
    return z, 1 - z
  end
  return _idempotents_via_matrices(x, y)
end

function _idempotents_via_matrices(x::AbsNumFieldOrderIdeal, y::AbsNumFieldOrderIdeal)

  O = order(x)
  d = degree(O)
  mx = minimum(x, copy = false)
  my = minimum(y, copy = false)
  # form the matrix
  #
  # ( 1 |  1  | 0 )
  # ( 0 | M_x | I )
  # ( 0 | M_y | 0 )

  V = O.tidempotents

  u = coordinates(one(O))

  V[1, 1] = 1

  for i in 1:d
    V[1, i + 1] = u[i]
  end

  _copy_matrix_into_matrix(V, 2, 2, basis_matrix(x, copy = false))
  _copy_matrix_into_matrix(V, 2 + d, 2, basis_matrix(y, copy = false))

  for i in 1:d
    V[1 + i, d + 1 + i] = 1
  end

  H = hnf_modular_eldiv!(V, lcm(mx, my)) # upper right

  for i in 2:(1 + d)
    if H[1, i] != 0
      error("Ideals are not coprime")
    end
  end

  basisofx = basis(x, copy = false)

  aux = O()
  z = basisofx[1]*H[1, d + 2]
  for i in 2:d
    mul!(aux, basisofx[i], H[1, d + 1 + i])
    add!(z, z, aux)
  end

  @hassert :AbsNumFieldOrder 2 -z in x
  @hassert :AbsNumFieldOrder 2 1 + z in y

  ccall((:fmpz_mat_zero, libflint), Nothing, (Ref{ZZMatrix}, ), V)

  return -z, 1 + z
end

################################################################################
#
#  crt
#
################################################################################

@doc raw"""
    crt(r1::AbsSimpleNumFieldOrderElem, i1::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, r2::AbsSimpleNumFieldOrderElem, i2::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> AbsSimpleNumFieldOrderElem

Find $x$ such that $x \equiv r_1 \bmod i_1$ and $x \equiv r_2 \bmod i_2$
using `idempotents`.
"""
function crt(r1::S, i1::T, r2::S, i2::T) where { S <: Union{AbsSimpleNumFieldOrderElem, RelNumFieldOrderElem, AlgAssAbsOrdElem}, T <: Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal, AlgAssAbsOrdIdl} }
  u, v = idempotents(i1, i2)
  return r1*v + r2*u
end

function crt(a::Vector{S}, I::Vector{T}) where { S <: Union{AbsSimpleNumFieldOrderElem, RelNumFieldOrderElem, AlgAssAbsOrdElem}, T <: Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, RelNumFieldOrderIdeal, AlgAssAbsOrdIdl} }
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
    push!(B, I[end])
  end
  return crt(A, B)
end

################################################################################
#
#  Division
#
################################################################################

divexact(A::AbsNumFieldOrderIdeal, b::Integer; check::Bool=true) = divexact(A, ZZRingElem(b); check=check)

#TODO: write a divexact! to change the ideal?
#  difficult due to Julia's inability to unset entries...

function divexact(A::AbsNumFieldOrderIdeal, b::ZZRingElem; check::Bool=true)
  if iszero(A)
    return A
  end
  zk = order(A)
  b = abs(b)
  if has_2_elem(A)
    B = ideal(zk, divexact(A.gen_one, b; check=check), divexact(A.gen_two, b; check=check))
    if isdefined(A, :gens_normal)
      B.gens_normal = A.gens_normal
    end
    B.gens_weakly_normal = A.gens_weakly_normal
    if has_basis_matrix(A)
      B.basis_matrix = divexact(A.basis_matrix, b; check=check)
    end
    if false && has_basis_mat_inv(A)
      error("not defined at all")
      B.basis_mat_inv = b*A.basis_mat_inv
    end
  else
    B = ideal(zk, divexact(A.basis_matrix, b; check=check))
    if false && has_basis_mat_inv(A)
      error("not defined at all")
      B.basis_mat_inv = b*A.basis_mat_inv
    end
  end
  if has_minimum(A)
    B.minimum = divexact(A.minimum, b; check=check)
  end
  if has_norm(A)
    B.norm = divexact(A.norm, b^degree(zk); check=check)
  end
  if has_princ_gen(A)
    B.princ_gen = divexact(A.princ_gen, b; check=check)
  end
  #TODO princ_gen_special missing
  return B
end

function divexact(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, B::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}; check::Bool=true)
  check_parent(A, B)
  # It is assumed that B divides A, that is, A \subseteq B
  t_prod = 0.0
  t_simpl = 0.0
  t_b_mat = 0.0
  t_2_elem_weak = 0.0
  t_2_elem = 0.0

  if norm(A, copy = false) == norm(B, copy = false)
    return ideal(order(A), one(FlintZZ), order(A)(1))
  else
    t_prod += @elapsed I = A*inv(B)
    t_simpl += @elapsed simplify_exact!(I)
    #t_b_mat += @elapsed B = basis_matrix(I)
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

################################################################################
#
#  Extend/contract
#
################################################################################

function extend(A::AbsNumFieldOrderIdeal, O::AbsNumFieldOrder)
  if order(A) === O
    return A
  end
  # Assumes order(A) \subseteq O

  if iszero(A)
    B = ideal(O, zero_matrix(FlintZZ, degree(O), degree(O)))
    B.iszero = 1
    return B
  end

  d = degree(O)
  M = zero_matrix(FlintZZ, d^2, d)
  X = basis(O, copy = false)
  Y = map(O, basis(A, copy = false))
  t = O()
  for i = 1:d
    for j = 1:d
      mul!(t, X[i], Y[j])
      for k = 1:d
        M[(i - 1)*d + j, k] = coordinates(t, copy = false)[k]
      end
    end
  end
  M = sub(_hnf_modular_eldiv(M, minimum(A), :lowerleft), d*(d - 1) + 1:d^2, 1:d)
  return ideal(O, M; check=false, M_in_hnf=true)
end

*(A::AbsNumFieldOrderIdeal, O::AbsNumFieldOrder) = extend(A, O)
*(O::AbsNumFieldOrder, A::AbsNumFieldOrderIdeal) = extend(A, O)

function contract(A::AbsNumFieldOrderIdeal, O::AbsNumFieldOrder)
  if order(A) === O
    return A
  end
  # Assumes O \subseteq order(A)

  if iszero(A)
    B = ideal(O, zero_matrix(FlintZZ, degree(O), degree(O)))
    B.iszero = 1
    return B
  end

  d = degree(O)
  M = basis_matrix(FakeFmpqMat, O, copy = false)*basis_mat_inv(FakeFmpqMat, order(A), copy = false)
  @assert M.den == 1
  H = vcat(basis_matrix(A, copy = false), M.num)
  K = kernel(H, side = :left)
  M = view(K, 1:d, 1:d)*basis_matrix(A, copy = false)
  M = M*basis_matrix(FakeFmpqMat, order(A), copy = false)*basis_mat_inv(FakeFmpqMat, O, copy = false)
  @assert M.den == 1
  M = _hnf_modular_eldiv(M.num, minimum(A), :lowerleft)
  res = ideal(O, M; check=false, M_in_hnf=true)
  if A.is_prime == 1
    res.is_prime = 1
  end
  return res
end

intersect(O::AbsSimpleNumFieldOrder, A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) = contract(A, O)

intersect(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, O::AbsSimpleNumFieldOrder) = contract(A, O)
