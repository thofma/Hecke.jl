# missing in FinFld
# base_ring consistently
# rand
# creation with string, symbol, neither
# minpoly, charpoly
# order = size?
# solve behave consistently for rings and fields
#         do pseudo solve for extra den
#       if ring is known to be field, use field version
#       solve for matrix of NOT full rank
#       kernel
#       version that returns false rather than an error
#         alterntively: throw a very precise error object that
#         can be caught
# residueRing creation: rename generator to prefix with r or so
#
# Padic -> pAdic
# gen for residue_ring(Poly)


#################################################


# Plesken: a ordering on finite field elements and polynomials
# from his lecture notes.

function steinitz(a::zzModPolyRingElem)
  p = characteristic(base_ring(a))
  ZZx = polynomial_ring(FlintZZ)[1]
  #  f = lift(ZZx, a)  ## bloody stupid lift for poly uses symmetric residue
  f = [lift(coeff(a, i))::ZZRingElem for i=0:degree(a)]
  return Nemo.evaluate(ZZx(f), p)
end

function steinitz(a::ResElem{ZZRingElem})
  return lift(a)
end

function steinitz(a::ResElem{T}) where T <: Union{zzModPolyRingElem, fqPolyRepPolyRingElem, PolyRingElem}
  f = [steinitz(coeff(a.data, i))::ZZRingElem for i=0:degree(a.data)]
  ZZx = polynomial_ring(FlintZZ)[1]
  S = base_ring(base_ring(parent(a)))
  return evaluate(ZZx(f), size(S))
end

function steinitz(a::FqPolyRepFieldElem)
  st = 0
  p = characteristic(parent(a))
  for i=degree(parent(a))-1:-1:0
    st *=p
    st += coeff(a, i)
  end
  return st
end

function steinitz(a::fqPolyRepFieldElem)
  st = 0
  p = characteristic(parent(a))
  for i=degree(parent(a))-1:-1:0
    st *=p
    st += coeff(a, i)
  end
  return st
end

##############################################################
# this is expensive, but completely generic
# possibly improve by using the fact that aut should be an automorphism
# if the order of aut would be known, one could use this to proceed in layers
function minpoly_aut(a::ResElem{T}, aut :: Function) where T <: Union{fqPolyRepPolyRingElem, zzModPolyRingElem}
  R = parent(a)
  RX, X = polynomial_ring(R)
  o = Set{typeof(X)}()
  push!(o, X-a)
  a = aut(a)
  while !(X-a in o)
    push!(o, X-a)
    a = aut(a)
  end
  f = prod(collect(o))
  # now, the coefficients SHOULD be in a smaller ring, but we
  # don't have that ring
  return f
end

function minpoly_aut(a::ResElem{T}, aut :: Function) where T <: PolyRingElem
  R = parent(a)
  RX, X = polynomial_ring(R)
  o = Set{typeof(X)}()
  push!(o, X-a)
  a = aut(a)
  while !(X-a in o)
    push!(o, X-a)
    a = aut(a)
  end
  f = prod(collect(o))
  return f
end

function minpoly_pow(a::ResElem{T}, deg::Int) where T <: Union{PolyRingElem, fqPolyRepPolyRingElem}
  R = parent(a)
  S = base_ring(base_ring(R))
  M = matrix_space(S, deg, degree(R.modulus))()
  B = matrix_space(S, 1, degree(R.modulus))()
  elem_to_mat_row!(M, 1, one(R))
  b = a
  for i=1:deg-1
    elem_to_mat_row!(M, i+1, b)
    b *= a
  end
  elem_to_mat_row!(B, 1, -b)
  s = Nemo._solve_rational(M', B')
  if isa(s, Tuple)
    s = s[1] * inv(s[2])
  end
  ## just to keep the interface...
  Rx,x = polynomial_ring(R)
  arr = Vector{typeof(b)}(deg+1)
  for i=1:deg
    arr[i] = R(s[i, 1])  ## wasteful
  end
  arr[deg+1] = one(R)
  return Rx(arr)
end

###################################################################
###################################################################
###################################################################
##
##
##
##
## Plesken starting
##

function primitive_root_r_div_qm1(R, r::Int)
  #Plesken, 1.39 essentially
  n = size(R)-1
  k, e = remove(n, r)
  @assert k>0
  @assert is_prime(r)

  a = rand(R)^e
  while a==0 || a^(r^(k-1)) == 1
    a = rand(R)^e
  end
  #println("found one $r^$k-th root of one: $a")

  #level 1: need a^(r^(k-1))^l minimal, 0<l<r (so a stays primitive)
  b = a^(r^(k-1))
  c = b
  st = steinitz(b)
  opt = 1
  for i=2:r-1
    c *= b
    if steinitz(c) < st
      opt = i
      st = steinitz(c)
    end
  end
  a = a^opt
  #println("adjusted for level 1: ", a, " st: $st")
  for i=2:k
    #println("dealing with level $i")
    ## (a*a^(xr^(i-1)))^r^(k-i) needs to be minimal in the Steinitz sense
    ## a^(r^(k-i) + xr^k-1)
    # use a*a^(xr^(i-1)) as the new root
    b = a^(r^(k-1)) ## basically a r-th root
    c = a^(r^(k-i))
    opt = 0
    st = steinitz(c)
    for ii=1:r
      c *= b
      if steinitz(c) < st
        opt = ii
        st = steinitz(c)
      end
    end
    #println("adjusted for level $i: ", a, " st: $st")
    a = a*a^(opt*r^(i-1))
  end
  return a
end

function get_f(r::Int, p::ZZRingElem, s::Int)
  R = PadicField(r, s)
  return lift(teichmuller(R(p)))
end
# plan
# to get a field p^n, decompose n into prime powers and use compositum (missing)
# to get p^(r^l)
# find minimal k sth. r| p^k-1 and define F_(p^k)
#  in F_p^k find the proper root of 1 (using the primitive_root_r_div_qm1
#    function), cal this mu
# build x^r - mu and iterate l times
# descent: find f using get_f and form the trace relative to f
# to find generators for the degree r extension of F_p, not F_p^k
# needs minpoly in some variant...

function f_tr(a::ResElem, f::ZZRingElem, o::Int)
  s = a
  for i=1:o-1
    a = a^f
    s += a
  end
  return s
end

function plesken_kummer(p::ZZRingElem, r::Int, s::Int)
  #find Plesken rep for F_p^(r^s)
  @assert r%2 == 1
  @assert r!=p
  @assert is_prime(r) && is_prime(p)


  if (p-1) % r == 0
    R = finite_field(p)
    descent = false
  else
    f = cyclotomic(r, polynomial_ring(FlintZZ)[2])
    f = polynomial_ring(residue_ring(FlintZZ, p)[1])[1](f)
    f = factor(f)
    k = keys(f.fac)
    st = start(k)
    f1, st = next(k, st)
    st = steinitz(f1)
    opt = f1
    while !done(k, st)
      fi, st = next(k, st)
      if steinitz(fi) < st
        st = steinitz(fi)
        opt = fi
      end
    end
    descent = true
    ord = degree(opt)
    R = Native.finite_field(opt, "a")[1]
    T = residue_ring(FlintZZ, p)[1]
    J = CoerceMap(T, R)
  end
  zeta = primitive_root_r_div_qm1(R, r)

  a = zeta

  if descent
    f = get_f(r, p, s+4)  #+4 is stupid. Need to think
    #println("using $f as f")
    # a -> a^f should be an automorphism of order ord = degree of ext
  end

  S = 1
  U = 1
  for i=1:s ## maybe do one step x^(r^s)-a only?
    #println("doin' stuff")
    Rx, x = polynomial_ring(R, "x_$i")
    S = residue_ring(Rx, x^r-a)[1]
    I = CoerceMap(R, S)
    a = S(x)
    if descent
      b = f_tr(a, f, ord)
      #println("$i: trace of $a is $b")
#      pol = minpoly_aut(b, x->x^(p^(r^(i-1))))
      pol = minpoly_pow(b, r)  ## does not work: expo too large
      #println(pol)
      arr = Array{typeof(zero(T))}(degree(pol)+1)
      @assert domain(I) == codomain(J)
      @assert parent(coeff(pol, 0)) == codomain(I)
      for j=0:degree(pol)
        arr[j+1] = preimage(J, preimage(I, coeff(pol, j)))
      end
      pol = polynomial_ring(T, "t_$i")[1](arr)
      U = residue_ring(parent(pol), pol)[1]
      H = ResidueRingPolyMap(U, S, b, J)
      #H.coeff_map = J
      J = H
      T = U
    end
    R = S
  end

  return U, S
end

function plesken_as(p::ZZRingElem, r::Int, s::Int)
  @assert p==r
  R = finite_field(p)
  g = R(-1)
  t = 1
  while s>1
    Rx,x = polynomial_ring(R, "t_$i")
    R = residue_ring(Rx, x^r-x-g^(r-1))[1] ## r==p, but of better type
    g = gen(R)
    s -= 1
    t += 1
  end
  return R
end

function plesken_2(p::ZZRingElem, r::Int, s::Int)
  @assert r==2
  #Plesken, 1.27
  if valuation(p-1, 2) >1
    R = finite_field(p)
    g = primitive_root_r_div_qm1(p, r)
    t = 1
  else
    @assert valuation(p+1, 2)>1
    R = finite_field(p)
    Rx,x = polynomial_ring(R, "t_1")
    R = residue_ring(Rx, x^2+1)[1]
    g = primitive_root_r_div_qm1(R, 2)
    s -= 1
    t = 2
  end
  while s>0
    Rx,x = polynomial_ring(R, "t_$t")
    R = residue_ring(Rx, x^2-g)[1]
    g = gen(R)
    t += 1
  end
  return R
end

## missing:
# the composition for general r (proper order and such)
# choice or sum or product to generate field uniquely
#
# efficiency: those towers are slow (improved by different minpoly, Plesken
#               suggests a recursion to writem them down, based on the matrix)
#   one should probably collapse them as much as possibly
#   the rep is still unique (in prime power towers) as the
#   fields are cyclic: there are now subfields that will
#   combine to everything
#
#   direct version: the final elt in them kummer case is x^(r^s)-a
#   we can descent on this directly
#   same with 2
#   as is more involved (->Witt ring construction)
#
# maps & coercion
#
# the Log = canonical generator

function h_minus(p::Int, nb::Int)
  #void
  #fmpz_poly_resultant_modular_div(fmpz_t res, const fmpz_poly_t poly1,
  #              const fmpz_poly_t poly2, const fmpz_t divisor, slong nbits)

  #let g be a generator for Z/pZ^*, h = g^-1 mod p
  # F = sum_0^p-2 h^i x^i in Z[x]
  # h^- = ResidueRingElem(F, x^((p-1)/2)+1)/(2p)^((p-3)/2)
  #
  # log(2*p*(p/4/pi^2)*(p-1)/4/log(2)
  #
  # is the asymptotic size, so that's what nb should be


  Zx, x = polynomial_ring(FlintZZ)
  F = Vector{ZZRingElem}(p-1)

  g = rand(1:p-1)
  while modord(g, p) != p-1
    g = rand(1:p-1)
  end
  h = invmod(g, p)
  F[1] = 1
  for i=2:p-1
    F[i] = F[i-1]*h % p
  end
  F = Zx(F)

  f = (2*ZZRingElem(p))^div(p-3, 2)
  @time r1 = resultant(F, x^div(p-1, 2)+1, f, nb)
  @time r2 = resultant(F, x^div(p-1, 2)+1)
  return r1
end

