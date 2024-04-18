module MultDep

using Hecke
import Base.*

function multiplicative_group_mod_units_fac_elem(A::Vector{AbsSimpleNumFieldElem}; use_max_ord::Bool = false)
  k = parent(A[1])
  @assert all(i->parent(i) === k, A)
  if use_max_ord
    zk = maximal_order(k)
    cp = coprime_base(A, zk)
  else
    cp = coprime_base(A)
  end
  sort!(cp, lt = (a,b) -> norm(a) > norm(b))
  M = sparse_matrix(FlintZZ)
  for a = A
    T = Tuple{Int, ZZRingElem}[]
    for i = 1:length(cp)
      p = cp[i]
      v = valuation(a, p)
      if v != 0
        push!(T, (i, ZZRingElem(v)))
      end
#      isone(I) && break
    end
    push!(M, sparse_row(FlintZZ, T))
  end
  h, t = Hecke.hnf_kannan_bachem(M, Val(true), truncate = true)
  return h, t, cp
end

function units(h::SMat, t, b::Vector{AbsSimpleNumFieldElem})
  u = FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[]
  for i=nrows(h)+1:length(b)
    k = [ZZRingElem(0) for i=b]
    k[i] = 1
    for i in length(t):-1:1
      Hecke.apply_right!(k, t[i])
    end
    push!(u, FacElem(b, k))
  end
  return u
end

function unit_group_mod_torsion_fac_elem(O::AbsNumFieldOrder, u::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}})
  U = Hecke._unit_group_init(O)
  s = signature(O)
  r = s[1] + s[2] - 1
  for y = u
    is_tors, p = is_torsion_unit(y, false, U.tors_prec)
    U.tors_prec = max(p, U.tors_prec)
    if is_tors
      continue
    end
    Hecke._add_unit(U, y)
    if length(U.units) >= r
      break
    end
  end
  if length(U.units) < r
    # maybe use pAdic stuff here...
    error("not complete yet")
  end

  U.full_rank = true

  U.units = Hecke.reduce(U.units, U.tors_prec)

  for y = u
    is_tors, p = is_torsion_unit(y, false, U.tors_prec)
    U.tors_prec = max(p, U.tors_prec)
    if is_tors
      continue
    end
    x = Hecke.reduce_mod_units([y], U)[1]
    is_tors, p = is_torsion_unit(x, false, U.tors_prec)
    U.tors_prec = max(p, U.tors_prec)
    if is_tors
      continue
    end
    Hecke._add_dependent_unit(U, x)
  end
  return U
end

function *(O1::AbsNumFieldOrder, O2::AbsNumFieldOrder)
  k = nf(O1)
  @assert k === nf(O2)
  b1 = basis(O1, k)
  n = length(b1)
  b2 = basis(O2, k)
  p = [x*y for (x,y) in Base.Iterators.ProductIterator((b1, b2))]
  d = reduce(lcm, [denominator(x) for x = p])
  M = zero_matrix(FlintZZ, n*n, n)
  z = ZZRingElem()
  for i = 1:n*n
    a = p[i]*d
    Hecke.elem_to_mat_row!(M, i, z, a)
  end
  h = hnf(M)
  b = AbsSimpleNumFieldElem[]
  for i=1:n
    push!(b, Hecke.elem_from_mat_row(k, h, i, d))
  end
  return Hecke.Order(k, b)
end

mutable struct GeIdeal
  a::AbsNumFieldOrderIdeal
  function GeIdeal(a::AbsNumFieldOrderIdeal)
    o =order(a)
    if o.is_maximal == 1
      return new(a)
    end
    #keep track of known maximality and use this to speed things up
    o = ring_of_multipliers(a)
    if o === order(a)
      return new(a)
    else
      return new(extend(a, o))
    end
  end
  function GeIdeal(a::AbsSimpleNumFieldElem)
    o = Hecke.any_order(parent(a))
    d = denominator(a, o)
    return new(o(a*d)*o), new(o(d)*o)
  end
end

import Hecke.gcd, Hecke.isone, Hecke.*, Hecke.gcd_into!, Hecke.copy, Hecke.divexact,
       Hecke.is_unit, Hecke.coprime_base, Hecke.valuation

function make_compatible!(a::GeIdeal, b::GeIdeal)
  o1 = order(a.a)
  o2 = order(b.a)
  if o1 === o2
    return
  end
  o = o1*o2
  a.a = extend(a.a, o)
  b.a = extend(b.a, o)
end

#is_unit, divexact, gcd, isone, *, gcd_into!, copy
isone(a::GeIdeal) = isone(a.a)
is_unit(a::GeIdeal) = isone(a)
copy(a::GeIdeal) = GeIdeal(a.a)

function gcd(a::GeIdeal, b::GeIdeal)
  make_compatible!(a, b)
  return GeIdeal(a.a + b.a)
end

function gcd_into!(a::GeIdeal, b::GeIdeal, c::GeIdeal)
  make_compatible!(b, c)
  a.a = b.a + c.a
  return a
end

function *(a::GeIdeal, b::GeIdeal)
  make_compatible!(a, b)
  return GeIdeal(a.a * b.a)
end

function divexact(a::GeIdeal, b::GeIdeal; check::Bool=true)
  make_compatible!(a, b)
  return GeIdeal(divexact(a.a, b.a; check=check))
end

Hecke.norm(a::GeIdeal) = norm(a.a)

function coprime_base(A::Vector{AbsSimpleNumFieldElem})
  c = Vector{GeIdeal}()
  for a = A
    n,d = GeIdeal(a)
    isone(n) || push!(c, n)
    isone(d) || push!(c, d)
  end
  return coprime_base(c)
end

function coprime_base(A::Vector{AbsSimpleNumFieldElem}, O::AbsNumFieldOrder)
  c = Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
  for a = A
    n,d = integral_split(a*O)
    isone(n) || push!(c, n)
    isone(d) || push!(c, d)
  end
  return coprime_base(c)
end


function valuation(a::AbsSimpleNumFieldElem, p::GeIdeal)
  return valuation(a, p.a)
end


function mult_syzygies_units(A::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}})
  p = next_prime(100)
  K = base_ring(parent(A[1]))
  m = maximum(degree, keys(factor(GF(p), K.pol).fac))
  while m > 4
    p = next_prime(p)
    m = maximum(degree, keys(factor(GF(p), K.pol).fac))
  end
         #experimentally, the runtime is dominated by log
  u = FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[]
  prec = 10

  r1, r2 = signature(K)
  r = r1+r2 -1
  n = degree(K)
  C = qAdicConj(K, p)
  la = matrix(conjugates_log(A[1], C, prec, all = false, flat = true))'
  lu = zero_matrix(base_ring(la), 0, n)
  uu = []
  for a = A
    while true
      @vtime :qAdic 1 la = matrix(conjugates_log(a, C, prec, all = false, flat = true))'
      if iszero(la)
        @vtime :qAdic 1 @hassert :qAdic 1 verify_gamma([a], [ZZRingElem(1)], ZZRingElem(p)^prec)
        @vprint :qAdic 1 println("torsion found")
        break
      end
      lv = vcat(lu, la)
      #check_precision and change
      if false && any(x->precision(x) < prec, lv)
        println("loss of precision - not sure what to do")
        for i=1:rows(lv)
          for j = cols(lv) #seems to not do anything
            lv[i, j] = setprecision(lv[i, j], min_p)
            @assert precision(lv[i,j]) == min_p
          end
        end
      end
      @vtime :qAdic 1 k = kernel(lv, side = :left)
      @assert nrows(k) < 2
      if nrows(k) == 0
        println("new ")
        push!(u, a)
        lu = vcat(lu, la)
        @assert length(u) <= r
      else # length == 1 extend the module
        s = QQFieldElem[]
        for x in k[1, :]
          @vtime :qAdic 1 y = lift_reco(FlintQQ, x, reco = true)
          if y === nothing
            prec *= 2
            @vprint :qAdic 1  "increase prec to ", prec
            lu = matrix([conjugates_log(x, C, prec, all = false, flat = true) for x = u])'
            break
          end
          push!(s, y)
        end
        if length(s) < ncols(k)
          continue
        end
        d = reduce(lcm, map(denominator, s))
        gamma = ZZRingElem[FlintZZ(x*d)::ZZRingElem for x = s]
        @assert reduce(gcd, gamma) == 1 # should be a primitive relation
        @time if !verify_gamma(push!(copy(u), a), gamma, ZZRingElem(p)^prec)
          prec *= 2
          @vprint :qAdic 1 "increase prec to ", prec
          lu = matrix([conjugates_log(x, C, prec, all = false, flat = true) for x = u])'
          continue
        end
        @assert length(gamma) == length(u)+1
        gamma = vcat(gamma[1:length(u)], [0 for i=length(u)+1:r+length(uu)], [gamma[end]])
        push!(uu, (a, gamma))
      end
      break
    end
  end
  #=
    let u_1, .., u_n be units and
       <u_i | i> has rank s and
        r_i in Z^n be such that
          prod u_i^r_i = 1  (OK, sum of the logs is zero)
          rank <r_i | i> = s as well
    so the r_i form a Q-basis for the relations.
    Essentially, the gamma of above are the r_i
    Let [H|0] = [r_i|i]*T be the hnf with trafo, so T in Gl(n, Z)
    Then
      <u_i|i> = <[u_i|i] T>
      [r_i|i] * [u_i|i]^t = 0 (by construction)
      [r_i|i] T inv(T) [u[i] | i] = 0
      [H | 0]   [v_i | i] = 0
      so, since H is triangular(!!) v_1, ... v_n-s = 0
      and <u_i |i> = <v_n-s+1, ..., v_n>

    for the case of n=s+1 this is mostly the "normal" construction.
    Note: as a side, the relations do not have to be primitive.
      If they are, (and n=s+1), then H = 1
  =#

  for i=1:length(uu)-1
    append!(uu[i][2], zeros(FlintZZ, length(uu[end][2])-length(uu[i][2])))
  end
  if length(uu) == 0
    U = matrix(FlintZZ, length(uu), length(uu[end][2]), reduce(vcat, [x[2] for x = uu]))
  else
    U = matrix(FlintZZ, length(uu), length(uu[end][2]), reduce(vcat, [x[2] for x = uu]))
  end
  _, U = hnf_with_transform(U')
  if false
    U = inv(U)
    V = sub(U, 1:rows(U), 1:cols(U)-length(u))
    U = sub(U, 1:rows(U), cols(U)-length(u)+1:cols(U))
    #U can be reduced modulo V...
    Z = zero_matrix(FlintZZ, cols(V), cols(U))
    I = identity_matrix(FlintZZ, cols(U)) * p^(2*prec)
    k = base_ring(A[1])
    A = [ Z V'; I U']
    l = lll(A)
    U = sub(l, cols(V)+1:rows(l), cols(U)+1:cols(l))
    U = lll(U)
  else
    U = lll(U')
  end
  return Hecke._transform(vcat(u, FacElem{AbsSimpleNumFieldElem,AbsSimpleNumField}[FacElem(k(1)) for i=length(u)+1:r], [x[1] for x = uu]), U')
end

function verify_gamma(a::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}, g::Vector{ZZRingElem}, v::ZZRingElem)
  #knowing that sum g[i] log(a[i]) == 0 mod v, prove that prod a[i]^g[i] is
  #torsion
  #= I claim N(1-a) > v^n for n the field degree:
   Let K be one of the p-adic fields involved, set b = a^g
   then log(K(b)) = 0 (v = p^l) by assumption
   so val(log(K(b))) >= l, but
   val(X) = 1/deg(K) val(norm(X)) for p-adics
   This is true for all completions involved, and sum degrees is n
 =#

  t = prod([a[i]^g[i] for i=1:length(a)])
  # t is either 1 or 1-t is large, norm(1-t) is div. by p^ln
  #in this case T2(1-t) is large, by the arguments above: T2>= (np^l)^2=:B
  # and, see the bottom, \|Log()\|_2^2 >= 1/4 arcosh((B-2)/2)^2
  B = ArbField(nbits(v)*2)(v)^2
  B = 1/2 *acosh((B-2)/2)^2
  p = Hecke.upper_bound(log(B)/log(parent(B)(2)), ZZRingElem)
  @vprint :qAdic 1  "using", p, nbits(v)*2
  b = conjugates_arb_log(t, max(-Int(div(p, 2)), 2))
#  @show B , sum(x*x for x = b), is_torsion_unit(t)[1]
  @hassert :qAdic 1 (B > sum(x*x for x = b)) == is_torsion_unit(t)[1]
  return B > sum(x*x for x = b)
end

function lift_reco(::QQField, a::PadicFieldElem; reco::Bool = false)
  if reco
    u, v, N = getUnit(a)
    R = parent(a)
    fl, c, d = rational_reconstruction(u, prime(R, N-v))
    !fl && return nothing

    x = FlintQQ(c, d)
    if v < 0
      return x//prime(R, -v)
    else
      return x*prime(R, v)
    end
  else
    return lift(FlintQQ, a)
  end
end

Hecke.number_of_rows(A::Matrix{T}) where {T} = size(A)[1]
Hecke.number_of_columns(A::Matrix{T}) where {T} = size(A)[2]

