module MultDep

using Hecke
import Base.*

"""
Given A[i] elements in K, find matrices I and U s.th.
A^I is a basis for 
  <A[i] | i>/Units < K^*/Units
actually a sub-group of the S-unit group for a coprime base
generated from the elements in A.

A^U is a generating set for the relations:
  <A^U> < Units
and every u s.th. A^u is a unit is in the span of U

The coprime base is returned as well, the columns of I correspond to the 
ordeing of the base.
"""
function syzygies_sunits_mod_units(A::Vector{AbsSimpleNumFieldElem}; use_ge::Bool = false, max_ord::Union{Nothing, AbsSimpleNumFieldOrder}=nothing)
  k = parent(A[1])
  @assert all(i->parent(i) === k, A)
  if !use_ge
    if max_ord === nothing
      zk = maximal_order(k)
    else
      zk = max_ord
    end
    cp = coprime_base(A, zk)
  else
    cp = coprime_base(A)
  end
  sort!(cp, lt = (a,b) -> norm(a) > norm(b))
  M = sparse_matrix(ZZ)
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
    push!(M, sparse_row(ZZ, T))
  end
  h, t = Hecke.hnf_with_transform(matrix(M))
  h = h[1:rank(h), :]
  return t[1:nrows(h), :], t[nrows(h)+1:end, :], cp
  # THINK! do we want or not...
  # - M is naturally sparse, hence it makes sense
  # - for this application we need all units, hence the complete
  #   kernel - which is huge and dense...
  # - cp seems to not be used for anything afterwards. 
  #   It will be when we actually create the group, in the DiscLog
  h, t = Hecke.hnf_kannan_bachem(M, Val(true), truncate = true)
  return h, t, cp
end

#=
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
=#

#= For Ge's PhD
 - smallest common overorder (non-coprime case)
 - ideals in non-maximal orders with checking if the operation
   worked - if not automatically redoing with larger order
=#
function *(O1::AbsNumFieldOrder, O2::AbsNumFieldOrder)
  k = number_field(O1)
  @assert k === number_field(O2)
  b1 = basis(O1, k)
  n = length(b1)
  b2 = basis(O2, k)
  p = [x*y for (x,y) in Base.Iterators.ProductIterator((b1, b2))]
  d = reduce(lcm, [denominator(x) for x = p])
  M = zero_matrix(ZZ, n*n, n)
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
  return Hecke.order(k, b)
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
#XXX:  not sure if those 2 should get "exported", Ge does not seem to be 
#      overly fast....
#TODO: do an integer coprime base first, then refine. Possibly also do
#      a p-maximality for all p from the integer coprime base.
#TODO: find examples where Ge is useful
function coprime_base(A::Vector{AbsSimpleNumFieldElem})
  c = Vector{GeIdeal}()
  for a = A
    n,d = GeIdeal(a)
    isone(n) || push!(c, n)
    isone(d) || push!(c, d)
  end
  return Hecke.AbstractAlgebra.coprime_base_steel(c)
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

#TODO: don't use Gram Schidt over Q, use reals. If M is LLL, then
#      a low precision should be OK
#TODO: an interface to reduce several v
#TODO: a sane implementation that is more memory friendly (views, ...)
"""
reduce the rows of v modulo the lattice spanned by the rows of M.
M should be LLL reduced.
"""
function size_reduce(M::ZZMatrix, v::ZZMatrix)
  s = gram_schmidt_orthogonalisation(QQ.(transpose(M)))
  d = diagonal(transpose(s)*s)
  for i=1:nrows(v)
    for j=nrows(M):-1:1
      x = ZZ(round((v[i:i, :]* s[:, j:j]/d[j])[1,1]))
      v[i:i, :] -= x*M[j:j, :]
    end
  end
  return v
end

"""
A a vector of units in fac-elem form. Find matrices U and V s.th.
A^U is a basis for <A>/Tor 
and
A^V is a generating system for the relations of A in Units/Tor

The pAdic Ctx is returned as well  
"""
function syzygies_units_mod_tor(A::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}})
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
  C = Hecke.qAdicConj(K, p)
  la = transpose(matrix(conjugates_log(A[1], C, prec, all = false, flat = true)))
  lu = zero_matrix(base_ring(la), 0, n)
  uu = []
  indep = Int[]
  dep = Int[]
  for ia = 1:length(A)
    a = A[ia]
    while true
      @vtime :qAdic 1 la = transpose(matrix(conjugates_log(a, C, prec, all = false, flat = true)))
      if iszero(la)
        @vtime :qAdic 1 @hassert :qAdic 1 verify_gamma([a], [ZZRingElem(1)], ZZRingElem(p)^prec)
        @vprint :qAdic 1 println("torsion found")
        gamma = vcat([ZZ(0) for i=1:r+length(uu)], [ZZ(1)])
        push!(uu, (a, gamma))
        push!(dep, ia)
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
        @vprint :qAdic 1 "new independent unit found\n"
        push!(u, a)
        push!(indep, ia)
        lu = vcat(lu, la)
        @assert length(u) <= r
      else # length == 1 extend the module
        @vprint :qAdic 1 "dependent unit found, looking for relation\n"
        s = QQFieldElem[]
        for x in k[1, :]
          @vtime :qAdic 1 y = lift_reco(QQ, x, reco = true)
          if y === nothing
            prec *= 2
            @vprint :qAdic 1  "increase prec to ", prec
            lu = transpose(matrix([conjugates_log(x, C, prec, all = false, flat = true) for x = u]))
            break
          end
          push!(s, y)
        end
        if length(s) < ncols(k)
          continue
        end
        d = reduce(lcm, map(denominator, s))
        gamma = ZZRingElem[ZZ(x*d)::ZZRingElem for x = s]
        @assert reduce(gcd, gamma) == 1 # should be a primitive relation
        if !verify_gamma(push!(copy(u), a), gamma, ZZRingElem(p)^prec)
          prec *= 2
          @vprint :qAdic 1 "increase prec to ", prec
          lu = transpose(matrix([conjugates_log(x, C, prec, all = false, flat = true) for x = u]))
          continue
        end
        @assert length(gamma) == length(u)+1
        gamma = vcat(gamma[1:length(u)], [0 for i=length(u)+1:r+length(uu)], [gamma[end]])
        push!(uu, (a, gamma))
        push!(dep, ia)
      end
      break
    end
  end
  #=
    let u_1, .., u_n be units and
       <u_i | i> has rank s and
        r_i in Z^n be such that
          prod u_i^r_i = 1  (OK, sum of the logs is zero)
          rank <r_i | i> = s as well #wrong:
          #Input: u^2, u^3, u^7 in rank r = 2
          #U = [-3 0 2 0; -7 0 0 2]
    the r_i form a Q-generating basis for the relations.
    They are indep as they are growing in length (new columns per new element, non
    are torsion, so the final non-zero entries are moving right.)
    Essentially, the gamma of above are the r_i
    Let [H|0] = [r_i|i]*T be the hnf with trafo, so T in Gl(n, Z)
    Then
      <u_i|i> = <[u_i|i] T>
      [r_i|i] * [u_i|i]^t = 0 (by construction)
      [r_i|i] T inv(T) [u[i] | i] = 0
      Careful! H may not have full rank, hence the shape is different
      [H | 0]   [v_i | i] = 0
      so, since H is triangular(!!) v_1, ... v_n-s = 0
      and <u_i |i> = <v_n-s+1, ..., v_n>

    for the case of n=s+1 this is mostly the "normal" construction.
    Note: as a side, the relations do not have to be primitive.
      If they are, (and n=s+1), then H = 1
    We deal with that by saturation  
  =#

  for i=1:length(uu)-1
    append!(uu[i][2], zeros(ZZ, length(uu[end][2])-length(uu[i][2])))
  end
  if length(uu) == 0 #all torsion
    return [], A
  else
    U = matrix(ZZ, length(uu), length(uu[end][2]), reduce(vcat, [x[2] for x = uu]))
    U = hcat(U[:, 1:length(u)], U[:, r+1:ncols(U)])
  end

  U = saturate(U)
  
  _, U = hnf_with_transform(transpose(U))

  k = base_ring(A[1])
  
  U = inv(U)
  V = sub(U, 1:nrows(U), 1:ncols(U)-length(u)) #the torsion part
  U = sub(U, 1:nrows(U), ncols(U)-length(u)+1:ncols(U))
  #U can be reduced modulo V...
  V = lll(transpose(V))
  U = size_reduce(V, transpose(U))
  U = lll(U)

  #so basis is A[indep] cat A[dep] ^U
  #rels: A[tor], .. * V
  nt = zero_matrix(ZZ, length(A), length(A))
  for i=1:length(indep)
    nt[i, indep[i]] = 1
  end
  for i=1:length(dep)
    nt[i+length(indep), dep[i]] = 1
  end
#  @assert nt*matrix([collect(1:length(A))])  == matrix([vcat(indep, dep)])
  rel = V*nt
  return U*nt, rel, C
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
  p = Hecke.upper_bound(ZZRingElem, log(B)/log(parent(B)(2)))
  @vprint :qAdic 1  "using", p, nbits(v)*2
  b = conjugates_arb_log(t, max(-Int(div(p, 2)), 2))
#  @show B , sum(x*x for x = b), is_torsion_unit(t)[1]
  @hassert :qAdic 1 (B > sum(x*x for x = b)) == is_torsion_unit(t)[1]
  return B > sum(x*x for x = b)
end

"""
A padic number a is internally written as 
  p^v*u
for a unit u given in some precision.
This returns u, v and the precision
"""
function canonical_split(a::PadicFieldElem)
  u = ZZ()
  ccall((:fmpz_set, Hecke.libflint), Nothing, (Ref{ZZRingElem}, Ref{Int}), u, a.u)
  return u, a.v, a.N
end

#TODO: different name ...
function lift_reco(::QQField, a::PadicFieldElem; reco::Bool = false)
  if iszero(a)
    return QQ(0)
  end
  if reco
    u, v, N = canonical_split(a)
    R = parent(a)
    fl, c, d = rational_reconstruction(u, prime(R, N-v))
    !fl && return nothing

    x = QQ(c, d)
    if v < 0
      return x//prime(R, -v)
    else
      return x*prime(R, v)
    end
  else
    return lift(QQ, a)
  end
end

"""
Given torsion units A[i] in factored form, find a generator
for the group <A[i] |i> as well as a basis for the relations
"""
function syzygies_tor(A::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}})
  K = base_ring(parent(A[1]))
  bnd = Int(Hecke._torsion_group_order_divisor(K))
  #bnd is a multiple of the torsion in the field
  #so any residue field where bnd divides q-1 can be used to find the
  #relations, Tor is a subgroup of k^* in this case.
  O = any_order(K)
  #XXX: bad, but prime ideals in non-max orders seem a bit dodgy
  #     in particular extend_easy gives garbage
  #=
    k, a = wildanger_field(5,13);
    O = any_order(k);
    P = prime_ideals_over(O, 71)[1]
    F, mF = residue_field(O, P)
    mF(O(gen(k))) # => 25
    mmF = Hecke.extend_easy(mF, k);
    mmF(gen(k)) # => 70
    degree(P) # => 0
    P.prim_elem # => 21 but should be a root...
  =#

  O = maximal_order(K)
  for p = PrimesSet(bnd, -1, bnd, 1)
    if discriminant(O) % p == 0
      continue
    end
    P = prime_ideals_over(O, p)[1]
    if degree(P) > 1
      continue
    end
    F, mF = Hecke.ResidueFieldSmallDegree1(O, P)
    mF = Hecke.extend_easy(mF, K)
    a = try
      map(mF, A)
    catch e
      if isa(e, Hecke.BadPrime)
        #if some element in the base of the fac elems is not a unit mod P
        #use the next prime...
        continue
      end
      rethrow(e)
    end
    U, mU = unit_group(F)
    b = map(pseudo_inv(mU), a)
    B = free_abelian_group(length(A))
    h = hom(B, U, b)
    k, mk = kernel(h)
    i, mi = image(h)
    @assert ngens(i) == 1
    return preimage(h, mi(i[1])).coeff, vcat([mk(x).coeff for x = gens(k)]...), order(i[1])
  end
end

@doc raw"""
    syzygies(A::Vector{AbsSimpleNumFieldElem}) -> ZZMatrix

Given non-zero elements A[i] in K, find a basis for the relations, returned
  as a matrix.
"""
function syzygies(A::Vector{AbsSimpleNumFieldElem}; use_ge::Bool = false, max_ord::Union{Nothing, AbsSimpleNumFieldOrder} = nothing)
  _, t, _ = syzygies_sunits_mod_units(A; use_ge, max_ord)
  u = [FacElem(A, t[i, :]) for i = 1:nrows(t)]
  _, tt = syzygies_units_mod_tor(u)
  u = Hecke._transform(u, transpose(tt))
  _, ttt, _ = syzygies_tor(u)
  return ttt*tt*t
end

@doc raw"""
    multiplicative_group(A::Vector{AbsSimpleNumFieldElem}) -> FinGenAbGroup, Map

Return the subgroup of the multiplicative group of the number field generated 
by the elements in `A` as an abstract abelian group together with a map
mapping group elements to number field elements and vice-versa.
"""
function Hecke.multiplicative_group(A::Vector{AbsSimpleNumFieldElem}; use_ge::Bool = false, max_ord::Union{Nothing, AbsSimpleNumFieldOrder} = nothing, task::Symbol = :all)

  S, T, cp = syzygies_sunits_mod_units(A; use_ge, max_ord)
  u = [FacElem(A, T[i, :]) for i = 1:nrows(T)]
  g1 = [FacElem(A, S[i, :]) for i = 1:nrows(S)] #gens for mult grp/ units
  
  U, T, C = syzygies_units_mod_tor(u)
  g2 = Hecke._transform(u, transpose(U))
  u = Hecke._transform(u, transpose(T))

  Ut, _, o = syzygies_tor(u)

  t = evaluate(Hecke._transform(u, transpose(Ut))[1])

  G = abelian_group(vcat([0 for i=1:length(g1)+length(g2)], [o]))
  g = vcat(g1, g2, [FacElem(t)])

  function im(a::FinGenAbGroupElem)
    @assert parent(a) == G
    return prod(g[i]^a[i] for i = 1:length(g))
  end

  local log_mat::Union{Generic.MatSpaceElem{PadicFieldElem}, Nothing} = nothing
  local prec::Int = 20
  local gamma::Vector{ZZRingElem}

  function pr(a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})
    @assert base_ring(parent(a)) == parent(A[1])
    c = ZZRingElem[]
    for i=1:length(cp)
      v = valuation(a, cp[i])
      push!(c, divexact(v, valuation(g1[i], cp[i])))
      a *= g1[i]^-c[end]
    end

    if log_mat === nothing
      log_mat = matrix([conjugates_log(x, C, prec, all = false, flat = true) for x = g2])
    end
    while true
      log_a = matrix([conjugates_log(a, C, prec, all = false, flat = true)])

      lv = vcat(log_mat, log_a)
      #check_precision and change
      @vtime :qAdic 1 k = kernel(lv, side = :left)

      @assert nrows(k) < 2
      if nrows(k) == 0
        error("not in the image")
      else # length == 1 extend the module
        @vprint :qAdic 1 "looking for relation\n"
        s = QQFieldElem[]
        for x in k[1, :]
          @vtime :qAdic 1 y = lift_reco(QQ, x, reco = true)
          if y === nothing
            prec *= 2
            @vprint :qAdic 1  "increase prec to ", prec
            log_mat = transpose(matrix([conjugates_log(x, C, prec, all = false, flat = true) for x = g2]))
            break
          end
          push!(s, y)
        end
        if length(s) < ncols(k)
          continue
        end
        d = reduce(lcm, map(denominator, s))
        gamma = ZZRingElem[ZZ(x*d)::ZZRingElem for x = s]
        @assert reduce(gcd, gamma) == 1 # should be a primitive relation
        if !verify_gamma(push!(copy(g2), a), gamma, prime(base_ring(log_mat), prec))
          prec *= 2
          @vprint :qAdic 1 "increase prec to ", prec
          log_mat = transpose(matrix([conjugates_log(x, C, prec, all = false, flat = true) for x = g2]))
          continue
        end
        @assert length(gamma) == length(g2)+1
        break
      end
    end
    for i=1:length(gamma)-1
      push!(c, divexact(gamma[i], -gamma[end]))
    end
    _, _c, _ = syzygies_tor(typeof(a)[g[end], a*prod(g2[i]^-gamma[i] for i=1:length(gamma)-1)])

    push!(c, divexact(_c[1,1], _c[1,2]))
    return G(c)
  end
  return G, MapFromFunc(G, parent(g1[1]), im, pr)
end

export syzygies

end

using .MultDep


