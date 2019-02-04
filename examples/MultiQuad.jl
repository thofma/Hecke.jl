module MultiQuad
using Hecke

function number_of_subgroups(p::Int, n::Int)
  @assert isprime(p)
  G = fmpz[1,2]
  pn = fmpz(p)
  for i=2:n
    push!(G, 2*G[i] + (pn -1)*G[i-1])
    pn *= p
  end
  return G[end]
end


function _combine(f::fmpq_poly, g::fmpq_poly, Qxy)
  Qx = parent(f)
  x = gen(Qx)
  y = gen(Qxy)
  f1 = f(x+y)
  f2 = g(y)
  return resultant(f1, f2)
end

function multi_quad_with_aut(d::Array{fmpz, 1})
  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  Qxy, y = PolynomialRing(Qx, "y", cached = false)
  lp = [ NumberField(x^2-a)[1] for a = d]
  aut = [ [gen(x), -gen(x)] for x = lp]
  while length(lp) > 1
    ld = []
    lau = []
    for i=1:div(length(lp), 2)
      K, m1, m2 = compositum(lp[2*i-1], lp[2*i])
      @assert m1(gen(lp[2*i-1])) + m2(gen(lp[2*i])) == gen(K)
      au = [m1(x) + m2(y) for x = aut[2*i-1] for y = aut[2*i]]
      push!(ld, K)
      push!(lau, au)
    end
    if isodd(length(lp))
      push!(ld, lp[end])
      push!(lau, aut[end])
    end
    lp = ld
    aut = lau
  end
  return lp[1], aut[1]
end

function multi_quad_with_emb(d::Array{fmpz, 1})
  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  Qxy, y = PolynomialRing(Qx, "y", cached = false)
  lp = [ NumberField(x^2-a)[1] for a = d]
  aut = [ [gen(x)] for x = lp]
  while length(lp) > 1
    ld = []
    lau = []
    for i=1:div(length(lp), 2)
      K, m1, m2 = compositum(lp[2*i-1], lp[2*i])
      push!(ld, K)
      push!(lau, vcat([ m1(x) for x = aut[2*i-1]], [ m2(x) for x = aut[2*i]]))
    end
    if isodd(length(lp))
      push!(ld, lp[end])
      push!(lau, aut[end])
    end
    lp = ld
    aut = lau
  end
  return lp[1], aut[1]
end

function multi_quad(d::Array{fmpz, 1}, B::Int)
  K, rt = multi_quad_with_emb(d)

  b = [K(1)]
  bb = [K(1)]
  for i = 1:length(d)
    if (d[i] < 0 && d[i] % 4 == -3) || (d[i] > 0 && d[i] % 4 == 1)
      o = (1+rt[i])//2
    else
      o = rt[i]
    end
    append!(b, Ref(o) .* b)
    append!(bb, Ref(rt[i]) .* bb)
  end

  all_d = fmpz[1]
  for i = d
    append!(all_d, Ref(i) .* all_d)
  end

  # @show all_d

  ZK = Order(K, b)
  ZK = pmaximal_overorder(ZK, fmpz(2))
  ZK.ismaximal = 1
  Hecke._set_maximal_order_of_nf(K, ZK)

  c = Hecke.class_group_init(ZK, B, complete = false, add_rels = false, min_size = 0)
  cp = Set(minimum(x) for x = c.FB.ideals)
  t_ord = 0
  local t_u

  Zx, x = FlintZZ["x"]

  for i = 2:length(all_d)
    k, a = number_field(x^2-all_d[i], cached = false)
    zk = maximal_order(k)
    class_group(zk)
    lp = prime_ideals_up_to(zk, Int(B), complete = false, degree_limit = 1)
    #only need split primes ...
    lp = [ x for x = lp if minimum(x) in cp]
    @assert all(x->minimum(x) == norm(x), lp)  
    if length(lp) > 0
      S, mS = Hecke.sunit_group_fac_elem(lp)
    else
      S, mS = Hecke.unit_group_fac_elem(zk)
    end
    h = Hecke.NfToNfMor(k, K, bb[i])
    @assert bb[i]^2 == all_d[i]

    for i=2:ngens(S) # don't need torsion here - it's the "same" everywhere
      u = mS(S[i])  #do compact rep here???
      u = Hecke.compact_presentation(u, 2, decom = Dict((P, valuation(u, P)) for P = lp))
      Hecke.class_group_add_relation(c, FacElem(Dict((h(x), v) for (x,v) = u.fac)))
    end
    if t_ord < order(S[1])
      t_ord = order(S[1])
      t_u = FacElem(Dict((h(x), v) for (x,v) = mS(S[1]).fac))
    end
  end
  zeta = evaluate(t_u)
  z_all = [K(1)]
  for i=1:t_ord-1
    push!(z_all, z_all[end]*zeta)
  end
  Hecke._set_nf_torsion_units(K, (z_all, zeta))

  return c
end

function dlog(dl::Dict, x, p::Int) 
  if iszero(x)
    throw(Hecke.BadPrime(1))
  end
  if haskey(dl, x)
    return dl[x]
  end
#  println("difficult for ", parent(x))
  i = 2
  y = x*x
  while !haskey(dl, y)
    y *= x
    i += 1
    @assert i <= p
  end
  #OK: we know x^i = g^dl[y] (we don't know g)
  v = dl[y]
  g = gcd(p, i)
  r = div(p, g)
  @assert v % g == 0
  e = invmod(div(i, g), r)*div(v, g) % r
  if e == 0
    e = r
  end
  dl[x] = e
  y = x*x
  f = (e*2) % p
  while !isone(y)
    if haskey(dl, y)
      @assert dl[y] == f
    end
    dl[y] = f
    y *= x
    f = (f+e) % p
  end
  g = [ a for (a,b) = dl if b == 1]
  @assert length(g) == 1
  @assert g[1]^dl[x] == x
  return dl[x]
end

function Hecke.matrix(R::Hecke.Ring, M::MatElem)
  return matrix(R, nrows(M), ncols(M), elem_type(R)[R(M[i,j]) for i=1:nrows(M) for j=1:ncols(M)])
end

function _nullspace(A::nmod_mat)
  A_orig = A
  p = fmpz(A.n)
  if isprime(p)
    return nullspace(A)
  end
  A = A'
  R = base_ring(A)
  r = nrows(A)
  c = ncols(A)
  A = hcat(A, identity_matrix(R, nrows(A)))
  A = vcat(A, zero_matrix(R, ncols(A) - nrows(A), ncols(A)))

  howell_form!(A)
  i = nrows(A)
  while iszero(A[i, :])
    i -= 1
  end
  r = i
  while i>0 && iszero(A[i:i, 1:c])
    i-= 1
  end
  if i < nrows(A)
    if i<r
      A = sub(A, i+1:r, c+1:ncols(A))
    else
      A = zero_matrix(base_ring(A), 0, ncols(A)-c)
    end
  else
    A = sub(A, i:r, c+1:ncols(A))
  end  
  A = A'
  @assert iszero(A_orig * A)
  for i = keys(factor(p).fac)
    if valuation(p, i) > 1
      continue
    end
    b = matrix(ResidueRing(FlintZZ, Int(i)), A_orig)
    b = nullspace(b)
    b = rref(b[1]')
    c = matrix(base_ring(b[2]), A)'
    c = rref(c)
    if c[1] != b[1]
      global bla
      bla = A_orig, A, c, b
    end
    @assert c[1] == b[1]
  end
  return ncols(A), A
end

function mod_p(R, Q::NfOrdIdl, p::Int)
  F, mF = Hecke.ResidueFieldSmall(order(Q), Q)
  mF = Hecke.extend_easy(mF, nf(order(Q)))
  @assert size(F) % p == 1
  pp,e = Hecke.ppio(Int(size(F)-1), p)
#  @show pp, e, p
  dl = Dict{elem_type(F), Int}()
  dl[F(1)] = 0
#  #=
  lp = factor(p)
  while true
    x = rand(F)
    if iszero(x)
      continue
    end
    x = x^e
    if any(i-> x^div(pp, Int(i)) == 1, keys(lp.fac))
      continue
    else
      dlog(dl, x, pp)
      @assert length(dl) == pp
      break
    end
  end
#  =#
  return matrix(ResidueRing(FlintZZ, p), 1, length(R), [dlog(dl, mF(x)^e, pp) % p for x = R])
end

Hecke.lift(A::fmpz_mat) = A
#Lorenz: does not work for 8|n in general...
function saturate_exp(c::Hecke.ClassGrpCtx, p::Int, stable = 1.5)
  # p does NOT have to be a prime!!!

  ZK = order(c.FB.ideals[1])
  T = torsion_unit_group(ZK)[1]
  sT = Int(length(T))


  R = vcat(c.R_gen, c.R_rel)
  K = nf(ZK)
  _, zeta = Hecke._get_nf_torsion_units(K)
  if !(hash(zeta) in c.RS)
    #println("adding zeta = ", zeta)
    push!(R, zeta)
  else
    #println("NOT doint zeta")
  end
  T = ResidueRing(FlintZZ, p)
  A = identity_matrix(T, length(R))
  i = 1
  for (up, k) = factor(p).fac
    if sT % Int(up) == 0
      all_p = [up^i for i=1:k]
    else
      all_p = [up^k]
    end
    #@show all_p
    AA = identity_matrix(FlintZZ, ncols(A))
    for pp = all_p
      #println("doin' $pp")
      AA = matrix(ResidueRing(FlintZZ, Int(pp)), lift(AA))
      Ap = matrix(base_ring(AA), A)
      i = 1
      S = Hecke.PrimesSet(Hecke.p_start, -1, Int(pp), 1)
      cAA = ncols(AA)
      for q in S
        if isindex_divisor(ZK, q)
          continue
        end
        if discriminant(ZK) % q == 0
          continue
        end
        #if gcd(div(q-1, Int(pp)), pp) > 1 # not possible if cond(k) is involved
        #  continue
        #end
        lq = prime_decomposition(ZK, q, 1)
        if length(lq) == 0
          continue
        end
        for Q in lq
          try
            z = mod_p(R, Q[1], Int(pp))
            z = z*Ap
            z = _nullspace(z)
            B = hcat(AA, sub(z[2], 1:nrows(z[2]), 1:z[1]))
            B = _nullspace(B)
            AA = AA*sub(B[2], 1:ncols(AA), 1:B[1])
            if !isprime(p)
              AA = AA'
              if nrows(AA) < ncols(AA)
                AA = vcat(AA, zero_matrix(base_ring(AA), ncols(AA) - nrows(AA), ncols(AA)))
              end
              howell_form!(AA)
              local i = nrows(AA)
              while i>0 && iszero(AA[i, :])
                i -= 1
              end
              AA = sub(AA, 1:i, 1:ncols(AA))'
            else
              @assert rank(AA') == ncols(AA)
            end  
#            @show cAA, pp, q, size(AA)
            if cAA == ncols(AA) 
              break #the other ideals are going to give the same info
                    #for multi-quad as the field is normal
            end        
          catch e
            @show "BadPrime"
            if !isa(e, Hecke.BadPrime)
              rethrow(e)
            end
          end
        end
        if cAA == ncols(AA) 
          #println("good $i")
          i += 1
        else
          #println("bad")
          i = 0
        end
        cAA = ncols(AA)
        if i> stable*ncols(AA)
          break
        end
      end
    end
    pp = Int(modulus(base_ring(AA)))
    #@show "done $pp"
    # A is given mod p, AA mod pp
    #we need AA mod p where the lift is any lift, modulo powers of pp
    #                                   identity modulo coprime (CRT)
    q, w = Hecke.ppio(p, pp) # q is a "power" of pp and w is coprime
    g, e, f = gcdx(q, w)
    AA = AA'
    AA = vcat(AA, zero_matrix(base_ring(AA), ncols(AA) - nrows(AA), ncols(AA)))
    strong_echelon_form!(AA)

    X  = similar(AA)
    for j=1:min(nrows(X), ncols(X))
      X[j,j] = 1
    end
    _A = matrix(base_ring(A), e*q*lift(X) + f*w*lift(AA))
    A = _A*A'
    howell_form!(A)
    i = nrows(A)
    while iszero(A[i, :])
      i -= 1
    end
    A = sub(A, 1:i, 1:ncols(A))'
    #@show size(A)
  end
  return A
end

fe(a::FacElem) = a
fe(a::nf_elem) = FacElem(a)

function elems_from_sat(c::Hecke.ClassGrpCtx, z)
  res = []
  fac = []
  for i=1:ncols(z)
    a = fe(c.R_gen[1])^FlintZZ(z[1, i])
    b = FlintZZ(z[1, i]) * c.M.bas_gens[1]
    for j=2:length(c.R_gen)
      a *= fe(c.R_gen[j])^FlintZZ(z[j, i])
      b += FlintZZ(z[j, i]) * c.M.bas_gens[j]
    end
    for j=1:length(c.R_rel)
      a *= fe(c.R_rel[j])^FlintZZ(z[j + length(c.R_gen), i])
      b += FlintZZ(z[j + length(c.R_gen), i]) * c.M.rel_gens[j]
    end

    push!(res, (a, b))
  end
  return res
end

function saturate(c::Hecke.ClassGrpCtx, n::Int, stable = 3.5)
  e = matrix(FlintZZ, saturate_exp(c, n%8 == 0 ? 2*n : n, stable))
  se = sparse_matrix(e)'

  A = sparse_matrix(FlintZZ)
  K = nf(c)
  _, zeta = Hecke._get_nf_torsion_units(K)

  #println("Enlarging by $(ncols(e)) elements")
  n_gen = []
  for i=1:ncols(e)
    r = e[:, i]
    g = content(r)
    g = gcd(g, n)
    divexact!(r, r, g)
#    g == 1 || println("non triv. content $g in ", e[:, i])  
    a = fe(c.R_gen[1])^r[1, 1]
    fac_a = r[1, 1] * c.M.bas_gens[1]
    for j = 2:length(c.R_gen)
      a *= fe(c.R_gen[j])^r[j, 1]
      fac_a += r[j, 1] * c.M.bas_gens[j]
    end
    for j=1:length(c.R_rel)
      a *= fe(c.R_rel[j])^r[j + length(c.R_gen), 1]
      fac_a += r[j + length(c.R_gen), 1] * c.M.rel_gens[j]
    end
    if nrows(e) > length(c.R_gen) + length(c.R_rel)
      @assert length(c.R_gen) + length(c.R_rel) + 1 == nrows(e)
      a *= fe(zeta)^r[nrows(e), 1]
    end
    
    decom = Dict((c.FB.ideals[k], v) for (k,v) = fac_a)
    if n == g
      fl = true
      x = a
    else
      fl, x = ispower(a, div(n, Int(g)), decom = decom)
      if !fl
        fl, x = ispower(nf(c)(-1)*a, div(n, Int(g)), decom = decom)
      end
    end
    if fl
      push!(n_gen, FacElem(x))
      r = divexact(se.rows[i], g)
      push!(r.pos, nrows(e) + length(n_gen))
      push!(r.values, -div(n, Int(g)))
      push!(A, r)
    else
      global bad = (a, div(n, Int(g)))
      error("not a power")
    end
  end
 
  #= Idea - before I forget:
  we have generators g_1, ..., g_n on input and enlarge by
                     h_1, ..., h_r
  And we have relations: n*h_i = some word in g
  in matrices:
  A = (words in g | n*I)
  now, using the column HNF
  A T = H = (I|0) - if the relations were primitive
  Thus
  A * (g | h)^t = 0 (using the relations) (possibly missing a sign)
  T^-1 = (R|S)^t
  then
  A T T^-1 (g|h)^t = (I|0) T^-1 (g|h)^t
  => R^t (g|h)^t = 0
  => S^t (g|h) is the new basis (by dimensions)

  now: since Hecke is row based, we have to transpose..
  =#
  A = A'
#    @show fmpz_mat(A)
  H, T = hnf_with_trafo(fmpz_mat(A))
  @assert isone(sub(H, 1:ncols(A), 1:ncols(A))) #otherwise, relations sucked.
  Ti = inv(T')
  Ti = sub(Ti, length(n_gen)+1:nrows(Ti), 1:ncols(Ti))

  R = vcat(c.R_gen, c.R_rel)
  if !(hash(zeta) in c.RS)
    push!(R, zeta)
  end
  R = vcat(R, n_gen)
  @assert ncols(Ti) == length(R) 

  d = Hecke.class_group_init(c.FB, SMat{fmpz}, add_rels = false)

  for i=1:nrows(Ti)
    a = FacElem(K(1))
    for j=1:ncols(Ti)
      a *= R[j]^Ti[i, j]
    end
      #TODO remove zeta from relations!!
    Hecke.class_group_add_relation(d, a)
  end
    
  return d
end

function sunits_mod_units(c::Hecke.ClassGrpCtx)
  Hecke.module_trafo_assure(c.M)
  trafos = c.M.trafo
  su = Array{FacElem{nf_elem, AnticNumberField}, 1}()
  for i=1:length(c.FB.ideals)
    x = zeros(fmpz, length(c.R_gen) + length(c.R_rel))
    x[i] = 1
    for j in length(trafos):-1:1
      Hecke.apply_right!(x, trafos[j])
    end
    y = FacElem(vcat(c.R_gen, c.R_rel), x)
    push!(su, y)
  end
  return su
end

function simplify(c::Hecke.ClassGrpCtx)
  d = Hecke.class_group_init(c.FB, SMat{fmpz}, add_rels = false)
  U = Hecke.UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(order(d))

  Hecke.module_trafo_assure(c.M)
  trafos = c.M.trafo

  for i=1:length(c.FB.ideals)
    x = zeros(fmpz, length(c.R_gen) + length(c.R_rel))
    x[i] = 1
    for j in length(trafos):-1:1
      Hecke.apply_right!(x, trafos[j])
    end
    y = FacElem(vcat(c.R_gen, c.R_rel), x)
    fl = Hecke.class_group_add_relation(d, y, deepcopy(c.M.basis.rows[i]))
    @assert fl
  end
  for i=1:nrows(c.M.rel_gens)
    if iszero(c.M.rel_gens.rows[i])
      Hecke._add_unit(U, c.R_rel[i])
    end
  end
  for i=1:length(U.units)  
    Hecke.class_group_add_relation(d, U.units[i], SRow(FlintZZ))
  end
  return d
end

function units(c::Hecke.ClassGrpCtx)
  d = Hecke.class_group_init(c.FB, SMat{fmpz}, add_rels = false)
  U = Hecke.UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(order(d))

  Hecke.module_trafo_assure(c.M)
  trafos = c.M.trafo

  for i=1:nrows(c.M.rel_gens)
    if iszero(c.M.rel_gens.rows[i])
      Hecke._add_unit(U, c.R_rel[i])
    end
  end

  U.units = Hecke.reduce(U.units, U.tors_prec)
  U.tentative_regulator = Hecke.regulator(U.units, 64)

  return U
end


#TODO:
#  use the essential part only for the saturation (pointless for MultiQuad:
#    the Brauer relations force every prime block to have 2 on the
#    diagonal)
#  in MultiQuad, we get the "unit-part" for free without the expensive
#    real-part, so the S-units are the image of the rel mat, and
#    no need for the kernel.
#  keep track if the relations and update the unit group as well
#  S-units: easy: add the relation, here if n is prime, either
#   the S-class number or the regulator changes, never both
#  units: we have new^n = prod old. use this to obtain new basis
#
#  track the torsion as well
#  if n is divisible by 8, then, generically, the saturation needs to 
#  be followed by a second saturation at 2:
#    Elements look like (locally) an 8-th power but are only a 4-th
#    so I can only extract a 4-th.
#    However, it might be an 8-th (or the product of 2 might be an 8-th)
#  Darn. Math is unfair.
#  
#  extend to gen. mult group...
end
