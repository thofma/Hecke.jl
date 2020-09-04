################################################################################
# maps and disc_log and such
################################################################################

export isprincipal

# TODO: Agree on a name for power_class vs power_reduce2
@doc Markdown.doc"""
    power_class(A::NfOrdIdl, e::fmpz) -> NfOrdIdl
Computes a (small) ideal in the same class as $A^e$
"""
function power_class(A::NfOrdIdl, e::fmpz)
  if e == 0
    O = order(A)
    return ideal(O, 1)
  end

  if e < 0
    A = inv(A)
    e = -e
    A = reduce_ideal(A)
  end

  if e == 1
    return A
  elseif e == 2
    return A*A
  end

  f = div(e, 2)
  B = power_class(A, f)^2
  if isodd(e)
    B *= A
  end
  if norm(B) > root(abs(discriminant(order(A))), 2)
    B, = reduce_ideal(B)
  end
  return B
end

@doc Markdown.doc"""
    power_product_class(A::Array{NfOrdIdl, 1}, e::Array{fmpz, 1}) -> NfOrdIdl
Computes a (small) ideal in the same class as $\prod A_i^{e_i}$.
"""
function power_product_class(A::Array{NfOrdIdl, 1}, e::Array{fmpz, 1})
  i = 1
  while i <= length(e) && e[i] == 0
    i += 1
  end
  if i > length(e)
    return power_class(A[1], fmpz(0))
  end
  B = power_class(A[i], e[i])
  i += 1
  while i <= length(e)
    if e[i] != 0
      B *= power_class(A[i], e[i])
      if norm(B) > root(abs(discriminant(order(B))), 2)
        B, = reduce_ideal(B)
      end
    end
    i += 1
  end
  return B
end

function class_group_disc_exp(a::GrpAbFinGenElem, c::ClassGrpCtx)
  if length(c.dl_data) == 3
    Ti = inv(c.dl_data[2])
    c.dl_data = (c.dl_data[1], c.dl_data[2], c.dl_data[3], Ti)
  else
    Ti = c.dl_data[4]
  end
  e = a.coeff * sub(Ti, nrows(Ti)-ncols(a.coeff)+1:nrows(Ti), 1:ncols(Ti))
  return power_product_class(c.FB.ideals[length(c.FB.ideals)-nrows(Ti)+1:end], [mod(e[1, i], c.h) for i=1:ncols(e)])
end

function class_group_disc_log(r::SRow{fmpz}, c::ClassGrpCtx)
  if length(c.dl_data) == 3
    s, T, C = c.dl_data
  else
    s, T, C, Ti = c.dl_data
  end
  if c.h==1
    return C[0]
  end
#  println("start with $r")
  while length(r.pos)>0 && r.pos[1] < s
    r = add_scaled_row(c.M.basis[r.pos[1]], r, -r.values[1])
    mod!(r, c.h)
  end

#  println("reduced to $r")
  rr = zero_matrix(FlintZZ, 1, nrows(T))
  for i = 1:nrows(T)
    rr[1,i] = 0
  end
  for (p,v) = r
    rr[1, p-s+1] = v
  end
  d = GrpAbFinGenElem(C, view(rr*T, 1:1, nrows(T)-length(C.snf)+1:nrows(T)))
#  println(d)
  return d
end

@doc Markdown.doc"""
    class_group_ideal_relation(I::NfOrdIdl, c::ClassGrpCtx) -> nf_elem, SRow{fmpz}
Finds a number field element $\alpha$ such that $\alpha I$ factors over
the factor base in $c$.
"""
function class_group_ideal_relation(I::NfOrdIdl, c::ClassGrpCtx)
  #easy case: I factors over the FB...
  # should be done for a factor base, not the class group ctx.
  # the ctx is needed for the small_elements buisness
  O = order(I)
  K = nf(O)
  n = norm(I)
  if issmooth(c.FB.fb_int, n)
    fl, r = _factor!(c.FB, I, false)
    if fl 
      return K(1), r
    end
  end
  # ok, we have to work
  
  _I, b = reduce_ideal(I) # do the obvious reduction to an ideal of bounded norm
  @hassert :PID_Test 1 b*I == _I
  I = _I
  n = norm(I)
  if issmooth(c.FB.fb_int, n)
    fl, r = _factor!(c.FB, I, false)
    if fl 
      return b, r
    end
  end
  #really annoying, but at least we have a small(ish) ideal now
  #println("have to work")
  E = class_group_small_lll_elements_relation_start(c, I)
  iI = inv(I)
  if isdefined(c, :randomClsEnv)
    J = c.randomClsEnv
  else
    J = random_init(c.FB.ideals[max(1, length(c.FB.ideals)-10):length(c.FB.ideals)], lb = root(abs(discriminant(O)), 2), ub = abs(discriminant(O)))
    c.randomClsEnv = J
  end
  use_rand = false
  last_j = I
  cnt = 0
  while true

    if E.cnt > max(2*c.expect, 0)
#      println("more random")
      use_rand = true
      last_j = random_get(J, reduce = false)
      E = class_group_small_lll_elements_relation_start(c, I*last_j) 
      iI = inv(E.A)
    end

    aa = class_group_small_lll_elements_relation_next(E)
    #println("trying $a")
    cnt += 1
    na = norm(aa, c.normCtx, norm(E.A))
    if na === nothing #basically means elt is too large,
                      # exhausted randomness, so redo it.
      use_rand = true
      last_j = random_get(J, reduce = false)
      E = class_group_small_lll_elements_relation_start(c, I*last_j) 
      iI = inv(E.A)
      continue
    end
    na = norm(E.A)*abs(na)
    n = FlintZZ(norm(iI)*na)
    if issmooth(c.FB.fb_int, n)
      a = K(O(fmpz[aa[1, i] for i=1:degree(K)]))
      Ia = simplify(a*iI)
      @assert n == norm(Ia)
      @assert Ia.den == 1
      local r::SRow{fmpz}
      if isone(n)
        @assert isone(Ia.num)
        r = SRow(FlintZZ)
      else
        fl, r = _factor!(c.FB, Ia.num, false)
        if !fl 
          continue
        end
        scale_row!(r, fmpz(-1))
      end
#      println("used $cnt attempts")
      if use_rand
        fl, s = _factor!(c.FB, last_j)
        @assert fl
        return b//a, r-s
      else
        return b//a, r
      end
    end
  end
end


function class_group_disc_log(I::NfOrdIdl, c::ClassGrpCtx)
  q, w = class_group_ideal_relation(I, c)
#  J = simplify(q*I)
#  H = prod([v<0?inv(c.FB.ideals[p])^Int(-v):c.FB.ideals[p]^Int(v) for (p,v) = w])
#  if J != H
#    println("q: $q\nw: $w")
#  end
#  @assert J == H
  return class_group_disc_log(w, c)
end

mutable struct MapClassGrp <: Map{GrpAbFinGen, NfOrdIdlSet, HeckeMap, MapClassGrp}
  header::MapHeader{GrpAbFinGen, NfOrdIdlSet}
  
  quo::Int
  princ_gens::Array{Tuple{FacElem{NfOrdIdl,NfOrdIdlSet}, FacElem{nf_elem, AnticNumberField}},1}
  small_gens::Vector{NfOrdIdl}
  function MapClassGrp()
    mp = new()
    mp.quo = -1
    return mp
  end
end

function change_base_ring(mC::MapClassGrp, O::NfOrd)
  L = order(codomain(mC))
  mD = MapClassGrp()
  mD.header = MapHeader(mC.header.domain, IdealSet(O), x -> IdealSet(O)(mC.header.image(x)), y -> mC.header.preimage(codomain(mC)(y)))
  return mD
end

function show(io::IO, mC::MapClassGrp)
  @show_name(io, mC)
  println(io, "ClassGroup map of ")
  show(IOContext(io, :compact => true), codomain(mC))
end

function class_group(c::ClassGrpCtx, O::NfOrd = order(c); redo::Bool = false)
  if !redo
    if isdefined(c, :cl_map)
      mC = c.cl_map::MapClassGrp
      C = domain(mC)
      if O !== order(c)
        return C, change_base_ring(mC, O)
      end
      return C, mC
    end
  end  
  C = class_group_grp(c, redo = redo)
  r = MapClassGrp()
  
  local disclog 
  let c = c, C = C
    function disclog(x::NfOrdIdl)
      if x.is_principal == 1
        return id(C)
      end
      return class_group_disc_log(x, c)
    end
  end
  
  local expo
  let c = c
    function expo(x::GrpAbFinGenElem)
      return class_group_disc_exp(x, c)
    end
  end
  r.header = MapHeader(C, parent(c.FB.ideals[1]), expo, disclog)

  c.cl_map = r
  if O !== order(c)
    return C, change_base_ring(r, O)
  end
  return C, r
end

function class_group_grp(c::ClassGrpCtx; redo::Bool = false)

  if !redo && isdefined(c, :dl_data)
    return c.dl_data[3]::GrpAbFinGen
  end

  h, p = class_group_get_pivot_info(c)
  @assert h>0

  if h==1 # group is trivial...
    C = abelian_group([1])
    #mC = x -> 1*O, inv x-> [1]
    c.dl_data = (1, identity_matrix(FlintZZ, 1), C)
    return C
  end

  s = minimum(p)
  #essential bit starts at s..

  n = length(c.FB.ideals)
  es = sub(c.M.basis, s:n, s:n)
  hnf!(es)
  es_dense = fmpz_mat(es)
  S, _, T = snf_with_transform(es_dense, false, true)

  p = findall(x->S[x,x]>1, 1:ncols(S))

  C = abelian_group(fmpz[S[x, x] for x in p])
  c.dl_data = (s, T, C)
  return C
end

#TODO: if an ideal is principal, store it on the ideal!!!
@doc Markdown.doc"""
    isprincipal_fac_elem(I::FacElem{NfOrdIdl, NfOrdIdlSet}) -> Bool, FacElem{nf_elem, NumberField}
Tests if $A$ is principal and returns $(\mathtt{true}, \alpha)$ if $A =
\langle \alpha\rangle$ of $(\mathtt{false}, 1)$ otherwise.  
The generator will be in factored form.
"""
function isprincipal_fac_elem(I::FacElem{NfOrdIdl, NfOrdIdlSet})
  J, a = reduce_ideal(I)
  @hassert :PID_Test 1 evaluate(a)*J == evaluate(I)
  fl, x = isprincipal_fac_elem(J)
  @hassert :PID_Test 1 ideal(order(J), evaluate(x)) == J
  x = x * a
  return fl, x
end

@doc Markdown.doc"""
    principal_generator_fac_elem(A::NfOrdIdl) -> FacElem{nf_elem, NumberField}
For a principal ideal $A$, find a generator in factored form.
"""
function principal_generator_fac_elem(A::NfOrdIdl)
  fl, e = isprincipal_fac_elem(A)
  if !fl
    error("Ideal is not principal")
  end
  return e
end


@doc Markdown.doc"""
    principal_generator_fac_elem(I::FacElem) -> FacElem{nf_elem, NumberField}
For a principal ideal $A$ in factored form, find a generator in factored form.
"""
function principal_generator_fac_elem(I::FacElem{NfOrdIdl, NfOrdIdlSet})
  if isempty(I.fac)
    return FacElem(one(nf(order(base_ring(I)))))
  end
  J, a= reduce_ideal(I)
  #@hassert :PID_Test 1 evaluate(a)*J == evaluate(I)
  x = Hecke.principal_generator_fac_elem(J)
  #@hassert :PID_Test 1 ideal(order(J), evaluate(x)) == J
  mul!(x, x, a) #x=x*a
  return x
end

@doc Markdown.doc"""
    principal_generator(A::NfOrdIdl) -> NfOrdElem
For a principal ideal $A$, find a generator.
"""
function principal_generator(A::NfOrdIdl)
  O = order(A)
  if ismaximal(O)
    fl, e = isprincipal_fac_elem(A)
    if !fl
      error("Ideal is not principal")
    end
    return O(evaluate(e))
  else
    fl, e1 = isprincipal_non_maximal(A)
    if !fl
      error("Ideal is not principal")
    end
    return e1
  end
end

@doc Markdown.doc"""
    isprincipal_fac_elem(A::NfOrdIdl) -> Bool, FacElem{nf_elem, NumberField}
Tests if $A$ is principal and returns $(\mathtt{true}, \alpha)$ if $A =
\langle \alpha\rangle$ of $(\mathtt{false}, 1)$ otherwise.  
The generator will be in factored form.
"""
function isprincipal_fac_elem(A::NfOrdIdl)
  if A.is_principal == 1
    if isdefined(A, :princ_gen_fac_elem)
      return true, A.princ_gen_fac_elem
    else
      if isdefined(A, :princ_gen)
        A.princ_gen_fac_elem = A.princ_gen.elem_in_nf
      end
      return true, FacElem(A.princ_gen_fac_elem)
    end
  end
  O = order(A)
  if A.is_principal == 2
    return false, FacElem(one(nf(O)))
  end
  c = _get_ClassGrpCtx_of_order(O, false)
  if c == nothing
    L = lll(maximal_order(nf(O)))
    class_group(L)
    c = _get_ClassGrpCtx_of_order(L)::Hecke.ClassGrpCtx{SMat{fmpz}}
    A = IdealSet(L)(A)
  else 
    L = O
  end

  module_trafo_assure(c.M)

  H = c.M.basis::SMat{fmpz}
  T = c.M.trafo::Vector

  x, r = class_group_ideal_relation(A, c)
  #so(?) x*A is c-smooth and x*A = evaluate(r)

  R, d = solve_ut(H, r)

  if d != 1
    A.is_principal = 2
    return false, FacElem([nf(O)(1)], fmpz[1])
  end
  
  
  rrows = (c.M.bas_gens.r + c.M.rel_gens.r)::Int
  rs = zeros(fmpz, rrows)

  for (p,v) = R
    rs[p] = v
  end

  for i in length(T):-1:1
    apply_right!(rs, T[i])
  end
  base = vcat(c.R_gen, c.R_rel)::Vector{Union{nf_elem, FacElem{nf_elem, AnticNumberField}}}
  e = FacElem(base, rs)::FacElem{nf_elem, AnticNumberField}
  add_to_key!(e.fac, x, -1)  

  #reduce e modulo units.
  e = reduce_mod_units(FacElem{nf_elem, AnticNumberField}[e], _get_UnitGrpCtx_of_order(L))[1]
  A.is_principal = 1
  A.princ_gen_fac_elem = e
  # TODO: if we set it to be principal, we need to set the generator. Otherwise the ^ function is broken
  return true, e
end

@doc Markdown.doc"""
    isprincipal(A::NfOrdIdl) -> Bool, NfOrdElem
    isprincipal(A::NfOrdFracIdl) -> Bool, NfOrdElem
Tests if $A$ is principal and returns $(\mathtt{true}, \alpha)$ if $A =
\langle \alpha\rangle$ of $(\mathtt{false}, 1)$ otherwise.  
"""
function isprincipal(A::NfOrdIdl)
  if A.is_principal == 1 && isdefined(A, :princ_gen)
    return true, A.princ_gen
  end
  O = order(A)
  if A.is_principal == 2
    return false, one(O)
  end
  if !ismaximal(O)
    return isprincipal_non_maximal(A)
  end
  fl, a = isprincipal_fac_elem(A)
  if fl
    ev = O(evaluate(a))
    A.is_principal = 1
    A.princ_gen = ev
  else
    ev = O(1)
    A.is_principal = 2
  end
  return fl, ev
end

function isprincipal(A::NfOrdFracIdl)
  O = order(A)
  if !ismaximal(O)
    fl, a = isprincipal_non_maximal(numerator(A, copy = false))
    b = elem_in_nf(a, copy = false)
  else
    fl, a = isprincipal_fac_elem(numerator(A, copy = false))
    b = evaluate(a)
  end
  return fl, b//denominator(A, copy = false)
end
 
# does not work, cannot work. Problem
#  x = 1/2 \pm 10^-n
# then x+1/2 = 1 \pm 10^-n and ceil can be 1 or 2
function unique_fmpz_mat(C::Nemo.arb_mat)
  half = parent(C[1,1])(fmpq(1//2))  #TODO: does not work
  half = parent(C[1,1])(1)//2
  v = zero_matrix(FlintZZ, nrows(C), ncols(C))

  for i=1:nrows(C)
    for j=1:ncols(C)
      fl, v[i,j] = unique_integer(floor(C[i,j] + half))
      if !fl
        return fl, v
      end
    end
  end
  return true, v
end

function Base.round(::Type{fmpz}, x::arb)
  if radius(x) > 1e-1
    throw(InexactError(:round, fmpz, x))
  end
  return round(fmpz, BigFloat(x))
end

function Base.round(::Type{fmpz_mat}, C::Nemo.arb_mat)
  v = zero_matrix(FlintZZ, nrows(C), ncols(C))

  for i=1:nrows(C)
    for j=1:ncols(C)
      v[i,j] = round(fmpz, C[i,j])
    end
  end
  return v
end

function round_approx(::Type{fmpz_mat}, C::Nemo.arb_mat)
  v = zero_matrix(FlintZZ, nrows(C), ncols(C))

  for i=1:nrows(C)
    for j=1:ncols(C)
      a = upper_bound(C[i,j], fmpz)
      b = lower_bound(C[i,j], fmpz)
      if (b-a) > sqrt(abs(C[i,j]))
        throw(InexactError(:round_approx, arb, C[i,j]))
      end
      v[i,j] = div(a+b, 2)
    end
  end
  return v
end
  
#a is an array of FacElem's
#the elements are reduced modulo the units in U
function reduce_mod_units(a::Array{FacElem{nf_elem, AnticNumberField}, 1}, U) 
  #for T of type FacElem, U cannot be found from the order as the order
  #is not known
  #TODO:
  # need to make this work (a bit) for non-maximal units!!!

  r = length(U.units)
  if r == 0
    return a
  end

  prec = U.tors_prec

  b = deepcopy(a)
  cnt = 10
  V = zero_matrix(FlintZZ, 1, 1)

  local B::arb_mat

  if isdefined(U, :tentative_regulator)
    #TODO: improve here - it works, kind of...
    B = Hecke._conj_arb_log_matrix_normalise_cutoff(b, prec)::arb_mat
    bd = maximum(sqrt(sum((B[i,j]::arb)^2 for j=1:ncols(B)))::arb for i=1:nrows(B))
    bd = bd/root(U.tentative_regulator, length(U.units))
    if isfinite(bd)
      s = ccall((:arb_bits, libarb), Int, (Ref{arb}, ), bd)
      prec = max(s, prec)
      prec = 1<<nbits(prec)
    else
      #@show "too large"
    end
  end

  while true
    prec::Int, A::arb_mat = Hecke._conj_log_mat_cutoff_inv(U, prec)
    B = Hecke._conj_arb_log_matrix_normalise_cutoff(b, prec)::arb_mat
    nB::arb = (B*B')[1,1]
    C = B*A
    exact = true
    try
      V  = round(fmpz_mat, C)
      exact = true
    catch e
      if !isa(e, InexactError)
        rethrow(e)
      end
      try 
        V = round_approx(fmpz_mat, C)
        exact = false
      catch e
        if !isa(e, InexactError)
          rethrow(e)
        end
      end
      prec *= 2
      if prec > 10000
        error("1: too much prec")
      end
      continue
    end

    if iszero(V)
      return b
    end
    @vprint :UnitGroup 2 "exactly? ($exact) reducing by $V\n"
    for i=1:length(b)
      for j = 1:ncols(V)
        if !iszero(V[i, j])
          mul!(b[i], b[i], U.units[j]^(-V[i,j]))
        end
      end
      #b[i] = b[i]*prod([U.units[j]^-V[i,j] for j = 1:ncols(V)])
    end

    if exact
      return b
    end
  end
end

################################################################################
#
#  Representative of ideal classes coprime to the modulus
#
################################################################################

@doc Markdown.doc"""
    find_coprime_representatives(mC::MapClassGrp, m::NfOrdIdl, lp::Dict{NfOrdIdl, Int} = factor(m)) -> MapClassGrp

Returns a class group map such that the representatives for every classes are coprime to $m$.
$lp$ is the factorization of $m$. 
"""
function find_coprime_representatives(mC::MapClassGrp, m::NfOrdIdl, lp::Dict{NfOrdIdl, Int} = factor(m))
  C = domain(mC)
  O = order(m)
  K = nf(O)
  
  L = Array{NfOrdIdl,1}(undef, ngens(C))
  el = Array{nf_elem,1}(undef, ngens(C))
  ppp = 1.0
  for (p, v) in lp
    ppp *= (1 - 1/Float64(norm(p)))
  end
  
  prob = ppp > 0.1 && degree(K) < 10
  for i = 1:ngens(C)
    @assert length(mC.princ_gens[i][1].fac) == 1
    a = first(keys(mC.princ_gens[i][1].fac))
    if iscoprime(a, m)
      L[i] = a
      el[i] = K(1)
    elseif prob
      L[i], el[i] = probabilistic_coprime(a, m)
    else
      L[i], el[i] = coprime_deterministic(a, m, lp)
    end
    @hassert :RayFacElem 1 iscoprime(L[i], m)
    @hassert :RayFacElem 1 a*el[i] == L[i]
  end
  
  local exp
  let L = L, C = C
    function exp(a::GrpAbFinGenElem)  
      e = Dict{NfOrdIdl,fmpz}()
      for i = 1:ngens(C)
        if !iszero(a[i])
          e[L[i]] = a[i]
        end
      end
      if isempty(e)
        e[ideal(O,1)]=1
      end
      return FacElem(e)
    end
  end
  
  return exp, el

end 

function coprime_deterministic(a::NfOrdIdl, m::NfOrdIdl, lp::Dict{NfOrdIdl, Int})
  g, ng = ppio(a.gen_one, m.gen_one)
  @assert !isone(g)
  primes = Tuple{fmpz, nf_elem}[]
  for (p, v) in lp
    if !divisible(g, minimum(p))
      continue
    end
    vp = valuation(a, p)
    if iszero(vp)
      continue
    end
    ant_val = anti_uniformizer(p)
    found = false
    ind = 1
    for i = 1:length(primes)
      if primes[i][1] == minimum(p)
        found = true
        ind = i
        break
      end
    end
    if found
      primes[ind] = (minimum(p), primes[ind][2]*ant_val^vp)
    else
      push!(primes, (minimum(p), ant_val^vp))
    end
  end
  
  OK = order(a)
  r = m.gen_one
  moduli = Vector{fmpz}(undef, length(primes)+1)
  for i = 1:length(primes)
    moduli[i] = ppio(a.gen_one, primes[i][1])[1]
    r = ppio(r, moduli[i])[2]
  end
  mo = moduli[1]
  res = primes[1][2]
  moduli[length(primes)+1] = r
  for i = 2:length(moduli)
    d, u, v = gcdx(mo, moduli[i])
    if i == length(moduli)
      res = u*mo + v*moduli[i]*res
    else
      res = primes[i][2]*u*mo + v*moduli[i]*res
    end
    mo = mo*moduli[i]
  end
  res = mod(res, minimum(m))
  I = res*a
  I = simplify(I)
  return I.num, res*I.den
end

function probabilistic_coprime(a::NfOrdIdl, m::NfOrdIdl)
  O = order(a)
  K = nf(O)
  J = inv(a)
  temp = basis_matrix(J.num, copy = false)*basis_matrix(O, copy = false)
  b = temp.num
  b_den = temp.den
  prec = 100
  local t
  while true
    if prec > 2^18
      error("Something wrong in short_elem")
    end
    try
      l, t = lll(J.num, zero_matrix(FlintZZ, 1,1), prec = prec)
      break
    catch e
      if !(e isa LowPrecisionLLL || e isa InexactError)
        rethrow(e)
      end
    end
    prec = 2 * prec
  end
  rr = matrix(FlintZZ, 1, nrows(t), fmpz[rand(1:minimum(a)^2) for i = 1:nrows(t)])
  b1 = t*b
  c = rr*b1
  s = divexact(elem_from_mat_row(K, c, 1, b_den), J.den)
  I = s*a
  I = simplify(I)
  I1 = I.num
  while !iscoprime(I1, m)
    rr = matrix(FlintZZ, 1, nrows(t), fmpz[rand(1:minimum(a)^2) for i = 1:nrows(t)])
    c = rr*b1
    s = divexact(elem_from_mat_row(K, c, 1, b_den), J.den)
    I = s*a
    I = simplify(I)
    I1 = I.num
  end
  return I1, s*I.den
end
