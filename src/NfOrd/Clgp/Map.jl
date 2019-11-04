################################################################################
# maps and disc_log and such
################################################################################

export isprincipal

################################################################################
#
#  Finding small representatives in the class of a factored ideal
#
################################################################################

@doc Markdown.doc"""
    reduce_ideal2(A::FacElem{NfOrdIdl}) -> NfOrdIdl, FacElem{nf_elem}
Computes $B$ and $\alpha$ in factored form, such that $\alpha B = A$.
"""
function reduce_ideal2(I::FacElem{NfOrdIdl, NfOrdIdlSet})
  @assert !isempty(I.fac)
  O = order(first(keys(I.fac)))
  K = nf(O)
  fst = true
  a = FacElem(Dict(K(1) => fmpz(1)))
  A = ideal(O, 1)
  for (k,v) = I.fac
    @assert order(k) === O
    if iszero(v)
      continue
    end
    if fst
      A, a = power_reduce2(k, v)
      @hassert :PID_Test 1 (v>0 ? k^Int(v) : inv(k)^Int(-v)) == A*evaluate(a)
      fst = false
    else
      B, b = power_reduce2(k, v)
      @hassert :PID_Test (v>0 ? k^Int(v) : inv(k)^Int(-v)) == B*evaluate(b)
      A = A*B
      mul!(a, a, b)
      #a = a*b
      if norm(A) > abs(discriminant(O))
        A, c = reduce_ideal2(A)
        add_to_key!(a.fac, K(c), fmpz(-1))
        #a = a*FacElem(Dict(K(c) => fmpz(-1)))
      end
    end
  end
  @hassert :PID_Test 1 A*evaluate(a) == evaluate(I)
  return A, a
end

################################################################################
#
#  Finding small representatives in the class of an ideal power
#
################################################################################

# The bound should be sqrt(disc) (something from LLL)
@doc Markdown.doc"""
    power_reduce2(A::NfOrdIdl, e::fmpz) -> NfOrdIdl, FacElem{nf_elem}
Computes $B$ and $\alpha$ in factored form, such that $\alpha B = A^e$
$B$ has small norm.
"""
function power_reduce2(A::NfOrdIdl, e::fmpz)
  A_orig = deepcopy(A)
  e_orig = e

  O = order(A)
  K= nf(O)
  if norm(A) > abs(discriminant(O))
    A, a = reduce_ideal2(A)
    @hassert :PID_Test 1 a*A_orig == A
    # A_old * inv(a) = A_new
    #so a^e A_old^e = A_new^e
    al = FacElem(Dict(a=>-e))
  else
    al = FacElem(Dict(K(1) => fmpz(1)))
  end

  #we have A_orig^e = (A*a)^e = A^e*a^e = A^e*al and A is now small

  if e < 0
    B = inv(A)
    A = numerator(B)
    #al *= FacElem(Dict(K(denominator(B)) => fmpz(e)))
    add_to_key!(al.fac, K(denominator(B)), fmpz(e))
    e = -e
  end
  # A^e = A^(e/2)^2 A or A^(e/2)^2
  # al * A^old^(e/2) = A_new
  if e>1
    C, cl = power_reduce2(A, div(e, 2))
    @hassert :PID_Test 1 C*evaluate(cl) == A^Int(div(e, 2))

    C2 = C^2
    mul!(al, al, cl^2)
    #al = al*cl^2
    if norm(C2) > abs(discriminant(O))
      C2, a = reduce_ideal2(C2)
      add_to_key!(al.fac, inv(a), 1)
      #mul!(al, al, inv(a))# al *= inv(a)
    end

    if isodd(e)
      A = C2*A
      if norm(A) > abs(discriminant(O))
        A, a = reduce_ideal2(A)
        add_to_key!(al.fac, inv(a), 1)
        #mul!(al, al, inv(a)) #al *= inv(a)
      end
    else
      A = C2
    end
    return A, al
  else
    @assert e==1
    return A, al
  end
end

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
    B = reduce_ideal(B)
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
        B = reduce_ideal(B)
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
    return C(fmpz[1])
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
  d = C(sub(rr*T, 1:1, nrows(T)-length(C.snf)+1:nrows(T)))
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
  
  _I, b = reduce_ideal2(I) # do the obvious reduction to an ideal of bounded norm
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
  let c = c
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
    C = DiagonalGroup([1])
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

  C = DiagonalGroup([S[x, x] for x in p])
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
  J, a = reduce_ideal2(I)
  @hassert :PID_Test 1 evaluate(a)*J == evaluate(I)
  fl, x = isprincipal_fac_elem(J)
  @hassert :PID_Test 1 ideal(order(J), evaluate(x)) == J
  x = x * a
  return fl, x
end

@doc Markdown.doc"""
    principal_gen_fac_elem(A::NfOrdIdl) -> FacElem{nf_elem, NumberField}
For a principal ideal $A$, find a generator in factored form.
"""
function principal_gen_fac_elem(A::NfOrdIdl)
  fl, e = isprincipal_fac_elem(A)
  if !fl
    error("Ideal is not principal")
  end
  return e
end


@doc Markdown.doc"""
    principal_gen_fac_elem(I::FacElem) -> FacElem{nf_elem, NumberField}
For a principal ideal $A$ in factored form, find a generator in factored form.
"""
function principal_gen_fac_elem(I::FacElem{NfOrdIdl, NfOrdIdlSet})
  J, a= reduce_ideal2(I)
  #@hassert :PID_Test 1 evaluate(a)*J == evaluate(I)
  x = Hecke.principal_gen_fac_elem(J)
  #@hassert :PID_Test 1 ideal(order(J), evaluate(x)) == J
  mul!(x, x, a) #x=x*a
  return x
  
end

@doc Markdown.doc"""
    principal_gen(A::NfOrdIdl) -> NfOrdElem
For a principal ideal $A$, find a generator.
"""
function principal_gen(A::NfOrdIdl)
  O = order(A)
  if ismaximal(O)
    fl, e = isprincipal_fac_elem(A)
  else
    fl, e = isprincipal_non_maximal(A)
  end
  if !fl
    error("Ideal is not principal")
  end
  if ismaximal(O)
    return O(evaluate(e))
  else
    return e
  end
end

@doc Markdown.doc"""
    isprincipal_fac_elem(A::NfOrdIdl) -> Bool, FacElem{nf_elem, NumberField}
Tests if $A$ is principal and returns $(\mathtt{true}, \alpha)$ if $A =
\langle \alpha\rangle$ of $(\mathtt{false}, 1)$ otherwise.  
The generator will be in factored form.
"""
function isprincipal_fac_elem(A::NfOrdIdl)
  if A.is_principal == 1 && isdefined(A, :princ_gen)
    return true, FacElem(A.princ_gen.elem_in_nf)
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
  #A.is_principal = 1
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
  ev = O(evaluate(a))
  A.is_principal = 1
  A.princ_gen = ev
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
        @show "cannot round:", C[i,j]
        throw(InexactError())
      end
      v[i,j] = div(a+b, 2)
    end
  end
  return v
end
  
#a is an array of FacElem's
#the elements are reduced modulo the units in U
function reduce_mod_units(a::Array{T, 1}, U) where T
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
  if isdefined(U, :tentative_regulator)
    #TODO: improve here - it works, kind of...
    B = Hecke._conj_arb_log_matrix_normalise_cutoff(b, prec)
    bd = maximum(sqrt(sum(B[i,j]^2 for j=1:ncols(B))) for i=1:nrows(B))
    bd = bd/root(U.tentative_regulator, length(U.units))
    if isfinite(bd)
      s = ccall((:arb_bits, :libarb), Int, (Ref{arb}, ), bd)
      prec = max(s, prec)
      prec = 1<<nbits(prec)
    else
      #@show "too large"
    end
  end

  while true
    prec, A = Hecke._conj_log_mat_cutoff_inv(U, prec)
    B = Hecke._conj_arb_log_matrix_normalise_cutoff(b, prec)
    nB = (B*B')[1,1]
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


mutable struct MapSUnitModUnitGrpFacElem{T} <: Map{T, FacElemMon{AnticNumberField}, HeckeMap, MapSUnitModUnitGrpFacElem}
  header::MapHeader
  idl::Array{NfOrdIdl, 1}
  valuations::Vector{SRow{fmpz}}

  function MapSUnitModUnitGrpFacElem{T}() where {T}
    return new{T}()
  end
end

function show(io::IO, mC::MapSUnitModUnitGrpFacElem)
  @show_name(io, mC)
  io = IOContext(io, :compact => true)
  println(io, "SUnits (in factored form) mod Units map of ")
  show(io, codomain(mC)) 
  println(io, "for $(mC.idl)")
end

#Plan:
# find x_i s.th. I[i]*x[i] is FB-smooth
#  find T sth. T R = (I[i]*x[i])^d
#  saturate T|-d??

@doc Markdown.doc"""
    sunit_mod_units_group_fac_elem(I::Array{NfOrdIdl, 1}) -> GrpAb, Map
For an array $I$ of (coprime prime) ideals, find the $S$-unit group defined
by $I$, ie. the group of non-zero field elements which are only divisible
by ideals in $I$ modulo the units of the field.
The map will return elements in factored form.
"""
function sunit_mod_units_group_fac_elem(I::Array{NfOrdIdl, 1})
  #deal with trivial case somehow!!!
  @assert length(I) > 0
  O = order(I[1])
  I_in = I

  @vprint :ClassGroup 1 "calling sunit_mod_units_group_fac_elem with $(length(I)) ideals\n"

  c = _get_ClassGrpCtx_of_order(O, false)
  if c == nothing
    L = lll(maximal_order(nf(O)))
    class_group(L)
    c = _get_ClassGrpCtx_of_order(L)
    I = map(IdealSet(L), I)
  end
  module_trafo_assure(c.M)
  H = c.M.basis
  T = c.M.trafo

  U = Array{FacElem{nf_elem, Nemo.AnticNumberField}, 1}()

  X = Array{nf_elem, 1}()

  rr = sparse_matrix(FlintZZ)

  # To track the valuation of the S-units
  vals_of_rels = SRow{fmpz}[]

  @vprint :ClassGroup 1 "finding relations ...\n"
  @vtime :ClassGroup 1 for (i, A) = enumerate(I)
    @vprint :ClassGroup 2 "doin' $A\n"
    @vtime :ClassGroup 2 x, r = class_group_ideal_relation(A, c)
# TODO: write == for Idl and FracIdl    
#    @assert prod([c.FB.ideals[p]^Int(v) for (p,v) = r]) == x*A
    push!(X, x)
    push!(rr, r)
    v = SRow(FlintZZ)
    # We only track the valuation of the prime ideals in S.
    # Even though S might intersect the class group factor base
    # non-trivially, this should still be correct.
    push!(vals_of_rels, sparse_row(FlintZZ, [(i, fmpz(-1))]))
  end

  @vprint :ClassGroup 1 "... done\n"
   
  @vprint :ClassGroup 1 "solving...\n"
  @vtime :ClassGroup 1 R, d = solve_ut(H, rr)
  Rd = hcat(d*identity_matrix(SMat, FlintZZ, nrows(R)), fmpz(-1)*R)
  @vprint :ClassGroup 1 ".. done, now saturating ...\n"
  @vtime :ClassGroup 1 S = hnf(saturate(Rd))
  @vprint :ClassGroup 1 " done\n"
  S1 = sub(S, 1:nrows(S), 1:nrows(S))
  S2 = sub(S, 1:nrows(S), (nrows(S) + 1):ncols(S))
  @assert nrows(S1) == nrows(S2) && nrows(S1) == nrows(S)
  
  g = vcat(c.R_gen, c.R_rel)

  valuations = SRow{fmpz}[]

  for s = 1:S.r
    rs = zeros(fmpz, c.M.bas_gens.r + c.M.rel_gens.r)
    for (p, v) = S2[s]
      rs[p] = v
    end

    for i in length(T):-1:1
      apply_right!(rs, T[i])
    end

    _val_vec = sparse_row(FlintZZ)

    e = FacElem(g, rs)
    for (p, v) = S1[s]
      _val_vec = _val_vec + v * vals_of_rels[p]
      if haskey(e.fac, X[p])
        e.fac[X[p]] += v
      else
        e.fac[X[p]] = v
      end
    end

    _val_vec = -_val_vec
    inv!(e)

    push!(valuations, _val_vec)
    push!(U, e)  # I don't understand the inv
  end
  @vprint :ClassGroup 1 "reducing mod units\n"
  @vtime :ClassGroup 1 U = reduce_mod_units(U, _get_UnitGrpCtx_of_order(order(c)))
  @vprint :ClassGroup 1 "Done!\n"

  #for j in 1:length(I)
  #  @assert (O(evaluate(U[j]))*O) == prod(I[i]^Int(valuations[j][i]) for i in 1:length(I))
  #end

  C = DiagonalGroup(fmpz[0 for i=U])
  r = MapSUnitModUnitGrpFacElem{typeof(C)}()
  r.idl = I_in
 
  function exp(a::GrpAbFinGenElem)
    b = U[1]^a.coeff[1, 1]
    for i = 2:length(U)
      if iszero(a.coeff[1, i])
        continue
      end
      mul!(b, b, U[i]^a.coeff[1, i])
    end
    return b
  end

  function log(a::FacElem{nf_elem, AnticNumberField})
    b = SRow{fmpz}()
    for i=1:length(I)
      v = valuation(a, I[i])
      if v != 0
        push!(b.pos, i)
        push!(b.values, v)
      end
    end
    s, d = solve_ut(S1, b)
    @assert d == 1  # this would indicate element is not in group...
    c = zeros(fmpz, length(I))
    for (p,v) = s
      c[p] = v
    end
    return C(c)
  end

  function log(a::nf_elem)
    return log(FacElem([a], fmpz[1]))
  end

  r.header = MapHeader(C, FacElemMon(nf(O)), exp, log)
  r.valuations = valuations

  return C, r
end

mutable struct MapSUnitGrpFacElem{T} <: Map{T, FacElemMon{AnticNumberField}, HeckeMap, MapSUnitGrpFacElem}
  header::MapHeader
  idl::Array{NfOrdIdl, 1}
  isquotientmap::Int

  function MapSUnitGrpFacElem{T}() where {T}
    z = new{T}()
    z.isquotientmap = -1
    return z
  end
end

function show(io::IO, mC::MapSUnitGrpFacElem)
  @show_name(io, mC)
  print(io, "SUnits (in factored form) map of ")
  show(IOContext(io, :compact => true), codomain(mC))
  println(io, " for S of length ", length(mC.idl))
  if mC.isquotientmap != -1
    println(io, " This is the quotient modulo $(mC.isquotientmap)")
  end
end

@doc Markdown.doc"""
    sunit_group_fac_elem(I::Array{NfOrdIdl, 1}) -> GrpAb, Map
For an array $I$ of (coprime prime) ideals, find the $S$-unit group defined
by $I$, ie. the group of non-zero field elements which are only divisible
by ideals in $I$.
The map will return elements in factored form.
"""
function sunit_group_fac_elem(I::Array{NfOrdIdl, 1})
  O = order(I[1])
  S, mS = sunit_mod_units_group_fac_elem(I)
  U, mU = unit_group_fac_elem(O)

  G = DiagonalGroup(vcat(U.snf, S.snf))

  r = MapSUnitGrpFacElem{typeof(G)}()
  r.idl = I

  function exp(a::GrpAbFinGenElem)
    return image(mU, U(sub(a.coeff, 1:1, 1:length(U.snf))))*
           image(mS, S(sub(a.coeff, 1:1, length(U.snf)+1:length(G.snf))))

  end

  function log(a::FacElem{nf_elem, AnticNumberField})
    a1 = preimage(mS, a)
    a2 = a*inv(image(mS, a1))
#    @assert isunit(O(evaluate(a2)))
    a3 = preimage(mU, a2)
    return G(vcat([a3.coeff[1,i] for i=1:ncols(a3.coeff)], [a1.coeff[1,i] for i=1:ncols(a1.coeff)]))
  end

  function log(a::nf_elem)
    return log(FacElem([a], fmpz[1]))
  end

  r.header = MapHeader(G, FacElemMon(nf(O)), exp, log)

  return G, r
end

mutable struct MapSUnitGrp{T} <: Map{T, AnticNumberField, HeckeMap, MapSUnitGrp}
  header::MapHeader
  idl::Array{NfOrdIdl, 1}

  function MapSUnitGrp{T}() where {T}
    return new{T}()
  end
end

function show(io::IO, mC::MapSUnitGrp)
  @show_name(io, mC)
  print(io, "SUnits  map of ")
  show(IOContext(io, :compact => true), codomain(mC))
  println(io, " for $(mC.idl)")
end

@doc Markdown.doc"""
    sunit_group(I::Array{NfOrdIdl, 1}) -> GrpAb, Map
For an array $I$ of (coprime prime) ideals, find the $S$-unit group defined
by $I$, ie. the group of non-zero field elements which are only divisible
by ideals in $I$.
"""
function sunit_group(I::Array{NfOrdIdl, 1})
  O = order(I[1])
  G, mG = sunit_group_fac_elem(I)

  r = MapSUnitGrp{typeof(G)}()
  r.idl = I

  function exp(a::GrpAbFinGenElem)
    return evaluate(image(mG, a))
  end

  function log(a::nf_elem)
    return preimage(mG, FacElem([a], fmpz[1]))
  end

  r.header = MapHeader(G, nf(O), exp, log)

  return G, r
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
  
  prob = ppp > 0.1
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
