################################################################################
# maps and disc_log and such
################################################################################

doc"""
    power_class(A::NfMaxOrdIdl, e::fmpz) -> NfMaxOrdIdl
> Computes a (small) ideal in the same class as $A^e$
"""
function power_class(A::NfMaxOrdIdl, e::fmpz)
  if e == 0
    O = order(A)
    return ideal(O, parent(basis_mat(O).num)(1))
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

doc"""
    power_product_class(A::Array{NfMaxOrdIdl, 1}, e::Array{fmpz, 1}) -> NfMaxOrdIdl
> Computes a (small) ideal in the same class as $\prod A_i^{e_i}$.
"""
function power_product_class(A::Array{NfMaxOrdIdl, 1}, e::Array{fmpz, 1})
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

function class_group_disc_exp(a::FinGenGrpAbElem, c::ClassGrpCtx)
  if length(c.dl_data) == 3
    Ti = inv(c.dl_data[2])
    c.dl_data = (c.dl_data[1], c.dl_data[2], c.dl_data[3], Ti)
  else
    Ti = c.dl_data[4]
  end
  e = a.coeff * sub(Ti, rows(Ti)-cols(a.coeff)+1:rows(Ti), 1:cols(Ti))
  return power_product_class(c.FB.ideals[length(c.FB.ideals)-rows(Ti)+1:end], [mod(e[1, i], c.h) for i=1:cols(e)])
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
  rr = MatrixSpace(FlintZZ, 1, rows(T))()
  for i = 1:rows(T)
    rr[1,i] = 0
  end
  for (p,v) = r
    rr[1, p-s+1] = v
  end
  return C(sub(rr*T, 1:1, rows(T)-length(C.snf)+1:rows(T)))
end

doc"""
    class_group_ideal_relation(I::NfMaxOrdIdl, c::ClassGrpCtx) -> nf_elem, SRow{fmpz}
> Finds a number field element $\alpha$ such that $\alpha I$ factors over
> the factor base in $c$.
"""
function class_group_ideal_relation(I::NfMaxOrdIdl, c::ClassGrpCtx)
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
#  println("reduce to $I")
#  J = simplify(b*_I)
#  @assert den(J) == 1
#  @assert num(J) == I
  I = _I
  n = norm(I)
  if issmooth(c.FB.fb_int, n)
    fl, r = _factor!(c.FB, I, false)
    if fl 
      return b, r
    end
  end
  #really annoying, but at least we have a small(ish) ideal now

#  println("have to work")
  E = class_group_small_lll_elements_relation_start(c, I)
  iI = inv(I)
  J = NfMaxOrdIdl[]
  use_rand = false
  last_j = I
  while true
    a = class_group_small_lll_elements_relation_next(E)
#    println("trying $a")
    Ia = simplify(a*iI)
    @assert Ia.den == 1
    n = norm(Ia.num)
    if issmooth(c.FB.fb_int, n)
      fl, r = _factor!(c.FB, Ia.num, false)
      if fl 
        scale_row!(r, fmpz(-1))
        if use_rand
          fl, s = _factor!(c.FB, last_j)
          @assert fl
          return b//a, r-s
        else
          return b//a, r
        end
      end
    end
    if E.cnt > max(2*c.expect, 0)
      println("more random")
      use_rand = true
      push!(J, rand(c.FB.ideals))
      last_j = random_get(J, reduce = false)
      E = class_group_small_lll_elements_relation_start(c, I*last_j) 
      iI = inv(E.A)
    end
  end
end


function class_group_disc_log(I::NfMaxOrdIdl, c::ClassGrpCtx)
  q, w = class_group_ideal_relation(I, c)
#  J = simplify(q*I)
#  H = prod([v<0?inv(c.FB.ideals[p])^Int(-v):c.FB.ideals[p]^Int(v) for (p,v) = w])
#  if J != H
#    println("q: $q\nw: $w")
#  end
#  @assert J == H
  return class_group_disc_log(w, c)
end

type MapClassGrp{T} <: Map{T, NfMaxOrdIdlSet}
  header::MapHeader

  function MapClassGrp()
    return new()
  end
end

function show(io::IO, mC::MapClassGrp)
  println(io, "ClassGroup map of $(codomain(mC))")
end

function class_group(c::ClassGrpCtx; redo::Bool = false)
  if !redo
    if isdefined(c, :cl_map)
      mC = c.cl_map
      C = domain(mC)
      return C, mC
    end
  end  
  C = class_group_grp(c, redo = redo)
  r = MapClassGrp{typeof(C)}()
  r.header = MapHeader(C, parent(c.FB.ideals[1]), x->class_group_disc_exp(x, c), x->class_group_disc_log(x, c))

  c.cl_map = r
  return C, r
end

function class_group_grp(c::ClassGrpCtx; redo::Bool = false)

  if !redo && isdefined(c, :dl_data)
    return c.dl_data[3]
  end

  h, p = class_group_get_pivot_info(c)
  @assert h>0

  if h==1 # group is trivial...
    C = DiagonalGroup([1])
    #mC = x -> 1*O, inv x-> [1]
    c.dl_data = (1, MatrixSpace(FlintZZ, 1, 1)(1), C)
    return C
  end

  s = minimum(p)
  #essential bit starts at s..

  n = length(c.FB.ideals)
  es = sub(c.M.basis, s:n, s:n)
  hnf!(es)
  es_dense = fmpz_mat(es)
  S, _, T = snf_with_transform(es_dense, false, true)

  p = find(x->S[x,x]>1, 1:cols(S))

  C = DiagonalGroup([S[x,x] for x= p])
  c.dl_data = (s, T, C)
  return C
end

#TODO: if an ideal is principal, store it on the ideal!!!

doc"""
    principal_gen_fac_elem(A::NfMaxOrdIdl) -> FacElem{nf_elem, NumberField}
> For a principal ideal $A$, find a generator in factored form.
"""
function principal_gen_fac_elem(A::NfMaxOrdIdl)
  fl, e = isprincipal_fac_elem(A)
  if !fl
    error("Ideal is not principal")
  end
  return e
end

doc"""
    principal_gen(A::NfMaxOrdIdl) -> NfOrdElem
> For a principal ideal $A$, find a generator.
"""
function principal_gen(A::NfMaxOrdIdl)
  fl, e = isprincipal_fac_elem(A)
  if !fl
    error("Ideal is not principal")
  end
  return O(evaluate(e))
end

doc"""
    isprincipal_fac_elem(A::NfMaxOrdIdl) -> Bool, FacElem{nf_elem, NumberField}
> Tests if $A$ is principal and returns $(\mathtt{true}, \alpha)$ if $A =
> \langle \alpha\rangle$ of $(\mathtt{false}, 1)$ otherwise.  
> The generator will be in factored form.
"""
function isprincipal_fac_elem(A::NfMaxOrdIdl)
  O = order(A)
  c = _get_ClassGrpCtx_of_order(O)

  module_trafo_assure(c.M)

  H = c.M.basis
  T = c.M.trafo

  x, r = class_group_ideal_relation(A, c)

  R, d = solve_ut(H, r)
  if d != 1
    false, FacElem([nf(O)(1)], fmpz[1])
  end
  rs = zeros(fmpz, c.M.bas_gens.r + c.M.rel_gens.r)
  for (p,v) = R
    rs[p] = v
  end

  for i in length(T):-1:1
    apply_right!(rs, T[i])
  end

  e = FacElem(vcat(c.R_gen, c.R_rel), rs)*x

  #reduce e modulo units.
  e = reduce_mod_units([e], _get_UnitGrpCtx_of_order(O))[1]

  return true, e
end

doc"""
    isprincipal(A::NfMaxOrdIdl) -> Bool, NfOrdElem
> Tests if $A$ is principal and returns $(\mathtt{true}, \alpha)$ if $A =
> \langle \alpha\rangle$ of $(\mathtt{false}, 1)$ otherwise.  
"""
function isprincipal(A::NfMaxOrdIdl)
  O = order(A)
  fl, a = isprincipal_fac_elem(A)
  return fl, O(evaluate(a))
end
 
#a is an array of FacElem's
#the elements are reduced modulo the units in U
function reduce_mod_units{T}(a::Array{T, 1}, U::UnitGrpCtx)
  #for T of type FacElem, U cannot be found from the order as the order
  #is not known
  r = length(U.units)
  if r == 0
    return a
  end

  prec = U.tors_prec

  b = deepcopy(a)
  while true
    prec, A = _conj_log_mat_cutoff_inv(U, prec)
    B = _conj_arb_log_matrix_normalise_cutoff(a, prec)
    C = B*A

    redo = false

    for i=1:rows(C)
      for j=1:cols(C)
        fl, v = unique_integer(ceil(C[i,j]))
        if !fl
          prec *= 2
          redo = true
          b = deepcopy(a)
#          println("more prec")
          break
        end
        if redo
          break
        end
        b[i] *= U.units[j]^-v
      end
    end
    return b
  end  
end

type MapSUnitModUnitGrpFacElem{T} <: Map{T, FacElemMon{AnticNumberField}}
  header::MapHeader
  idl::Array{NfMaxOrdIdl, 1}

  function MapSUnitModUnitGrpFacElem()
    return new()
  end
end

function show(io::IO, mC::MapSUnitModUnitGrpFacElem)
  println(io, "SUnits (in factored form) mod Units map of $(codomain(mC)) for $(mC.idl)")
end

#Plan:
# find x_i s.th. I[i]*x[i] is FB-smooth
#  find T sth. T R = (I[i]*x[i])^d
#  saturate T|-d??

doc"""
    sunit_mod_units_group_fac_elem(I::Array{NfMaxOrdIdl, 1}) -> GrpAb, Map
> For an array $I$ of (coprime prime) ideals, find the $S$-unit group defined
> by $I$, ie. the group of non-zero field elements which are only divisible
> by ideals in $I$ modulo the units of the field.
> The map will return elements in factored form.
"""
function sunit_mod_units_group_fac_elem(I::Array{NfMaxOrdIdl, 1})
  #deal with trivial case somehow!!!
  O = order(I[1])

  c = _get_ClassGrpCtx_of_order(O)
  module_trafo_assure(c.M)
  H = c.M.basis
  T = c.M.trafo

  U = Array{FacElem{nf_elem, Nemo.AnticNumberField}, 1}()

  X = Array{nf_elem, 1}()

  rr = SMat(FlintZZ)
  for A = I
    x, r = class_group_ideal_relation(A, c)
# TODO: write == for Idl and FracIdl    
#    @assert prod([c.FB.ideals[p]^Int(v) for (p,v) = r]) == x*A
    push!(X, x)
    push!(rr, r)
  end
    
  R, d = solve_ut(H, rr)
  Rd = hcat(d*id(SMat, FlintZZ, R.r), fmpz(-1)*R)
  S = hnf(saturate(Rd))
  S1 = sub(S, 1:S.r, 1:S.r)
  S2 = sub(S, 1:S.r, S.r+1:S.c)
  @assert rows(S1) == rows(S2) && rows(S1) == S.r
  
  g = vcat(c.R_gen, c.R_rel)

  for s = 1:S.r
    rs = zeros(fmpz, c.M.bas_gens.r + c.M.rel_gens.r)
    for (p,v) = S2[s] 
      rs[p] = v
    end

    for i in length(T):-1:1
      apply_right!(rs, T[i])
    end

    e = FacElem(g, rs)
    for (p,v) = S1[s]
      e *= X[p]^v
    end

    push!(U, inv(e))  # I don't understand the inv
  end
  U = reduce_mod_units(U, _get_UnitGrpCtx_of_order(O))

  C = DiagonalGroup(fmpz[0 for i=U])
  r = MapSUnitModUnitGrpFacElem{typeof(C)}()
  r.idl = I
 
  function exp(a::FinGenGrpAbElem)
    b = U[1]^a.coeff[1, 1]
    for i=2:length(U)
      b *= U[i]^a.coeff[1, i]
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

  return C, r
end

type MapSUnitGrpFacElem{T} <: Map{T, FacElemMon{AnticNumberField}}
  header::MapHeader
  idl::Array{NfMaxOrdIdl, 1}

  function MapSUnitGrpFacElem()
    return new()
  end
end

function show(io::IO, mC::MapSUnitGrpFacElem)
  println(io, "SUnits (in factored form) map of $(codomain(mC)) for $(mC.idl)")
end

doc"""
    sunit_group_fac_elem(I::Array{NfMaxOrdIdl, 1}) -> GrpAb, Map
> For an array $I$ of (coprime prime) ideals, find the $S$-unit group defined
> by $I$, ie. the group of non-zero field elements which are only divisible
> by ideals in $I$.
> The map will return elements in factored form.
"""
function sunit_group_fac_elem(I::Array{NfMaxOrdIdl, 1})
  O = order(I[1])
  S, mS = sunit_mod_units_group_fac_elem(I)
  U, mU = unit_group_fac_elem(O)

  G = DiagonalGroup(vcat(U.snf, S.snf))

  r = MapSUnitGrpFacElem{typeof(G)}()
  r.idl = I

  function exp(a::FinGenGrpAbElem)
    return image(mU, U(sub(a.coeff, 1:1, 1:length(U.snf))))*
           image(mS, S(sub(a.coeff, 1:1, length(U.snf)+1:length(G.snf))))

  end

  function log(a::FacElem{nf_elem, AnticNumberField})
    a1 = preimage(mS, a)
    a2 = a*inv(image(mS, a1))
    a3 = preimage(mU, a2)
    return G(vcat([a3.coeff[1,i] for i=1:cols(a3.coeff)], [a1.coeff[1,i] for i=1:cols(a1.coeff)]))
  end

  function log(a::nf_elem)
    return log(FacElem([a], fmpz[1]))
  end

  r.header = MapHeader(G, FacElemMon(nf(O)), exp, log)

  return G, r
end

type MapSUnitGrp{T} <: Map{T, AnticNumberField}
  header::MapHeader
  idl::Array{NfMaxOrdIdl, 1}

  function MapSUnitGrp()
    return new()
  end
end

function show(io::IO, mC::MapSUnitGrp)
  println(io, "SUnits  map of $(codomain(mC)) for $(mC.idl)")
end

doc"""
    sunit_group(I::Array{NfMaxOrdIdl, 1}) -> GrpAb, Map
> For an array $I$ of (coprime prime) ideals, find the $S$-unit group defined
> by $I$, ie. the group of non-zero field elements which are only divisible
> by ideals in $I$.
"""
function sunit_group(I::Array{NfMaxOrdIdl, 1})
  O = order(I[1])
  G, mG = sunit_group_fac_elem(I)

  r = MapSUnitGrp{typeof(G)}()
  r.idl = I

  function exp(a::FinGenGrpAbElem)
    return evaluate(image(mG, a))
  end

  function log(a::nf_elem)
    return preimage(mG, FacElem([a], fmpz[1]))
  end

  r.header = MapHeader(G, nf(O), exp, log)

  return G, r
end


