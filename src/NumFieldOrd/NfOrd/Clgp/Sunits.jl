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

@doc raw"""
    sunit_mod_units_group_fac_elem(I::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}) -> GrpAb, Map
For an array $I$ of (coprime prime) ideals, find the $S$-unit group defined
by $I$, ie. the group of non-zero field elements which are only divisible
by ideals in $I$ modulo the units of the field.
The map will return elements in factored form.
"""
function sunit_mod_units_group_fac_elem(I::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  #deal with trivial case somehow!!!
  @assert length(I) > 0
  O = order(I[1])
  I_in = I

  @vprintln :ClassGroup 1 "calling sunit_mod_units_group_fac_elem with $(length(I)) ideals"

  c = get_attribute(O, :ClassGrpCtx)
  if c === nothing
    L = lll(maximal_order(nf(O)))
    class_group(L)
    c = get_attribute(L, :ClassGrpCtx)
    I = map(IdealSet(L), I)
  end
  module_trafo_assure(c.M)
  H = c.M.basis
  T = c.M.trafo

  U = Vector{FacElem{AbsSimpleNumFieldElem, Nemo.AbsSimpleNumField}}()

  X = Vector{AbsSimpleNumFieldElem}()

  rr = sparse_matrix(FlintZZ)

  # To track the valuation of the S-units
  vals_of_rels = SRow{ZZRingElem}[]

  @vprintln :ClassGroup 1 "finding relations ..."
  @vtime :ClassGroup 1 for (i, A) = enumerate(I)
    @vprintln :ClassGroup 2 "doin' $(i)/$(length(I)):\n$A"
    @vtime :ClassGroup 2 x, r = class_group_ideal_relation(A, c)
# TODO: write == for Idl and FracIdl
#    @assert prod([c.FB.ideals[p]^Int(v) for (p,v) = r]) == x*A
    push!(X, x)
    push!(rr, r)
    v = sparse_row(FlintZZ)
    # We only track the valuation of the prime ideals in S.
    # Even though S might intersect the class group factor base
    # non-trivially, this should still be correct.
    push!(vals_of_rels, sparse_row(FlintZZ, [(i, ZZRingElem(-1))], sort = false))
  end

  @vprintln :ClassGroup 1 "... done"

  @vprintln :ClassGroup 1 "solving..."
  @vtime :ClassGroup 1 R, d = _solve_ut(H, rr)
  Rd = hcat(d*identity_matrix(SMat, FlintZZ, nrows(R)), ZZRingElem(-1)*R)
  @vprintln :ClassGroup 1 ".. done, now saturating ..."
  @vtime :ClassGroup 1 S = hnf(saturate(Rd))
  @vprintln :ClassGroup 1 " done"
  S1 = sub(S, 1:nrows(S), 1:nrows(S))
  S2 = sub(S, 1:nrows(S), (nrows(S) + 1):ncols(S))
  @assert nrows(S1) == nrows(S2) && nrows(S1) == nrows(S)

  g = vcat(c.R_gen, c.R_rel)

  valuations = SRow{ZZRingElem}[]

  for s = 1:S.r
    rs = zeros(ZZRingElem, c.M.bas_gens.r + c.M.rel_gens.r)
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
  @vprintln :ClassGroup 1 "reducing mod units"
  @vtime :ClassGroup 1 U = reduce_mod_units(U, get_attribute(order(c), :UnitGrpCtx))
  @vprintln :ClassGroup 1 "Done!"

  #for j in 1:length(I)
  #  @assert (O(evaluate(U[j]))*O) == prod(I[i]^Int(valuations[j][i]) for i in 1:length(I))
  #end

  C = abelian_group(ZZRingElem[0 for i=U])
  r = MapSUnitModUnitGrpFacElem()
  r.idl = I_in

  local exp
  let U = U
    function exp(a::FinGenAbGroupElem)
      b = U[1]^a.coeff[1, 1]
      for i = 2:length(U)
        if iszero(a.coeff[1, i])
          continue
        end
        mul!(b, b, U[i]^a.coeff[1, i])
      end
      return b
    end
  end

  local log
  let I = I, S1 = S1, C = C

    function log(a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})
      b = sparse_row(FlintZZ)
      for i=1:length(I)
        v = valuation(a, I[i])
        if v != 0
          push!(b.pos, i)
          push!(b.values, v)
        end
      end
      s, d = _solve_ut(S1, b)
      @assert d == 1  # this would indicate element is not in group...
      c = zeros(ZZRingElem, length(I))
      for (p,v) = s
        c[p] = v
      end
      return C(c)
    end

    function log(a::AbsSimpleNumFieldElem)
      return log(FacElem(a))
    end
  end

  r.header = MapHeader(C, FacElemMon(nf(O)), exp, log)
  r.valuations = valuations

  return C, r
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

@doc raw"""
    sunit_group_fac_elem(I::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}) -> GrpAb, Map
For an array $I$ of (coprime prime) ideals, find the $S$-unit group defined
by $I$, ie. the group of non-zero field elements which are only divisible
by ideals in $I$.
The map will return elements in factored form.
"""
function sunit_group_fac_elem(I::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  O = order(I[1])
  S, mS = sunit_mod_units_group_fac_elem(I)
  U, mU = unit_group_fac_elem(O)

  G = abelian_group(vcat(U.snf, S.snf))

  r = MapSUnitGrpFacElem()
  r.valuations = Vector{SRow{ZZRingElem}}(undef, ngens(G))
  for i = 1:ngens(U)
    r.valuations[i] = sparse_row(FlintZZ)
  end
  for i = 1:ngens(S)
    r.valuations[i+ngens(U)] = mS.valuations[i]
  end
  r.idl = I

  local exp
  let mU = mU, mS = mS, U = U, G = G
    function exp(a::FinGenAbGroupElem)
      return image(mU, FinGenAbGroupElem(U, sub(a.coeff, 1:1, 1:length(U.snf))))*
             image(mS, FinGenAbGroupElem(S, sub(a.coeff, 1:1, length(U.snf)+1:length(G.snf))))
    end
  end

  local log
  let mS = mS, mU = mU, G = G
    function log(a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})
      a1 = preimage(mS, a)
      a2 = a*inv(image(mS, a1))
      #     @assert is_unit(O(evaluate(a2)))
      a3 = preimage(mU, a2)
      return FinGenAbGroupElem(G, hcat(a3.coeff, a1.coeff))
    end

    function log(a::AbsSimpleNumFieldElem)
      return log(FacElem(a))
    end
  end

  r.header = MapHeader(G, FacElemMon(nf(O)), exp, log)

  return G, r
end


function show(io::IO, mC::MapSUnitGrp)
  @show_name(io, mC)
  print(io, "SUnits  map of ")
  show(IOContext(io, :compact => true), codomain(mC))
  println(io, " for $(mC.idl)")
end

@doc raw"""
    sunit_group(I::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}) -> GrpAb, Map
For an array $I$ of (coprime prime) ideals, find the $S$-unit group defined
by $I$, ie. the group of non-zero field elements which are only divisible
by ideals in $I$.
"""
function sunit_group(I::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  O = order(I[1])
  G, mG = sunit_group_fac_elem(I)

  r = MapSUnitGrp()
  r.idl = I

  local exp
  let mG = mG
    function exp(a::FinGenAbGroupElem)
      return evaluate(image(mG, a))
    end
  end

  local log
  let mG = mG
    function log(a::AbsSimpleNumFieldElem)
      return preimage(mG, FacElem(a))
    end
  end

  r.header = MapHeader(G, nf(O), exp, log)

  return G, r
end
