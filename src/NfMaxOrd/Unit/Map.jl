type MapUnitGrp{T, S} <: Map{T, S}
  header::Hecke.MapHeader

  function MapUnitGrp()
    return new()
  end
end

function show(io::IO, mC::MapUnitGrp)
  println(io, "UnitGroup map of $(codomain(mC))")
end

type MapUnitGrpFacElem{T} <: Map{T, FacElemMon{AnticNumberField}}
  header::Hecke.MapHeader

  function MapUnitGrpFacElem()
    return new()
  end
end

function show(io::IO, mC::MapUnitGrpFacElem)
  println(io, "Unit group map of $(codomain(mC)) in factored presentation")
end

function unit_group_disc_exp(x::FinGenGrpAbElem, U::UnitGrpCtx)
  K = nf(order(U))
  y = FacElem([K(U.torsion_units_gen)], [x.coeff[1,1]])
  for i=1:length(U.units)
    y *= U.units[i]^x.coeff[1,i+1]
  end
  return y
end

function unit_group_disc_log(x::FacElem{nf_elem, AnticNumberField} , U::UnitGrpCtx, G::FinGenGrpAbSnf)

  r = _add_dependent_unit(U, x, rel_only = true)
  @assert r[end] == -1

  y = deepcopy(x)
  for i=1:length(r)-1
    y *= U.units[i]^-r[i]
  end

  K = nf(order(U))

  p = next_prime(2^30)
  while (p-1) % U.torsion_units_order != 0
    p = next_prime(p)
  end
  P = prime_decomposition(order(U), p)[1][1]
  F, mF = ResidueField(order(U), P)
  mK = extend(mF, K)

  yp = F(1)
  for (k,v) = y.fac
    yp *= mK(k)^v
  end

  zp = mF(U.torsion_units_gen)
  res = fmpz[]
  for i=0:U.torsion_units_order-1
    if zp^i == yp
      push!(res, i)
    end
  end
  @assert length(res) == 1

  for i = 1:length(r)-1
    push!(res, r[i])
  end
  return G(res)
end 

function unit_group_fac_elem(c::ClassGrpCtx; redo::Bool = false)
  u = unit_group_ctx(c, redo = redo)
  if isdefined(u, :unit_map)
    mU = u.unit_map
    U = domain(mU)
    return U, mU
  end
  return unit_group_fac_elem(c, u)
end

function unit_group_fac_elem(c::ClassGrpCtx, u::UnitGrpCtx)
  O = order(c.FB.ideals[1])

  zo = u.torsion_units_order
  if zo == -1
    u.torsion_units_gen, u.torsion_units_order = torsion_units_gen_order(O)
    zo = u.torsion_units_order
  end
  r = unit_rank(O)
  d = fmpz[zo]
  for i=1:r
    push!(d, fmpz(0))
  end
  U = DiagonalGroup(d)

  r = MapUnitGrpFacElem{typeof(U)}()

  r.header = MapHeader(U, FacElemMon(nf(O)),
    x->unit_group_disc_exp(x, u),
    x->unit_group_disc_log(x, u, U))

  u.unit_map = r

  return U, r
end

