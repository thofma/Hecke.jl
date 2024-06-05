################################################################################
#
#  Unit groups of orders in étale algebras
#
################################################################################

function unit_group(O::AlgAssAbsOrd)
  @assert is_commutative(O)
  mU = get_attribute!(O, :unit_group) do
    if is_maximal(O)
      U, mU = _unit_group_maximal(O)
    else
      OK = maximal_order(O)
      UU, mUU = unit_group(OK)
      U, mU = _unit_group_non_maximal(O, OK, mUU)
    end
    return mU
  end::Map
  return domain(mU), mU
end

function unit_group_fac_elem(O::AlgAssAbsOrd)
  @assert is_commutative(O)
  mU = get_attribute!(O, :unit_group_fac_elem) do
    if is_maximal(O)
      U, mU = _unit_group_maximal_fac_elem(O)
    else
      OK = maximal_order(O)
      UU, mUU = unit_group_fac_elem(OK)
      U, mU = _unit_group_non_maximal(O, OK, mUU)
    end
    return mU
  end::Map
  return domain(mU), mU
end

function _preimage_fac_elem(f, y, i, fields_and_maps)
  A = domain(f)
  almostone = one(A) - preimage(fields_and_maps[i][2], one(fields_and_maps[i][1]))
  D = Dict{elem_type(domain(f)), ZZRingElem}((almostone + preimage(f, b)) => e for (b, e) in y)
  return FacElem(domain(f), D)
end

function _image_fac_elem(f, x)
  K = codomain(f)
  D = Dict{elem_type(K), ZZRingElem}(image(f, b) => e for (b, e) in x)
  return FacElem(K, D)
end

#function _image_fac_elem(f, y, i, fields_and_maps)
#  A = domain(f)
#  almostone = one(A) - preimage(fields_and_maps[i][2], one(fields_and_maps[i][1]))
#  D = Dict{elem_type(domain(f)), ZZRingElem}((almostone + preimage(f, b)) => e for (b, e) in y)
#  return FacElem(domain(f), D)
#end

function _unit_group_maximal_fac_elem(O::AlgAssAbsOrd)
  A = algebra(O)
  fields_and_maps = as_number_fields(A)
  unit_groups = Tuple{FinGenAbGroup, MapUnitGrp{FacElemMon{AbsSimpleNumField}}}[unit_group_fac_elem(maximal_order(field)) for (field, map) in fields_and_maps ]
  G = unit_groups[1][1]
  for i = 2:length(unit_groups)
    G = direct_product(G, unit_groups[i][1], task = :none)::FinGenAbGroup
  end
  S, StoG = snf(G)

  local disc_exp
  let StoG = StoG, unit_groups = unit_groups, fields_and_maps = fields_and_maps
    function disc_exp(x::FinGenAbGroupElem)
      g = StoG(x)
      v = FacElem(one(A))
      offset = 1
      for i = 1:length(fields_and_maps)
        K, AtoK = fields_and_maps[i]
        U, mU = unit_groups[i]
        u = U(sub(g.coeff, 1:1, offset:(offset + ngens(U) - 1)))
        v *= _preimage_fac_elem(AtoK, mU(u), i, fields_and_maps)
        offset += ngens(U)
      end
      return v
    end
  end

  local disc_log
  let fields_and_maps = fields_and_maps, unit_groups = unit_groups, StoG = StoG, G = G
    function disc_log(x::FacElem)
      g = zero_matrix(FlintZZ, 1, 0)
      for i = 1:length(fields_and_maps)
        K, AtoK = fields_and_maps[i]
        U, mU = unit_groups[i]
        y = _image_fac_elem(AtoK, x)
        u = mU\y
        g = hcat(g, u.coeff)
      end
      return StoG\G(g)
    end
  end

  StoO = MapUnitGrp{FacElemMon{typeof(A)}}()
  StoO.header = MapHeader(S, FacElemMon(A), disc_exp, disc_log)
  return S, StoO
end

function _unit_group_maximal(O::AlgAssAbsOrd)
  A = algebra(O)
  fields_and_maps = as_number_fields(A)
  unit_groups = Tuple{FinGenAbGroup, MapUnitGrp{AbsSimpleNumFieldOrder}}[ unit_group(maximal_order(field)) for (field, map) in fields_and_maps ]
  G = unit_groups[1][1]
  for i = 2:length(unit_groups)
    G = direct_product(G, unit_groups[i][1], task = :none)::FinGenAbGroup
  end
  S, StoG = snf(G)

  local disc_exp
  let StoG = StoG, unit_groups = unit_groups, fields_and_maps = fields_and_maps
    function disc_exp(x::FinGenAbGroupElem)
      g = StoG(x)
      v = zero(O)
      offset = 1
      for i = 1:length(fields_and_maps)
        K, AtoK = fields_and_maps[i]
        U, mU = unit_groups[i]
        u = U(sub(g.coeff, 1:1, offset:(offset + ngens(U) - 1)))
        v += O(AtoK\elem_in_nf(mU(u), copy = false))
        offset += ngens(U)
      end
      return v
    end
  end

  local disc_log
  let fields_and_maps = fields_and_maps, unit_groups = unit_groups, StoG = StoG, G = G
    function disc_log(x::AlgAssAbsOrdElem)
      g = zero_matrix(FlintZZ, 1, 0)
      for i = 1:length(fields_and_maps)
        K, AtoK = fields_and_maps[i]
        U, mU = unit_groups[i]
        OK = codomain(mU)
        y = OK(AtoK(elem_in_algebra(x, copy = false)))
        @assert is_unit(y)
        u = mU\y
        g = hcat(g, u.coeff)
      end
      return StoG\G(g)
    end
  end

  StoO = MapUnitGrp{typeof(O)}()
  StoO.header = MapHeader(S, O, disc_exp, disc_log)
  return S, StoO
end

# Returns the group (O_A/F)^\times/(O/F)^\times and a map from this group to
# O_A/F where F is the conductor of O in the maximal order O_A.
function OO_mod_F_mod_O_mod_F(O::AlgAssAbsOrd)
  OA = maximal_order(algebra(O))
  F = conductor(O, OA, :left)
  FOA = F*OA
  Q1, toQ1 = quo(OA, FOA)
  H1, H1toQ1 = unit_group(Q1)
  Q2, toQ2 = quo(O, F)
  H2, H2toQ2 = unit_group(Q2)
  H2inH1, _ = sub(H1, [ H1toQ1\(toQ1(OA(elem_in_algebra(toQ2\(H2toQ2(H2[i])), copy = false)))) for i = 1:ngens(H2) ])
  H, toH = quo(H1, H2inH1)
  S, StoH = snf(H)
  local _disc_log
  let toH = toH, StoH = StoH, Q1 = Q1
    function _disc_log(x)
      @assert parent(x) === Q1
      s = StoH\(toH(H1toQ1\x))
      return s.coeff
    end
  end

  StoQ1 = GrpAbFinGenToAbsOrdQuoRingMultMap(S, Q1, [ H1toQ1(toH\(StoH(S[i]))) for i = 1:ngens(S) ], _disc_log)
  return S, StoQ1, toQ1
end
# for _unit_group_non_maximal see AbsSimpleNumFieldOrder/PicardGroup.jl

# Given an order O in an étale algebra, determine the
# O^+ = {x \in O | x_v > 0 for v in rlpl}
function unit_group_positive(O::AlgAssAbsOrd, rlpl)
  U, mU = unit_group(O)
  co = components(Field, algebra(O))
  n = sum(length.(rlpl))
  A = abelian_group(fill(2, n))
  t = Vector{elem_type(A)}()
  for j in 1:ngens(U)
    u = elem_in_algebra(mU(gen(U, j)))
    imu = Int[]
    for i in 1:length(co)
      uinK = co[i][2](u)
      for r in rlpl[i]
        @assert number_field(r) === co[i][1]
        if is_positive(uinK, r)
          push!(imu, 0)
        else
          push!(imu, 1)
        end
      end
    end
    push!(t, A(imu))
  end
  h = hom(U, A, t)
  K, KtoU = kernel(h)
  S, StoK = snf(K)
  StoU = StoK * KtoU

  exp = function(s)
    @assert parent(s) === S
    return mU(StoU(s))
  end

  log = function(uu)
    @assert parent(uu) === O
    kk = mU\uu
    fl, k = has_preimage_with_preimage(StoU, kk)
    if !fl
      error("Element not positive at described places")
    end
    return k
  end

  StoO = MapUnitGrp{typeof(O)}()
  StoO.header = MapHeader(S, O, exp, log)
  return S, StoO
end

# Determine the kernel of
# O^\times -> (O/g*oo)^
# O must be maximal order in an étale algebra
# mU is the unit group (map) of O
function _unit_group_one_units(O::AlgAssAbsOrd, g, real_places, mU)
  A = algebra(O)
  U = domain(mU)
  Q, mQ = quo(O, g)
  Quni, mQuni = unit_group(Q)
  c = components(Field, A)
  # At the moment I don't need the "exponent" map, so I will do the obvious
  # thing to deal with the infinite places. If one ever wants the exponent
  # map, one would have to patch together
  # infinite_primes_map(OK, p, m)
  # for the different components of A.
  npl = sum(length.(real_places))
  T = abelian_group(fill(2, npl))
  D, (QuniToD, TtoD) = direct_product(Quni, T, task = :sum)
  @assert domain(QuniToD) === Quni
  @assert domain(TtoD) === T
  imgs = elem_type(D)[]
  for a in gens(U)
    u = mU(a)
    img_inf = Int[]
    for i in 1:length(c)
      K, KtoC = c[i]
      for r in real_places[i]
        if sign(KtoC(elem_in_algebra(u)), r) == 1
          push!(img_inf, 0)
        else
          push!(img_inf, 1)
        end
      end
    end
    u_img_inf = T(img_inf)
    push!(imgs, QuniToD((mQuni\(mQ(u)))) + TtoD(u_img_inf))
  end
  h = hom(U, D, imgs)
  K, KtoU = kernel(h)
  S, StoK = snf(K)
  return S, (StoK * KtoU)
end
