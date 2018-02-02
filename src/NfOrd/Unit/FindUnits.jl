################################################################################
#
#  Compute unit group from class group context
#
################################################################################

function _unit_group(O::NfOrd, c::ClassGrpCtx)
  u = UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(O)
  _unit_group_find_units(u, c)
  return u
end

# TH:
# Current strategy
# ================
# Compute some "random" kernel elements using the transformation matrix to first
# find r independent units, where r is the unit rank.
# In the second round, try to enlarge the unit group with some random kernel
# elements.
function _unit_group_find_units_with_trafo(u::UnitGrpCtx, x::ClassGrpCtx)
  @vprint :UnitGroup 1 "Processing ClassGrpCtx to find units ... \n"

  @vprint :UnitGroup 1 "Relation module  $(x.M)\n"

  O = order(u)

  #ker = transpose(ker)

  K = nf(order(x.FB.ideals[1]))
  r = unit_rank(O)
  r1, r2 = signature(O)

  A = u.units

  j = 0

  dim_ker = length(x.M.rel_gens.rows) # dimension of the kernel

  total_dim = length(x.M.bas_gens.rows) + dim_ker

  kelem = fmpz[ 0 for i in 1:total_dim ]

  trafos = x.M.trafo

  MAX_RND_RD_1 = 2*r

  time_indep = 0.0
  time_add_dep_unit = 0.0
  time_kernel = 0.0
  time_torsion = 0.0

  while(length(A) < r)

    for i in 1:length(kelem)
      kelem[i] = 0
    end

    if j > MAX_RND_RD_1
      return 0
    end
    @vprint :UnitGroup 1 "Found $(length(A)) independent units so far ($(r - length(A)) left to find)\n"
    j = j + 1

    for i in 1:dim_ker
      kelem[end - i + 1] = rand(0:1)
    end

    time_kernel += @elapsed for i in length(trafos):-1:1
      apply_right!(kelem, trafos[i])
    end

    _make_row_primitive!(kelem)

    y = FacElem(vcat(x.R_gen, x.R_rel), kelem)

    time_torsion += @elapsed is_tors, p = istorsion_unit(y, false, u.tors_prec)
    u.tors_prec = max(p, u.tors_prec)
    if is_tors
      continue
    end

    @vprint :UnitGroup 1 "Exponents are of bit size $(maximum([ nbits(o) for o in kelem]))\n"

    time_indep += @elapsed _add_unit(u, y)

  end

  @vprint :UnitGroup 1 "Found $r linear independent units \n"

  @vprint :UnitGroup 1 "Independent unit time: $time_indep\n"
  @vprint :UnitGroup 1 "Adding dependent unit time: $time_add_dep_unit\n"
  @vprint :UnitGroup 1 "Torsion test time: $time_torsion\n"
  @vprint :UnitGroup 1 "Kernel time: $time_kernel\n"

  u.full_rank = true

  u.units = reduce(u.units, u.tors_prec)

  not_larger = 0

  @vprint :UnitGroup 1 "Enlarging unit group by adding more kernel basis elements ...\n"
  while not_larger < 3 

    for i in 1:length(kelem)
      kelem[i] = 0
    end

    for i in 1:dim_ker
      kelem[end - i + 1] = rand(-2:2)
    end

    time_kernel += @elapsed for i in length(trafos):-1:1
      apply_right!(kelem, trafos[i])
    end

    y = FacElem(vcat(x.R_gen, x.R_rel), kelem)

    @hassert :UnitGroup 2 _isunit(y)
    @vprint :UnitGroup 2 "Reduce 1st...\n"
    y = reduce_mod_units([y], u)[1]

    @vprint :UnitGroup 2 "Test if kernel element yields torsion unit ... \n"
    @v_do :UnitGroup 2 pushindent()
    time_torsion += @elapsed is_tors, p = istorsion_unit(y, false, u.tors_prec)
    u.tors_prec = max(p, u.tors_prec)
    if is_tors
      @v_do :UnitGroup 2 popindent()
      @vprint :UnitGroup 2 "Element is torsion unit\n"
      continue
    end
    @v_do :UnitGroup 2 popindent()

    @v_do :UnitGroup 2 pushindent()
    time_add_dep_unit += @elapsed m = _add_dependent_unit(u, y)
    @v_do :UnitGroup 2 popindent()

    if !m
      not_larger = not_larger + 1
    else
      not_larger = 0
    end
  end
  #final reduction ...
  u.units = reduce(u.units, u.tors_prec)

  u.tentative_regulator = regulator(u.units, 64)

  @vprint :UnitGroup 1 "Finished processing\n"
  @vprint :UnitGroup 1 "Regulator of current unit group is $(u.tentative_regulator)\n"
  @vprint :UnitGroup 1 "-"^80 * "\n"
  @vprint :UnitGroup 1 "Independent unit time: $time_indep\n"
  @vprint :UnitGroup 1 "Adding dependent unit time: $time_add_dep_unit\n"
  @vprint :UnitGroup 1 "Torsion test time: $time_torsion\n"
  @vprint :UnitGroup 1 "Kernel time: $time_kernel\n"
  @vtime_add :UnitGroup 1 x :unit_hnf_time time_kernel
  return 1
end

function _unit_group_find_units(u::UnitGrpCtx, x::ClassGrpCtx)
  @vprint :UnitGroup 1 "Processing ClassGrpCtx to find units ... \n"

  @vprint :UnitGroup 1 "Relation module $(x.M)\n"

  O = order(u)

  K = nf(order(x.FB.ideals[1]))
  r = unit_rank(O)

  if r == 0
    Ar = ArbField(u.indep_prec)
    u.tentative_regulator = Ar(1)
    u.regulator = Ar(1)
    u.regulator_precision = u.indep_prec
    u.full_rank = true
    return 1
  end

  r1, r2 = signature(O)

  A = u.units

  j = 0

  MAX_RND_RD_1 = 2*r

  time_indep = 0.0
  time_add_dep_unit = 0.0
  time_kernel = 0.0
  time_torsion = 0.0


  j = 0

  not_larger = 0

  @vprint :UnitGroup 1 "Enlarging unit group by adding kernel elements ...\n"
  while not_larger < 5 

    add_units = []
    rel = SMat{fmpz}()
    for jj in 1:min(div(rows(x.M.rel_gens), 10)+1, 20)
      xj = rand(1:rows(x.M.rel_gens))
      if xj in add_units
        continue
      end
      push!(add_units, xj)
      push!(rel, x.M.rel_gens[xj])
    end

    time_kernel += @elapsed k, d = solve_dixon_sf(x.M.bas_gens, rel)
    @vtime_add_elapsed :UnitGroup 1 x :saturate_time s = saturate(hcat(k, (-d)*id(SMat, FlintZZ, k.r)))

    ge = vcat(x.R_gen[1:k.c], x.R_rel[add_units])
    for i=1:s.r
      y = FacElem(ge[s[i].pos], s[i].values)
      @hassert :UnitGroup 2 _isunit(y)

      if u.full_rank
        y = reduce_mod_units([y], u)[1]
      end

      @vprint :UnitGroup 1 "Exponents are of bit size $(maximum([ nbits(o) for o in values(y.fac)]))\n"

      @vprint :UnitGroup 1 "Test if kernel element yields torsion unit ... \n"
      @v_do :UnitGroup 2 pushindent()
      time_torsion += @elapsed is_tors, p = istorsion_unit(y, false, u.tors_prec)
      u.tors_prec = max(p, u.tors_prec)
      if is_tors
        @v_do :UnitGroup 2 popindent()
        @vprint :UnitGroup 1 "Element is torsion unit\n"
        not_larger += 1
        if u.full_rank && not_larger > 5
          break
        end
        continue
      end
      @vprint :UnitGroup 1 "Element is non-torsion unit\n"
      @v_do :UnitGroup 2 popindent()

      @v_do :UnitGroup 2 pushindent()
      if u.full_rank
        time_add_dep_unit += @elapsed m = _add_dependent_unit(u, y)
        if m
          @vprint :UnitGroup 1 "improved reg, reg is $(regulator(u.units, 16))\n"
        end
      else
        old_len = length(u.units)
        time_add_dep_unit += @elapsed _add_unit(u, y)
        m = old_len == length(u.units)
        if m
          u.units = reduce(u.units)
        end
        u.full_rank = length(u.units) == r
        if u.full_rank
          @vprint :UnitGroup 1 "reached full rank, reg is $(regulator(u.units, 16))\n"
        end
      end
      @v_do :UnitGroup 2 popindent()

      if !m
        not_larger = not_larger + 1
        if u.full_rank && not_larger > 5
          break
        end
      else
        not_larger = 0
      end
    end
  end

  #final reduction ...
  u.units = reduce(u.units, u.tors_prec)

  u.tentative_regulator = regulator(u.units, 64)

  @vprint :UnitGroup 1 "Finished processing\n"
  @vprint :UnitGroup 1 "Regulator of current unit group is $(u.tentative_regulator)\n"
  @vprint :UnitGroup 1 "-"^80 * "\n"
  @vprint :UnitGroup 1 "Independent unit time: $time_indep\n"
  @vprint :UnitGroup 1 "Adding dependent unit time: $time_add_dep_unit\n"
  @vprint :UnitGroup 1 "Torsion test time: $time_torsion\n"
  @vprint :UnitGroup 1 "Kernel time: $time_kernel\n"

  @vtime_add :UnitGroup 1 x :unit_hnf_time time_kernel
  return 1
end


