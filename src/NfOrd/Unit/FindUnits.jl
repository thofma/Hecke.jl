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
function _unit_group_find_units_with_transform(u::UnitGrpCtx, x::ClassGrpCtx; add_orbit::Bool = false)
  @assert false

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

    @assert length(kelem) == length(x.R_gen) + length(x.R_rel)

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

    @assert length(kelem) == length(x.R_gen) + length(x.R_rel)

    y = FacElem(vcat(x.R_gen, x.R_rel), kelem)

    time_torsion += @elapsed is_tors, p = istorsion_unit(y, false, u.tors_prec)
    u.tors_prec = max(p, u.tors_prec)
    if is_tors
      continue
    end

    @vprint :UnitGroup 1 "Exponents are of bit size $(maximum([ nbits(o) for o in kelem]))\n"

    if add_orbit
      for phi in aut
        time_indep += @elapsed _add_unit(u, phi(y))
      end
    else
      time_indep += @elapsed _add_unit(u, y)
    end
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

    @assert length(kelem) == length(x.R_gen) + length(x.R_rel)

    for i in 1:length(kelem)
      kelem[i] = 0
    end

    for i in 1:dim_ker
      kelem[end - i + 1] = rand(-2:2)
    end

    time_kernel += @elapsed for i in length(trafos):-1:1
      apply_right!(kelem, trafos[i])
    end

    @assert length(kelem) == length(x.R_gen) + length(x.R_rel)

    y = FacElem(vcat(x.R_gen, x.R_rel), kelem)

    @hassert :UnitGroup 2 _isunit(y)
    @vprint :UnitGroup 2 "Reduce 1st...\n"
    y = reduce_mod_units([y], u)[1]

    @vprint :UnitGroup 2 "Test if kernel element yields torsion unit ... \n"
    @v_do :UnitGroup 2 pushindent()
    time_torsion += @elapsed is_tors, p = istorsion_unit(y, false, u.tors_prec)
    @v_do :UnitGroup 2 popindent()
    u.tors_prec = max(p, u.tors_prec)
    if is_tors
      @vprint :UnitGroup 2 "Element is torsion unit\n"
      not_larger = not_larger + 1
      continue
    end

    @v_do :UnitGroup 2 pushindent()
    if add_orbit
      for phi in aut
        time_add_dep_unit += @elapsed m = _add_dependent_unit(u, phi(y))::Bool
      end
    else
      time_add_dep_unit += @elapsed m = _add_dependent_unit(u, y)::Bool
    end
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


function find_candidates(x::ClassGrpCtx, u::UnitGrpCtx)
  time_kernel = 0.0
  add_units = Int[]
  rel = SMat{fmpz}()
  K = nf(x)
  r1, r2 = signature(K)
  nrel = min(10, r1+r2-1, nrows(x.M.rel_gens))
  while length(add_units) < nrel
    xj = rand(1:nrows(x.M.rel_gens))
    if length(u.relations_used) != nrows(x.M.rel_gens)
      if xj in add_units || xj in u.relations_used
        continue
      end
      push!(u.relations_used, xj)
    else
      if xj in add_units 
        continue
      end
    end
    push!(add_units, xj)
    push!(rel, x.M.rel_gens[xj])
  end
  time_kernel += @elapsed k, d = solve_dixon_sf(x.M.bas_gens, rel)
  @vprint :UnitGroup 1 "Saturating the kernel\n"
  @vtime_add_elapsed :UnitGroup 1 x :saturate_time s = saturate(hcat(k, (-d)*identity_matrix(SMat, FlintZZ, k.r)))
  @vprint :UnitGroup 1 "Done\n"
  s1 = matrix(s)
  lll!(s1)
  @vprint :UnitGroup 1 "Kernel time: $time_kernel\n"
  @vtime_add :UnitGroup 1 x :unit_hnf_time time_kernel
  return k, add_units, s1
end

function _unit_group_find_units(u::UnitGrpCtx, x::ClassGrpCtx; add_orbit::Bool = true, expected_reg::arb = ArbField(32, cached = false)(-1))
  add_orbit = false
  @vprint :UnitGroup 1 "Processing ClassGrpCtx to find units ... (using orbits: $add_orbit)\n"
  @vprint :UnitGroup 1 "Relation module $(x.M)\n"

  O = order(u)

  K = nf(order(x.FB.ideals[1]))
  r = unit_rank(O)

  if r == 0
    Ar = ArbField(u.indep_prec, cached = false)
    u.tentative_regulator = Ar(1)
    u.regulator = Ar(1)
    u.regulator_precision = u.indep_prec
    u.full_rank = true
    return 1
  end

  # I am not allowed to do this before the other block
  if nrows(x.M.rel_gens) == 0
    @vprint :UnitGroup 1 "No additional relations. Going back ...\n"
    return 0
  end



  r1, r2 = signature(O)

  A = u.units

  j = 0

  MAX_RND_RD_1 = 2*r

  time_indep = 0.0
  time_add_dep_unit = 0.0
  
  time_torsion = 0.0


  j = 0

  not_larger = 0

  @vprint :UnitGroup 1 "Enlarging unit group by adding kernel elements ...\n"

  not_larger_bound = min(20, nrows(x.M.rel_gens), r)

  first = true
  if has_full_rank(u)
    first = false
  end
  if !isdefined(u, :relations_used)
    u.relations_used = Vector{Int}()
  end
  finished = false
  while not_larger < not_larger_bound 
    k, add_units, s1 = find_candidates(x, u)
    ge = vcat(x.R_gen[1:k.c], x.R_rel[add_units])
    elements = Vector{FacElem{nf_elem, AnticNumberField}}(undef, nrows(s1))
    for i = 1:nrows(s1)
      elements[i] = FacElem(ge, fmpz[s1[i, j] for j = 1:ncols(s1)])
    end
    p = 32
    if has_full_rank(u)
      elements = reduce_mod_units(elements, u)
    end
    #I order the elements by the maximum of the conjugate log.
    m_conjs = Vector{fmpz}(undef, length(elements))
    for i = 1:length(m_conjs)
      m_conjs[i] = maximum(fmpz[abs_upper_bound(x, fmpz) for x in conjugates_arb_log(elements[i], p)])
    end
    p_elements = sortperm(m_conjs)
    elements = elements[p_elements]
    done = falses(length(elements))
    for i=1:length(elements)
      @vprint :UnitGroup 1 "Element $(i) / $(length(elements))\n"
      y = elements[i]
      @hassert :UnitGroup 2 _isunit(y)
      @vprint :UnitGroup 1 "(It really is a unit.)\n"
      @hassert :UnitGroup 9000 denominator(minpoly(evaluate(y))) == 1

      if has_full_rank(u)
        @vprint :UnitGroup 2 "have full rank, can reduce unit first...\n"
        y = reduce_mod_units(FacElem{nf_elem, AnticNumberField}[y], u)[1]
      else
        @vprint :UnitGroup 2 "no full rank, cannot reduce unit first...\n"
      end

      @vprint :UnitGroup 1 "Exponents are of bit size $(isempty(y.fac) ? 0 : maximum([ nbits(o) for o in values(y.fac)]))\n"
      @vprint :UnitGroup 1 "Test if kernel element yields torsion unit ... \n"

      @v_do :UnitGroup 2 pushindent()
      time_torsion += @elapsed is_tors, p1 = istorsion_unit(y, false, u.tors_prec)
      @v_do :UnitGroup 2 popindent()

      u.tors_prec = max(p1, u.tors_prec)
      p = max(p, u.tors_prec)
      if is_tors
        @vprint :UnitGroup 1 "Element is torsion unit\n"
        not_larger += 1
        if has_full_rank(u) && not_larger > not_larger_bound
          break
        end
        done[i] = true
        continue
      end

      @vprint :UnitGroup 1 "Element is non-torsion unit\n"

      @v_do :UnitGroup 2 pushindent()

      m = add_unit!(u, y)
      if m 
        done[i] = true
        not_larger = 0 
        if has_full_rank(u) 
          @vprint :UnitGroup 1 "improved reg, reg is $(tentative_regulator(u))\n"
          if first
            idx, expected_reg = _validate_class_unit_group(x, u)
            first = false
          end
          if expected_reg > divexact(abs(tentative_regulator(u)), 2)
            done = trues(length(elements))
            not_larger = not_larger_bound + 1
            finished = true
            break
          end
        else
          @vprint :UnitGroup 1 "Increased rank by 1 (now $(rank(u)))\n"
        end
      else
        if has_full_rank(u)
          done[i] = true
        end
        not_larger = not_larger + 1
        if not_larger > not_larger_bound
          @v_do :UnitGroup 2 popindent()
          break
        end
      end

      @v_do :UnitGroup 2 popindent()
    end
    u.units = reduce(u.units, u.tors_prec)
    if add_orbit && rank(u) > r-div(r, 4)
      @vprint :UnitGroup 1 "Adding orbits\n"
      # I close the units via Galois action
      aut = automorphisms(u)
      for i = 1:length(u.units)
        threshold = 3
        for j = 1:length(aut)
          if aut[j] == id_hom(K)
            continue
          end
          phiu = apply_automorphism(u, j, u.units[i])
          if !add_unit!(u, phiu)
            not_larger += 1
            threshold -= 1
          else
            if has_full_rank(u)
	            @vprint :UnitGroup 1 "New regulator: $(tentative_regulator(u))\n"
            end
	          not_larger = 0
          end
          if iszero(threshold)
            break
          end
        end
        if not_larger > not_larger_bound
          break
        end
        if nrows(x.M.rel_gens) == not_larger_bound
          break
        end
      end
    end
    
    if has_full_rank(u)
      add_done = false
      for i = 1:length(elements)
        if !done[i]
          time_torsion += @elapsed is_tors, p1 = istorsion_unit(elements[i], false, u.tors_prec)
          @v_do :UnitGroup 2 popindent()

          u.tors_prec = max(p1, u.tors_prec)
          p = max(p, u.tors_prec)
          if is_tors
            @vprint :UnitGroup 1 "Element is torsion unit\n"
            done[i] = true
            continue
          end
          add_done = add_unit!(u, elements[i]) || add_done  
          if expected_reg > divexact(abs(tentative_regulator(u)), 2)
            done = trues(length(elements))
            not_larger = not_larger_bound + 1
            finished = true
            break
          end
        end
      end
      if add_done
        u.units = reduce(u.units, u.tors_prec)
      end
    end
    if finished
      break
    end
    if not_larger > not_larger_bound && length(u.relations_used) != nrows(x.M.rel_gens)
      not_larger = 0
    end
  end
  @vprint :UnitGroup 1 "Finished processing\n"
  if has_full_rank(u)
    u.tentative_regulator = regulator(u.units, 64)
    @vprint :UnitGroup 1 "Regulator of current unit group is $(u.tentative_regulator)\n"
  else
    @vprint :UnitGroup 1 "current rank is $(length(u.units)), need $r\n"
  end  
  @vprint :UnitGroup 1 "-"^80 * "\n"
  @vprint :UnitGroup 1 "Independent unit time: $time_indep\n"
  @vprint :UnitGroup 1 "Adding dependent unit time: $time_add_dep_unit\n"
  @vprint :UnitGroup 1 "Torsion test time: $time_torsion\n"
  

 
  if has_full_rank(u)
    return 1
  else
    return 0
  end
end
