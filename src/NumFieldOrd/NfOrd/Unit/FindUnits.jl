################################################################################
#
#  Compute unit group from class group context
#
################################################################################

function _unit_group(O::AbsSimpleNumFieldOrder, c::ClassGrpCtx)
  u = UnitGrpCtx{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}(O)
  _unit_group_find_units(u, c)
  return u
end

function find_candidates(x::ClassGrpCtx, u::UnitGrpCtx, add::Int = 0)
  time_kernel = 0.0
  add_units = Int[]
  rel = sparse_matrix(ZZ)
  K = nf(x)
  r1, r2 = signature(K)
  nrel = max(10, r1+r2-1)
  if nrel > nrows(x.M.rel_gens)
    nrel = nrows(x.M.rel_gens)
  end
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
  for i = 1:add
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
  @vprintln :UnitGroup 1 "Saturating the kernel"
  @vtime_add_elapsed :UnitGroup 1 x :saturate_time s = saturate(hcat(k, (-d)*identity_matrix(SMat, FlintZZ, k.r)))
  @vprintln :UnitGroup 1 "Done"
  s1 = matrix(s)
  lll!(s1)
  @vprintln :UnitGroup 1 "Kernel time: $time_kernel"
  @vtime_add :UnitGroup 1 x :unit_hnf_time time_kernel
  return k, add_units, s1
end

function _unit_group_find_units(u::UnitGrpCtx, x::ClassGrpCtx; add_orbit::Bool = true, expected_reg::ArbFieldElem = ArbField(32, cached = false)(-1), add::Int = 0)
  add_orbit = false
  @vprintln :UnitGroup 1 "Processing ClassGrpCtx to find units ... (using orbits: $add_orbit)"
  @vprintln :UnitGroup 1 "Relation module $(x.M)"

  O = order(u)

  K = nf(order(x.FB.ideals[1]))
  r = unit_group_rank(O)

  if r == 0
    Ar = ArbField(u.indep_prec, cached = false)
    u.tentative_regulator = Ar(1)
    u.regulator = Ar(1)
    u.regulator_precision = u.indep_prec
    u.full_rank = true
    return 1, 0
  end

  # I am not allowed to do this before the other block
  if nrows(x.M.rel_gens) == 0
    @vprintln :UnitGroup 1 "No additional relations. Going back ..."
    return 0, 0
  end

  time_indep = 0.0
  time_add_dep_unit = 0.0
  time_torsion = 0.0
  not_larger = 0

  @vprintln :UnitGroup 1 "Enlarging unit group by adding kernel elements ..."

  starting_full_rank = has_full_rank(u)
  if starting_full_rank
    starting_idx = _validate_class_unit_group(x, u)[1]
  else
    starting_idx = 0
  end

  not_larger_bound = min(20, nrows(x.M.rel_gens), r)

  first = true
  if has_full_rank(u)
    first = false
    add += 2 #+ div(nrows(x.M.rel_gens), r)
  end
  if !isdefined(u, :relations_used)
    u.relations_used = Vector{Int}()
  end
  finished = false

  if add_orbit
    aut = automorphism_list(u)
    gens_aut = small_generating_set(aut)
    indices_aut = Int[]
    for s = 1:length(gens_aut)
      for j = 1:length(aut)
        if aut[j] == gens_aut[s]
          push!(indices_aut, j)
          break
        end
      end
    end
  end
  new_add = 0
  while not_larger < not_larger_bound
    add += new_add
    new_add = 2
    k, add_units, s1 = find_candidates(x, u, add)

    ge = vcat(x.R_gen[1:k.c], x.R_rel[add_units])
    elements = Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}(undef, nrows(s1))
    for i = 1:nrows(s1)
      elements[i] = FacElem(ge, ZZRingElem[s1[i, j] for j = 1:ncols(s1)])
    end
    p = 32
    if has_full_rank(u)
      elements = reduce_mod_units(elements, u)
    end
    #I order the elements by the maximum of the conjugate log.
    m_conjs = Vector{ZZRingElem}(undef, length(elements))
    for i = 1:length(m_conjs)
      m_conjs[i] = maximum(ZZRingElem[abs_upper_bound(ZZRingElem, x) for x in conjugates_arb_log(elements[i], p)])
    end
    p_elements = sortperm(m_conjs)
    elements = elements[p_elements]
    done = falses(length(elements))
    for i = 1:length(elements)
      @vprintln :UnitGroup 1 "Element $(i) / $(length(elements))"
      y = elements[i]
      @hassert :UnitGroup 2 _isunit(y)
      @vprintln :UnitGroup 1 "(It really is a unit.)"
      @hassert :UnitGroup 9000 denominator(minpoly(evaluate(y))) == 1

      if has_full_rank(u)
        @vprintln :UnitGroup 2 "have full rank, can reduce unit first..."
        y = reduce_mod_units(FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[y], u)[1]
      else
        @vprintln :UnitGroup 2 "no full rank, cannot reduce unit first..."
      end

      @vprintln :UnitGroup 1 "Exponents are of bit size $(isempty(y.fac) ? 0 : maximum([ nbits(o) for o in values(y.fac)]))"
      @vprintln :UnitGroup 1 "Test if kernel element yields torsion unit ..."

      @v_do :UnitGroup 2 pushindent()
      time_torsion += @elapsed is_tors, p1 = is_torsion_unit(y, false, u.tors_prec)
      @v_do :UnitGroup 2 popindent()

      u.tors_prec = max(p1, u.tors_prec)
      p = max(p, u.tors_prec)
      if is_tors
        @vprintln :UnitGroup 1 "Element is torsion unit"
        not_larger += 1
        # We do break out of the for loop if not_larger > not_larger_bound,
        # because otherwise we do not check all kernel elements
        done[i] = true
        continue
      end

      @vprintln :UnitGroup 1 "Element is non-torsion unit"

      @v_do :UnitGroup 2 pushindent()

      m = add_unit!(u, y)
      if m
        new_add = 0
        done[i] = true
        not_larger = 0
        if has_full_rank(u)
          @vprintln :UnitGroup 1 "improved reg, reg is $(tentative_regulator(u))"
          if first
            idx, expected_reg = _validate_class_unit_group(x, u)
            first = false
          end
          if expected_reg > divexact(abs(tentative_regulator(u)), 2)
            done = trues(length(elements))
            not_larger = not_larger_bound + 1
            finished = true
            @v_do :UnitGroup 2 popindent()
            break
          end
          if add_orbit
            for j  in indices_aut
              phiu = apply_automorphism(u, j, y)
              if add_unit!(u, phiu)
                @vprintln :UnitGroup 1 "New regulator: $(tentative_regulator(u))"
                not_larger = 0
              end
            end
          end
        else
          @vprintln :UnitGroup 1 "Increased rank by 1 (now $(rank(u)))"
        end
      else
        if has_full_rank(u)
          done[i] = true
        end
        not_larger = not_larger + 1
        # We do break out of the for loop if not_larger > not_larger_bound,
        # because otherwise we do not check all kernel elements
      end

      @v_do :UnitGroup 2 popindent()
    end  #for loop


    if has_full_rank(u)
      add_done = false
      for i = 1:length(elements)
        if !done[i]
          time_torsion += @elapsed is_tors, p1 = is_torsion_unit(elements[i], false, u.tors_prec)
          u.tors_prec = max(p1, u.tors_prec)
          p = max(p, u.tors_prec)
          if is_tors
            @vprintln :UnitGroup 1 "Element is torsion unit"
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
      u.units = reduce(u.units, u.tors_prec)
    end

    if finished
      break
    end
    if not_larger > not_larger_bound && length(u.relations_used) != nrows(x.M.rel_gens)
      not_larger = 0
    end
  end
  @vprintln :UnitGroup 1 "Finished processing"
  if has_full_rank(u)
    u.tentative_regulator = regulator(u.units, 64)
    @vprintln :UnitGroup 1 "Regulator of current unit group is $(u.tentative_regulator)"
  else
    @vprintln :UnitGroup 1 "current rank is $(length(u.units)), need $r"
  end
  @vprintln :UnitGroup 1 "-"^80 * ""
  @vprintln :UnitGroup 1 "Independent unit time: $time_indep"
  @vprintln :UnitGroup 1 "Adding dependent unit time: $time_add_dep_unit"
  @vprintln :UnitGroup 1 "Torsion test time: $time_torsion"



  if starting_full_rank
    return 1, div(starting_idx, _validate_class_unit_group(x, u)[1])
  elseif has_full_rank(u)
    return 1, 0
  else
    return 0, 0
  end
end


function compute_galois_closure!(U::UnitGrpCtx, c::ClassGrpCtx)
  @vprintln :UnitGroup 1 "Computing Galois closure"
  aut = automorphism_list(U)
  gens_aut = small_generating_set(aut)
  indices_aut = Int[]
  for s = 1:length(gens_aut)
    for j = 1:length(aut)
      if aut[j] == gens_aut[s]
        push!(indices_aut, j)
        break
      end
    end
  end
  found_new = true
  while found_new
    found_new = false
    for i = 1:length(indices_aut)
      for j = 1:length(U.units)
        @vprintln :UnitGroup 1 "Applying auto"
        uphi = apply_automorphism(U, indices_aut[i], U.units[j])
        @vprintln :UnitGroup 1 "Adding unit"
        fl = add_unit!(U, uphi)
        if fl
          @vprintln :UnitGroup 1 "Found new unit!"
          found_new = true
          idx = _validate_class_unit_group(c, U)[1]
          if isone(idx)
            return nothing
          end
        end
      end
    end
  end
  return nothing

end
