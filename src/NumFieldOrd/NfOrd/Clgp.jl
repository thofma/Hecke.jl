################################################################################
#
#     Clgrp.jl : Class group computation of maximal orders in number fields
#
# This file is part of hecke.
#
# Copyright (c) 2015: Claus Fieker, Tommy Hofmann
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
#
# (C) 2015, 2016 Claus Fieker
#
################################################################################
#
# Todo:
#  - make sure the precision for LLL is high enough (by checking that the
#    resulting elements have a reasonable norm/ length? theory?)
#    done
#  - add reasonable verbose printing
#    done
#  - write hnf from upper_triangular
#  - understand/use profiling information (memory, ...)
#
#  - need different norm function: modular resultant? with a large known
#    factor AND without any proof...
#    otherwise, it takes much too long if the ideal is non-trivial
#  DONE (norm_div)
#
#  - move the various factor, is_smooth and similar to a sensible
#    spot. This has nothing to do with class groups
#  - the SingleP version:
#      figure out if a union is better than the current version
#      ie have a version for easy primes
#         and a dumb version as fallback
#      make sure stuff works with fractionals as well!
#      just scaling by the den can affect smoothness (incomplete factor base)
#
#
# Clean up:
#  - write show functions
#  - export
#
# Note: enumerating x,0,0,0 is pointless unless x==1
#
################################################################################

add_verbosity_scope(:ClassGroup)
add_verbosity_scope(:ClassGroup_time)
add_verbosity_scope(:ClassGroup_gc)

add_assertion_scope(:ClassGroup)

include("Clgp/Ctx.jl")
include("Clgp/FacBase_Euc.jl")
include("Clgp/FacBase_Idl.jl")
include("Clgp/Main_enum.jl")
include("Clgp/Map.jl")
include("Clgp/Proof.jl")
include("Clgp/Rel_add.jl")
include("Clgp/Rel_enum.jl")
include("Clgp/Rel_LLL.jl")
include("Clgp/Main_LLL.jl")
include("Clgp/Rel_Schmettow.jl")
include("Clgp/Saturate.jl")
include("Clgp/Sunits.jl")
include("Clgp/cm_field.jl")
using .RelSaturate

################################################################################
#
#  Main function
#
################################################################################

function class_group_ctx(O::AbsSimpleNumFieldOrder; bound::Int = -1, method::Int = 3, large::Int = 1000, redo::Bool = false, use_aut::Bool = false)

  if !redo
    c = get_attribute(O, :ClassGrpCtx)
    if c !== nothing
      return c::ClassGrpCtx{SMat{ZZRingElem, ZZRingElem_Array_Mod.ZZRingElem_Array}}
    end
  end

  if bound == -1
    bound = factor_base_bound_grh(O)
    (bound == 0) && (bound = 1)
  end

  c = class_group_init(O, bound, complete = false, use_aut = use_aut)::ClassGrpCtx{SMat{ZZRingElem, ZZRingElem_Array_Mod.ZZRingElem_Array}}
  @assert order(c) === O

  set_attribute!(O, :ClassGrpCtx, c)

  c.B2 = bound * large

  if method == 2
    class_group_find_relations2(c)
  else
    d = isqrt(abs(discriminant(O)))
    c.expect = class_group_expected(c, 100)
    class_group_via_lll(c)
  end

  c.GRH = true

  return c
end

################################################################################
#
#  Verification
#
################################################################################

# think of a sensible function name

function _validate_class_unit_group(c::ClassGrpCtx, U::UnitGrpCtx)
  @vprintln :UnitGroup 1 "Validating unit group and class group ..."
  O = U.order

  # The residue of the zeta function cannot be computed for degree 1 (K = Q),
  # so we shortcircuit it.

  h = class_group_current_h(c)
  if degree(O) == 1
    if h == 1 && U.tentative_regulator == 1
      return ZZRingElem(1), U.tentative_regulator
    else
      error("Something odd for K = Q")
    end
  end

  if !isdefined(U, :torsion_units)
    @vprintln :UnitGroup 1 "Computing torsion structure ..."
    g, ord = torsion_units_gen_order(O)
    U.torsion_units_order = ord
    U.torsion_units_gen = g
  end

  @vprintln :UnitGroup 1 "Torsion structure done!"

  w = U.torsion_units_order

  if h == 1 && iszero(unit_group_rank(O))
    return ZZRingElem(1), U.tentative_regulator
  end

  r1, r2 = signature(O)

  if !isdefined(U, :residue)
    @vprintln :UnitGroup 1 "Computing residue of Dedekind zeta function ..."
    U.residue = zeta_log_residue(O, 0.6931/2)  #log(2)/2
  end
  residue = U.residue

  pre = precision(parent(residue))

  Ar = ArbField(pre, cached = false)

  loghRtrue = Ar(residue) + log(Ar(w)*sqrt(abs(Ar(discriminant(O))))//(Ar(2)^(r1+r2) * const_pi(Ar)^r2))

  # I should assert that radius(loghRtrue) < log(2)

  @assert isfinite(loghRtrue)

  @vprintln :ClassGroup 1 "tentative class group $h"
  @vprintln :ClassGroup 1 "tentative regulator $(tentative_regulator(U))"

  while true
    loghRapprox = log(h* abs(tentative_regulator(U)))

    @assert isfinite(loghRapprox)

    if contains(loghRtrue, loghRapprox)
      return ZZRingElem(1), abs(tentative_regulator(U))
    elseif !overlaps(loghRtrue, loghRapprox)
      e = exp(loghRapprox - loghRtrue)
      e_fmpz = abs_upper_bound(ZZRingElem, e)
      @vprintln :ClassGroup 1 "validate called, index bound is $e_fmpz"
      return e_fmpz, divexact(abs(tentative_regulator(U)), e_fmpz)
    end

    error("Not yet implemented")
  end
end

function class_group_current_h(c::ClassGrpCtx)
  module_trafo_assure(c.M)
  c.h = check_index(c.M)
  return c.h
end

function _class_unit_group(O::AbsSimpleNumFieldOrder; saturate_at_2::Bool = true, bound::Int = -1, method::Int = 3, large::Int = 1000, redo::Bool = false, unit_method::Int = 1, use_aut::Bool = false, GRH::Bool = true)

  @vprintln :UnitGroup 1 "Computing tentative class and unit group ..."

  @v_do :UnitGroup 1 pushindent()
  c = class_group_ctx(O, bound = bound, method = method, large = large, redo = redo, use_aut = use_aut)
  @v_do :UnitGroup 1 popindent()

  if c.finished
    U = get_attribute(O, :UnitGrpCtx)::UnitGrpCtx{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}
    @assert U.finished
    @vprintln :UnitGroup 1 "... done (retrieved)."
    if c.GRH && !GRH
      if !GRH
        class_group_proof(c, ZZRingElem(2), factor_base_bound_minkowski(O))
        for (p, _) in factor(c.h)
          while saturate!(c, U, Int(p), 3.5)
          end
        end
      end
      c.GRH = false
    end
    return c, U, ZZRingElem(1)
  end

  @vprintln :UnitGroup 1 "Tentative class number is now $(c.h)"

  U = UnitGrpCtx{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}(O)

  need_more = true

  hnftime = 0.0

  r = 0

  do_units = true
  if length(c.M.rel_gens) < unit_group_rank(O)
    do_units = false
  end
  reg_expected = ArbField(32, cached = false)(-1)
  add = 0
  closed = false
  improved = 0
  while true
    @v_do :UnitGroup 1 pushindent()
    has_already_full_rank = has_full_rank(U)
    reg = ArbField(32, cached = false)(-1)
    if has_already_full_rank
      reg = tentative_regulator(U)
    end
    if do_units
      @vtime_add_elapsed :UnitGroup 1 c :unit_time r, improved = _unit_group_find_units(U, c, add_orbit = use_aut, expected_reg = reg_expected, add = add)
      add += 1
    end

    @v_do :UnitGroup 1 popindent()
    # r == 1 means full rank
    if isone(r)  # use saturation!!!!
      idx, reg_expected = _validate_class_unit_group(c, U)
      if isone(idx)
        break
      end

      stable = 3.5
      # No matter what, try a saturation at 2
      # This is not a good idea when we use the automorphisms.
      # In this case, the index may contain a large 2-power and saturation
      # will take forever.
      if isone(improved) && iszero(c.sat_done)
        @vprintln :ClassGroup 1 "Finite index, saturating at 2"
        while saturate!(c, U, 2, stable)
          @vprintln :ClassGroup 1 "Finite index, saturating at 2"
        end
        idx, reg_expected = _validate_class_unit_group(c, U)
        c.sat_done = 2
        if isone(idx)
          break
        end
      end
      if isone(improved) && use_aut
        #Compute Galois closure of the units
        compute_galois_closure!(U, c)
        idx, reg_expected = _validate_class_unit_group(c, U)
        if isone(idx)
          break
        end
      end
      while (!use_aut && idx < 20 && idx > 1) || (idx < 10 && idx > 1)
        @vprintln :ClassGroup 1 "Finishing by saturating up to $idx"
        fl = false
        p = 2
        while !fl && p < 2*Int(idx)
          fl = saturate!(c, U, p, stable)
          p = next_prime(p)
        end
        @assert fl  # so I can switch assertions off...
        c.sat_done = 2*Int(idx)
        n_idx, reg_expected = _validate_class_unit_group(c, U)
        @vprintln :ClassGroup 1 "index estimate down to $n_idx from $idx"
        @assert idx != n_idx
        idx = n_idx
      end
      if idx == 1
        break
      end
    end
    #TODO: use LLL?
    if need_more
      d = isqrt(abs(discriminant(O)))
      c.expect = class_group_expected(d, degree(O), Int(norm(c.FB.ideals[1])), 100)
      need_more = false
    end
    h_old = class_group_current_h(c)
    class_group_new_relations_via_lll(c, extra = unit_group_rank(O) - length(U.units) +1)
    if h_old == class_group_current_h(c)
      do_units = true
      if length(c.M.rel_gens) < unit_group_rank(O)
        do_units = false
      end
    else
      add += 2
      do_units = false
    end
  end
  @assert U.full_rank
  set_attribute!(O, :UnitGrpCtx => U)
  set_attribute!(O, :ClassGrpCtx => c)

  c.finished = true
  U.finished = true

  #@vprintln :ClassGroup 1 "hnftime $(c.time[:hnf_time])"

  if !GRH
    class_group_proof(c, ZZRingElem(2), factor_base_bound_minkowski(O))
    for (p, _) in factor(c.h)
      while saturate!(c, U, Int(p), 3.5)
      end
    end
    c.GRH = false
  end

  return c, U, _validate_class_unit_group(c, U)[1]
end

function unit_group_ctx(c::ClassGrpCtx; redo::Bool = false)
  O = order(c.FB.ideals[1])
  if !redo
    U = get_attribute(O, :UnitGrpCtx)::UnitGrpCtx
    if U !== nothing
      return U
    end
  end

  U = UnitGrpCtx{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}(O)
  need_more = true
  while true
    r = _unit_group_find_units(U, c)
    if r == 0
      if need_more
        d = isqrt(abs(discriminant(O)))
        c.expect = class_group_expected(d, degree(O), Int(norm(c.FB.ideals[1])), 100)
        need_more = false
      end
      class_group_new_relations_via_lll(c, E)
    else
      set_attribute!(O, :UnitGrpCtx => U)
      return U
    end
  end
end

function unit_group(c::ClassGrpCtx)
  U = unit_group_ctx(c)
  return unit_group(c, U)
end

function unit_group(c::ClassGrpCtx, U::UnitGrpCtx)
  O = order(c.FB.ideals[1])
  K = nf(O)
  U, mU = unit_group_fac_elem(U)

  r = MapUnitGrp{typeof(O)}()
  r.header = Hecke.MapHeader(U, O,
    x->O(evaluate(image(mU, x))),
    x->preimage(mU, FacElem([K(x)], ZZRingElem[1])))
  return U, r
end

@doc raw"""
    class_group(O::AbsSimpleNumFieldOrder; bound = -1,
                          redo = false,
                          GRH = true)   -> FinGenAbGroup, Map

Returns a group $A$ and a map $f$ from $A$ to the set of ideals of $O$. The
inverse of the map is the projection onto the group of ideals modulo the group
of principal ideals.

By default, the correctness is guarenteed only assuming the Generalized Riemann
Hypothesis (GRH).

Keyword arguments:

- `redo`: Trigger a recomputation, thus avoiding the cache.
- `bound`: When specified, this is used for the bound for the factor base.
- `GRH`: If `false`, the correctness of the result does not depend on GRH.
"""
function class_group(O::AbsSimpleNumFieldOrder; bound::Int = -1, method::Int = 3,
                     redo::Bool = false, unit_method::Int = 1,
                     large::Int = 1000, use_aut::Bool = is_automorphisms_known(nf(O)), GRH::Bool = true, do_lll::Bool = true,
                     saturate_at_2::Bool = true)
  if do_lll
   OK = maximal_order(nf(O))
    @assert OK.is_maximal == 1
    L = lll(OK)
    @assert L.is_maximal == 1
  else
    L = O
  end
  c, U, b = _class_unit_group(L, bound = bound, method = method, redo = redo, unit_method = unit_method, large = large, use_aut = use_aut, GRH = GRH, saturate_at_2 = saturate_at_2)

  @assert b == 1
  return class_group(c, O)::Tuple{FinGenAbGroup, MapClassGrp}
end

function _unit_group_maximal(O::AbsSimpleNumFieldOrder; method::Int = 3, unit_method::Int = 1, use_aut::Bool = false, GRH::Bool = true)
  c, U, b = _class_unit_group(O, method = method, unit_method = unit_method, use_aut = use_aut, GRH = GRH)
  @assert b==1
  return unit_group(c, U)::Tuple{FinGenAbGroup, MapUnitGrp{AbsNumFieldOrder{AbsSimpleNumField,AbsSimpleNumFieldElem}}}
end


@doc raw"""
    unit_group(O::AbsSimpleNumFieldOrder) -> FinGenAbGroup, Map

Returns a group $U$ and an isomorphism map $f \colon U \to \mathcal O^\times$.
A set of fundamental units of $\mathcal O$ can be
obtained via `[ f(U[1+i]) for i in 1:unit_group_rank(O) ]`.
`f(U[1])` will give a generator for the torsion subgroup.
"""
function unit_group(O::AbsSimpleNumFieldOrder; method::Int = 3, unit_method::Int = 1, use_aut::Bool = false, GRH::Bool = true)
  if is_maximal(O)
    return _unit_group_maximal(O, method = method, unit_method = unit_method, use_aut = use_aut, GRH = GRH)
  else
    return unit_group_non_maximal(O)::Tuple{FinGenAbGroup, MapUnitGrp{AbsNumFieldOrder{AbsSimpleNumField,AbsSimpleNumFieldElem}}}
  end
end

@doc raw"""
    unit_group_fac_elem(O::AbsSimpleNumFieldOrder) -> FinGenAbGroup, Map

Returns a group $U$ and an isomorphism map $f \colon U \to \mathcal O^\times$.
A set of fundamental units of $\mathcal O$ can be
obtained via `[ f(U[1+i]) for i in 1:unit_group_rank(O) ]`.
`f(U[1])` will give a generator for the torsion subgroup.
All elements will be returned in factored form.
"""
function unit_group_fac_elem(O::AbsSimpleNumFieldOrder; method::Int = 3, unit_method::Int = 1, use_aut::Bool = false, GRH::Bool = true, redo::Bool = false)
  if !is_maximal(O)
    OK = maximal_order(nf(O))
    UUU, mUUU = unit_group_fac_elem(OK)::Tuple{FinGenAbGroup, MapUnitGrp{FacElemMon{AbsSimpleNumField}}}
    return _unit_group_non_maximal(O, OK, mUUU)::Tuple{FinGenAbGroup, MapUnitGrp{FacElemMon{AbsSimpleNumField}}}
  end

  U = get_attribute(O, :UnitGrpCtx)
  if U !== nothing && U.finished
    return unit_group_fac_elem(U::UnitGrpCtx{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}})::Tuple{FinGenAbGroup, MapUnitGrp{FacElemMon{AbsSimpleNumField}}}
  end
  c = get_attribute(O, :ClassGrpCtx)
  if c === nothing
    O = lll(maximal_order(nf(O)))
  end
  _, UU, b = _class_unit_group(O, method = method, unit_method = unit_method, use_aut = use_aut, GRH = GRH, redo = redo)
  @assert b==1
  return unit_group_fac_elem(UU)::Tuple{FinGenAbGroup, MapUnitGrp{FacElemMon{AbsSimpleNumField}}}
end

@doc raw"""
    regulator(O::AbsSimpleNumFieldOrder)

Computes the regulator of $O$, i.e. the discriminant of the unit lattice.
"""
function regulator(O::AbsSimpleNumFieldOrder; method::Int = 3, unit_method::Int = 1, use_aut::Bool = false, GRH::Bool = true)
  c = get_attribute(O, :ClassGrpCtx)
  if c === nothing
    O = lll(maximal_order(nf(O)))
  end
  c, U, b = _class_unit_group(O, method = method, unit_method = unit_method, use_aut = use_aut, GRH = GRH)
  @assert b == 1
  unit_group_fac_elem(U)
  return U.tentative_regulator
end

@doc raw"""
    regulator(K::AbsSimpleNumField)

Computes the regulator of $K$, i.e. the discriminant of the unit lattice
for the maximal order of $K$.
"""
function regulator(K::AbsSimpleNumField)
  return regulator(maximal_order(K))
end
