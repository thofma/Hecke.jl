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
#  - move the various factor, issmooth and similar to a sensible
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

export class_group, FactorBase, issmooth, factor, lll_basis,
       unit_group_fac_elem, unit_group, regulator

add_verbose_scope(:ClassGroup)
add_verbose_scope(:ClassGroup_time)
add_verbose_scope(:ClassGroup_gc)

add_assert_scope(:ClassGroup)
set_assert_level(:ClassGroup, 0)
set_assert_level(:LatEnum, 0)

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
using .RelSaturate

################################################################################
#
#  Main function
#
################################################################################

function class_group_ctx(O::NfOrd; bound::Int = -1, method::Int = 3, large::Int = 1000, redo::Bool = false, use_aut::Bool = false)

  if !redo
    try
      c = _get_ClassGrpCtx_of_order(O)::ClassGrpCtx{SMat{fmpz}}
      return c
    catch e
    end
  end

  if bound == -1
    bound = Int(ceil(log(abs(discriminant(O)))^2*0.3))
    (bound == 0) && (bound = 1)
  end

  c = class_group_init(O, bound, complete = false, use_aut = use_aut)::ClassGrpCtx{SMat{fmpz}}

  _set_ClassGrpCtx_of_order(O, c)

  c.B2 = bound * large

  if method == 2
    class_group_find_relations2(c)
  else
    d = root(abs(discriminant(O)), 2)
    c.expect = class_group_expected(c, 100)
    class_group_via_lll(c)
  end

  return c
end

################################################################################
#
#  Verification
#
################################################################################

# think of a sensible function name

function _validate_class_unit_group(c::ClassGrpCtx, U::UnitGrpCtx)
  @vprint :UnitGroup 1 "Validating unit group and class group ... \n"
  O = U.order

  # The residue of the zeta function cannot be computed for degree 1 (K = Q),
  # so we shortcircuit it.

  h = class_group_current_h(c)
  if degree(O) == 1
    if h == 1 && U.tentative_regulator == 1
      return fmpz(1)
    else
      error("Something odd for K = Q")
    end
  end

  if !isdefined(U, :torsion_units)
    @vprint :UnitGroup 1 "Computing torsion structure ... \n"
    #U.torsion_units = torsion_units(O)
    g, ord = torsion_units_gen_order(O)
    U.torsion_units_order = ord
    U.torsion_units_gen = g
  end  

  @vprint :UnitGroup 1 "Torsion structure done!\n"

  w = U.torsion_units_order

  r1, r2 = signature(O)

  if !isdefined(U, :residue)
    @vprint :UnitGroup 1 "Computing residue of Dedekind zeta function ... \n"
    U.residue = zeta_log_residue(O, 0.6931/2)  #log(2)/2
  end
  residue = U.residue

  pre = prec(parent(residue))

  Ar = ArbField(pre, false)

  loghRtrue = Ar(residue) + log(Ar(w)*sqrt(abs(Ar(discriminant(O))))//(Ar(2)^(r1+r2) * const_pi(Ar)^r2))

  # I should assert that radius(loghRtrue) < log(2)

  @assert isfinite(loghRtrue)

  while true
    loghRapprox = log(h* abs(U.tentative_regulator))

    @assert isfinite(loghRapprox)

    if contains(loghRtrue, loghRapprox)
      return fmpz(1)
    elseif !overlaps(loghRtrue, loghRapprox)
      e = exp(loghRapprox - loghRtrue)
      e_fmpz = abs_upper_bound(e, fmpz)
      @vprint :ClassGroup 1 "validate called, index bound is $e_fmpz\n"
      return e_fmpz
    end

    error("Not yet implemented")
  end
end

function class_group_current_h(c::ClassGrpCtx)
  module_trafo_assure(c.M)
  c.h = check_index(c.M)
  return c.h
end

function _class_unit_group(O::NfOrd; bound::Int = -1, method::Int = 3, large::Int = 1000, redo::Bool = false, unit_method::Int = 1, use_aut::Bool = false)

  @vprint :UnitGroup 1 "Computing tentative class and unit group ... \n"

  @v_do :UnitGroup 1 pushindent()
  c = class_group_ctx(O, bound = bound, method = method, large = large, redo = redo, use_aut = use_aut)
  @v_do :UnitGroup 1 popindent()

  if c.finished
    U = _get_UnitGrpCtx_of_order(O)
    @assert U.finished
    @vprint :UnitGroup 1 "... done (retrieved).\n"
    return c, U, 1
  end

  @vprint :UnitGroup 1 "Tentative class number is now $(c.h)\n"

  U = UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(O)

  need_more = true

  hnftime = 0.0

  r = 0

  do_units = true
  while true
    @v_do :UnitGroup 1 pushindent()
    if do_units
      if unit_method == 1
        @vtime_add_elapsed :UnitGroup 1 c :unit_time r = _unit_group_find_units(U, c)
      else
        @vtime_add_elapsed :UnitGroup 1 c :unit_hnf_time module_trafo_assure(c.M)
        @vtime_add_elapsed :UnitGroup 1 c :unit_time r = _unit_group_find_units_with_trafo(U, c)
      end
      @v_do :UnitGroup 1 popindent()
    end
    if r == 1  # use saturation!!!!
      idx = _validate_class_unit_group(c, U) 
      @assert idx == _validate_class_unit_group(c, U)
      stable = 3.5
      if c.sat_done == 0
        @vprint :ClassGroup 1 "Finite index, saturating at 2\n"
        while saturate!(c, U, 2, stable)
          @vtime_add_elapsed :UnitGroup 1 c :unit_time r = _unit_group_find_units(U, c)
        end
        idx = _validate_class_unit_group(c, U) 
        c.sat_done = 2
      end
      while idx < 20 && idx > 1
        @vprint :ClassGroup 1 "Finishing by saturating up to $idx\n"
        fl = any(p->saturate!(c, U, p, stable), PrimesSet(1, 2*Int(idx)))
        @assert fl  # so I can switch assertions off...
        c.sat_done = 2*Int(idx)

        @vtime_add_elapsed :UnitGroup 1 c :unit_time r = _unit_group_find_units(U, c)
        n_idx = _validate_class_unit_group(c, U) 
        @vprint :ClassGroup 1 "index estimate down to $n_idx from $idx\n"
        @assert idx != n_idx
        idx = n_idx
      end  
      if idx == 1
        break
      end
    end
    #TODO: use LLL?
    if need_more
      d = root(abs(discriminant(O)), 2)
      c.expect = class_group_expected(d, degree(O), Int(norm(c.FB.ideals[1])), 100)
      need_more = false
    end
    h_old = class_group_current_h(c)
    class_group_new_relations_via_lll(c, extra = unit_rank(O) - length(U.units) +1)
    if h_old == class_group_current_h(c)
      do_units = true
    else
      do_units = false
    end
  end
  @assert U.full_rank
  _set_UnitGrpCtx_of_order(O, U)

  c.finished = true
  U.finished = true

  @vprint :ClassGroup 1 "hnftime $(c.time[:hnf_time])\n"

  return c, U, _validate_class_unit_group(c, U)
end

function unit_group_ctx(c::ClassGrpCtx; redo::Bool = false)
  O = order(c.FB.ideals[1])
  if !redo
    try
      U = _get_UnitGrpCtx_of_order(O)::UnitGrpCtx
      return U
    catch e
    end
  end

  U = UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(O)
  need_more = true
  while true
    r = _unit_group_find_units(U, c)
    if r == 0
      if need_more
        d = root(abs(discriminant(O)), 2)
        c.expect = class_group_expected(d, degree(O), Int(norm(c.FB.ideals[1])), 100)
        need_more = false
      end
      class_group_new_relations_via_lll(c, E)
    else
      _set_UnitGrpCtx_of_order(O, U)
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
  U, mU = unit_group_fac_elem(c, U)

  r = MapUnitGrp{typeof(U), typeof(O)}()
  r.header = Hecke.MapHeader(U, O,
    x->O(evaluate(image(mU, x))),
    x->preimage(mU, FacElem([K(x)], fmpz[1])))
  return U, r
end

@doc Markdown.doc"""
***
    class_group(O::NfOrd; bound = -1, method = 3, redo = false, large = 1000) -> GrpAbFinGen, Map

> Returns a group $A$ and a map $f$ from $A$ to the set of ideals of $O$.
> The inverse of the map is the projection onto the group of ideals modulo the 
> group of principal ideals.
> \texttt{redo} allows to trigger a re-computation, thus avoiding the cache.
> \texttt{bound}, when given, is the bound for the factor base.
"""
function class_group(O::NfOrd; bound::Int = -1, method::Int = 3, redo::Bool = false, unit_method::Int = 1, large::Int = 1000, use_aut::Bool = false)
  c, U, b = _class_unit_group(O, bound = bound, method = method, redo = redo, unit_method = unit_method, large = large, use_aut = use_aut)
  @assert b==1
  return class_group(c)
end


@doc Markdown.doc"""
***
    unit_group(O::NfOrd) -> GrpAbFinGen, Map

> Returns a group $U$ and an isomorphism map $f \colon U \to \mathcal O^\times$.
> A set of fundamental units of $\mathcal O$ can be
> obtained via `[ f(U[1+i]) for i in 1:unit_rank(O) ]`.
> `f(U[1])` will give a generator for the torsion subgroup.
"""
function unit_group(O::NfOrd; method::Int = 3, unit_method::Int = 1, use_aut::Bool = false)
  c, U, b = _class_unit_group(O, method = method, unit_method = unit_method, use_aut = use_aut)
  @assert b==1
  return unit_group(c, U)
end

@doc Markdown.doc"""
***
    unit_group_fac_elem(O::NfOrd) -> GrpAbFinGen, Map

> Returns a group $U$ and an isomorphism map $f \colon U \to \mathcal O^\times$.
> A set of fundamental units of $\mathcal O$ can be
> obtained via `[ f(U[1+i]) for i in 1:unit_rank(O) ]`.
> `f(U[1])` will give a generator for the torsion subgroup.
> All elements will be returned in factored form.
"""
function unit_group_fac_elem(O::NfOrd; method::Int = 3, unit_method::Int = 1, use_aut::Bool = false)
  c, U, b = _class_unit_group(O, method = method, unit_method = unit_method, use_aut = use_aut)
  @assert b==1
  return unit_group_fac_elem(c, U)
end

@doc Markdown.doc"""
    regulator(O::NfOrd)
> Computes the regulator of $O$, ie. the discriminant of the unit lattice.    
"""
function regulator(O::NfOrd; method::Int = 3, unit_method::Int = 1, use_aut::Bool = false)
  c, U, b = _class_unit_group(O, method = method, unit_method = unit_method, use_aut = use_aut)
  @assert b==1
  unit_group_fac_elem(c, U)
  return U.tentative_regulator
end

@doc Markdown.doc"""
    regulator(K::AnticNumberField)
> Computes the regulator of $K$, ie. the discriminant of the unit lattice 
> for the maximal order of $K$
"""
function regulator(K::AnticNumberField)
  return regulator(maximal_order(K))
end
