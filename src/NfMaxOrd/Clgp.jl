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
       unit_group_fac_elem, unit_group

add_verbose_scope(:ClassGroup)
add_verbose_scope(:ClassGroup_time)
add_verbose_scope(:ClassGroup_gc)

add_assert_scope(:ClassGroup)
set_assert_level(:ClassGroup, 0)
set_assert_level(:LatEnum, 0)

for i in ["Clgp/Ctx.jl"
          "Clgp/FacBase_Euc.jl"
          "Clgp/FacBase_Idl.jl"
          "Clgp/Main_enum.jl"
          "Clgp/Map.jl"
          "Clgp/Proof.jl"
          "Clgp/Rel_add.jl"
          "Clgp/Rel_enum.jl"
          "Clgp/Rel_LLL.jl"
          "Clgp/Main_LLL.jl"
          "Clgp/Rel_Schmettow.jl"]
  include(i)
end

################################################################################
#
#  Main function
#
################################################################################

function class_group_ctx(O::NfMaxOrd; bound::Int = -1, method::Int = 3, large = 1000, redo::Bool = false)

  if !redo
    try
      c = _get_ClassGrpCtx_of_order(O)::ClassGrpCtx
      return c
    end
  end

  if bound == -1
    bound = Int(ceil(log(abs(discriminant(O)))^2*0.3))
    (bound == 0) && (bound = 1)
  end

  c = class_group_init(O, bound, complete = false)
  c.B2 = bound * large

  if false # method==1
    class_group_find_relations(c)
  elseif method == 2
    class_group_find_relations2(c)
  else
    d = root(abs(discriminant(O)), 2)
    c.expect = class_group_expected(c, 100)
    class_group_via_lll(c)
  end

  _set_ClassGrpCtx_of_order(O, c)

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

  @vprint :UnitGroup 1 "Computing torsion structure ... \n"
  U.torsion_units = torsion_units(O)
  U.torsion_units_order = length(U.torsion_units)
  U.torsion_units_gen = torsion_units_gen(O)

  w = U.torsion_units_order

  r1, r2 = signature(O)

  @vprint :UnitGroup 1 "Computing residue of Dedekind zeta function ... \n"
  residue = zeta_log_residue(O, 0.6931/2)  #log(2)/2

  pre = prec(parent(residue))

  Ar = ArbField(pre)

  loghRtrue = Ar(residue) + log(Ar(w)*sqrt(abs(Ar(discriminant(O))))//(Ar(2)^(r1+r2) * const_pi(Ar)^r2))

  # I should assert that radius(loghRtrue) < log(2)

  @assert isfinite(loghRtrue)

  while true
    loghRapprox = log(c.h* abs(U.tentative_regulator))

    @assert isfinite(loghRapprox)

    if contains(loghRtrue, loghRapprox)
      return fmpz(1)
    elseif !overlaps(loghRtrue, loghRapprox)
      e = exp(loghRapprox - loghRtrue)
      t = arf_struct(0, 0, 0, 0)
      ccall((:arf_init, :libarb), Void, (Ptr{arf_struct}, ), &t)

      s = fmpz()
      ccall((:arb_get_abs_ubound_arf, :libarb), Void, (Ptr{arf_struct}, Ptr{arb}, Clong), &t, &e, pre)
      ccall((:arf_get_fmpz, :libarb), Void, (Ptr{fmpz}, Ptr{arf_struct}, Cint), &s, &t, 1) # 1 is round up
      ccall((:arf_clear, :libarb), Void, (Ptr{arf_struct}, ), &t)
      return s
    end

    error("Not yet implemented")
  end
end

function _class_unit_group(O::NfMaxOrd; bound::Int = -1, method::Int = 3, large::Int = 1000, redo::Bool = false, unit_method::Int = 1)

  @vprint :UnitGroup 1 "Computing tentative class and unit group ... \n"

  @v_do :UnitGroup 1 pushindent()
  c = class_group_ctx(O, bound = bound, method = method, large = large, redo = redo)
  @v_do :UnitGroup 1 popindent()

  if c.finished
    U = _get_UnitGrpCtx_of_order(O)
    @assert U.finished
    return c, U, 1
  end

  @vprint :UnitGroup 1 "Tentative class number is now $(c.h)\n"

  U = UnitGrpCtx{FacElem{nf_elem, AnticNumberField}}(O)

  need_more = true

  hnftime = 0.0

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
      if _validate_class_unit_group(c, U) == 1
        break
      end
    end
    #TODO: use LLL?
    if need_more
      d = root(abs(discriminant(O)), 2)
      c.expect = class_group_expected(d, degree(O), Int(norm(c.FB.ideals[1])), 100)
      need_more = false
    end
    class_group_new_relations_via_lll(c, extra = unit_rank(O) - length(U.units) +1)
    h_old = c.h
    class_group_get_pivot_info(c)
    if h_old == c.h
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

doc"""
***
    class_group(O::NfMaxOrd; bound = -1, method = 3) -> Map

> Returns an isomorphism map $f$ from $A$ to the set of ideals of $O$.
> `A = domain(f)
"""
function class_group(O::NfMaxOrd; bound::Int = -1, method::Int = 3, redo::Bool = false, unit_method::Int = 1)
  c, U, b = _class_unit_group(O, bound = bound, method = method, redo = redo, unit_method = unit_method)
  @assert b==1
  return class_group(c)
end


doc"""
***
    unit_group(O::NfMaxOrd) -> Map

> Returns an isomorphism map $f \colon A \to \mathcal O^\times$. Let
> `A = domain(f)`. Then a set of fundamental units of $\mathcal O$ can be
> obtained via `[ f(A[i]) for i in 1:unit_rank(O) ]`.
"""
function unit_group(O::NfMaxOrd; method::Int = 3, unit_method::Int = 1)
  c, U, b = _class_unit_group(O, method = method, unit_method = unit_method)
  @assert b==1
  return unit_group(c, U)
end

doc"""
***
    unit_group_fac_elem(O::NfMaxOrd) -> Map

> Returns an isomorphism map $f \colon A \to \mathcal O^\times$. Let
> `A = domain(f)`. Then a set of fundamental units of $\mathcal O$ can be
> obtained via `[ f(A[i]) for i in 1:unit_rank(O) ]`.
"""
function unit_group_fac_elem(O::NfMaxOrd; method::Int = 3, unit_method::Int = 1)
  c, U, b = _class_unit_group(O, method = method, unit_method = unit_method)
  @assert b==1
  return unit_group_fac_elem(c, U)
end

