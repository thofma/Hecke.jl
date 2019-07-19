################################################################################
#
#     Hecke.jl : Hecke main file
#
# This file is part of Hecke.
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
# (C) 2015-2019 Claus Fieker, Tommy Hofmann
#
################################################################################

module Hecke

################################################################################
#
#  Import/export
#
################################################################################

import Base: show, minimum, rand, prod, copy, rand, ceil, round, size, in,
             powermod, ^, getindex, ==, <, >, +, *, /, \, -, !=, getindex,
             setindex!, transpose, getindex, //, div, floor, max, BigFloat,
             precision, first, StepRange, show, one, zero, inv, iseven, isodd,
             convert, angle, abs2, isless, exponent, isfinite, zeros, rem, min,
             numerator, denominator, exp, maximum, intersect

# To make all exported Nemo functions visible to someone using "using Hecke"
# we have to export everything again
# dong it the "import" route, we can pick & choose...

using LinearAlgebra, Markdown, InteractiveUtils, Libdl, Distributed, Printf, SparseArrays, Serialization, Random, Pkg, Test

import AbstractAlgebra

import LinearAlgebra: dot, istriu, nullspace

import SparseArrays: nnz

import Serialization: serialize, deserialize

import Random: rand!

import Nemo

exclude = [:Nemo, :AbstractAlgebra, :RealField, :zz, :qq, :factor, :call,
           :factors, :parseint, :strongequal, :window, :xgcd, :rows, :cols,
           :can_solve]

for i in names(Nemo)
  i in exclude && continue
  eval(Meta.parse("import Nemo." * string(i)))
  eval(Expr(:export, i))
end

import Nemo: acb_struct, Ring, Group, Field, NmodRing, nmod, arf_struct,
             elem_to_mat_row!, elem_from_mat_row, gfp_elem, gfp_mat,
             Zmodn_poly, Zmodn_mat, GaloisField, acb_vec, array, acb_vec_clear

export @vprint, @hassert, @vtime, add_verbose_scope, get_verbose_level,
       set_verbose_level, add_assert_scope, get_assert_level, set_assert_level,
       update, show, StepRange, domain, codomain, image, preimage,
       modord, resultant, next_prime, ispower, number_field, factor

###############################################################################
#
#   Library initialisation
#
###############################################################################

const pkgdir = joinpath(dirname(pathof(Hecke)), "..")
#
#const libhecke = joinpath(pkgdir, "local", "lib", "libhecke")
#
#const libdir = joinpath(pkgdir, "local", "lib")

global const number_field = NumberField
function MaximalOrder
end
global const maximal_order = MaximalOrder

function __init__()

  if myid() == 1
    println("")
    print("Welcome to \n")
    printstyled("
    _    _           _        
   | |  | |         | |       
   | |__| | ___  ___| | _____ 
   |  __  |/ _ \\/ __| |/ / _ \\
   | |  | |  __/ (__|   <  __/
   |_|  |_|\\___|\\___|_|\\_\\___|
    ", color = :red)

    println()
    print("Version")
    printstyled(" $VERSION_NUMBER ", color = :green)
    print("... \n ... which comes with absolutely no warranty whatsoever")
    println()
    println("(c) 2015-2019 by Claus Fieker, Tommy Hofmann and Carlo Sircana")
    println()
  else
    println("Hecke $VERSION_NUMBER ...")
  end

  if inNotebook()  # to make toggle work in IJulia
    display("text/html", "\$\\require{action}\$")
  end
  
  #if "HOSTNAME" in keys(ENV) && ENV["HOSTNAME"] == "juliabox"
  #  push!(Libdl.DL_LOAD_PATH, "/usr/local/lib")
  #elseif Sys.islinux()
  #  push!(Libdl.DL_LOAD_PATH, libdir)
  #  Libdl.dlopen(libhecke)
  #else
  #  push!(Libdl.DL_LOAD_PATH, libdir)
  #end
  
  t = create_accessors(AnticNumberField, acb_root_ctx, get_handle())
  global _get_nf_conjugate_data_arb = t[1]
  global _set_nf_conjugate_data_arb = t[2]

  t = create_accessors(AnticNumberField, Dict{Int, acb_roots}, get_handle())
  global _get_nf_conjugate_data_arb_roots = t[1]
  global _set_nf_conjugate_data_arb_roots = t[2]


  t = create_accessors(AnticNumberField,
                       Tuple{Int, nf_elem},
                       get_handle())
  global _get_nf_torsion_units = t[1]
  global _set_nf_torsion_units = t[2]

  t = create_accessors(AnticNumberField, NfOrd, get_handle())

  global _get_maximal_order_of_nf = t[1]
  global _set_maximal_order_of_nf = t[2]

  t = create_accessors(NfOrd, ClassGrpCtx, get_handle())

  global _get_ClassGrpCtx_of_order = t[1]
  global _set_ClassGrpCtx_of_order = t[2]

  t = create_accessors(NfOrd, UnitGrpCtx, get_handle())

  global _get_UnitGrpCtx_of_order = t[1]
  global _set_UnitGrpCtx_of_order = t[2]
  
  t = create_accessors(NfOrd, Array, get_handle())
  
  global _get_carlos_units_of_order = t[1]
  global _set_carlos_units_of_order = t[2]

  t = create_accessors(AnticNumberField, roots_ctx, get_handle())

  global _get_roots_ctx_of_nf = t[1]
  global _set_roots_ctx_of_nf = t[2]

  t = create_accessors(AnticNumberField, Array, get_handle())

  global _get_cyclotomic_ext_nf = t[1]
  global _set_cyclotomic_ext_nf = t[2]

  t = create_accessors(AnticNumberField, Array, get_handle())

  global _get_automorphisms_nf = t[1]
  global _set_automorphisms_nf = t[2]

  t = create_accessors(AnticNumberField, NfAbsOrd{AnticNumberField, nf_elem}, get_handle())
  global _get_equation_order_of_nf = t[1]
  global _set_equation_order_of_nf = t[2]

  t = create_accessors(RelativeExtension, NfRelOrd, get_handle())

  global _get_maximal_order_of_nf_rel = t[1]
  global _set_maximal_order_of_nf_rel = t[2]

  t = create_accessors(NfOrd, MapClassGrp, get_handle())

  global _get_picard_group = t[1]
  global _set_picard_group = t[2]

  t = create_accessors(NfOrd, MapUnitGrp, get_handle())

  global _get_unit_group_non_maximal = t[1]
  global _set_unit_group_non_maximal = t[2]

  t = create_accessors(AnticNumberField, FacElemMon{AnticNumberField}, get_handle())

  global _get_fac_elem_mon_of_nf = t[1]
  global _set_fac_elem_mon_of_nf = t[2]

  t = create_accessors(NfRel, Array, get_handle())

  global _get_automorphisms_nf_rel = t[1]
  global _set_automorphisms_nf_rel = t[2]


  global R = _RealRing()

  # Stuff for elliptic curves
  # polynomial rings Zx = ZZ[x] and _Zxy = ZZ[x,y]
  # will be removed eventually
  #global _Zx = PolynomialRing(FlintZZ, "_x")[1]
  #global _Zxy = PolynomialRing(_Zx, "_y")[1]
  #global _x = gen(_Zx)
  #global _y = gen(_Zxy)

  global flint_rand_ctx = flint_rand_state()
end

function _get_maximal_order(K::AnticNumberField)
  return _get_maximal_order_of_nf(K)
end

function _set_maximal_order(K::AnticNumberField, O)
  _set_maximal_order_of_nf(K, O)
end

function _get_nf_equation_order(K::AnticNumberField)
  return _get_equation_order_of_nf(K)::NfAbsOrd{AnticNumberField, nf_elem}
end

function _set_nf_equation_order(K::AnticNumberField, O)
  _set_equation_order_of_nf(K, O)
  return nothing
end

function conjugate_data_arb(K::AnticNumberField)
  try
    c = _get_nf_conjugate_data_arb(K)::acb_root_ctx
    return c
  catch
    c = acb_root_ctx(K.pol)
    _set_nf_conjugate_data_arb(K, c)
    return c::acb_root_ctx
  end
end

function conjugate_data_arb_roots(K::AnticNumberField, p::Int)
  already_set = false
  local c
  try
    c = _get_nf_conjugate_data_arb_roots(K)::Dict{Int, acb_roots}
    already_set = true
  catch
    c = Dict{Int, acb_roots}()
  end

  if already_set && haskey(c, p)
    return c[p]
  end

  #if p > 2^18
  #  Base.show_backtr(STDOUT, backtr())
  #end
  rootc = conjugate_data_arb(K)
  q = rootc.prec
  while q < p
    refine(rootc)
    q = rootc.prec
  end
  @assert p <= q
  rall = deepcopy(rootc.roots)
  rreal = deepcopy(rootc.real_roots)
  rcomplex = deepcopy(rootc.complex_roots)
  for z in rall
    expand!(z, -p)
  end
  for z in rreal
    expand!(z, -p)
  end
  for z in rcomplex
    expand!(z, -p)
  end
  c[p] = acb_roots(p, rall, rreal, rcomplex)
  if !already_set
    _set_nf_conjugate_data_arb_roots(K, c)
  end
  return c[p]::acb_roots
end

function _torsion_units(K::AnticNumberField)
  try
    c = _get_nf_torsion_units(K)::Tuple{Int, nf_elem}
    return c
  catch
    ord, gen = _torsion_units_gen(K)
    _set_nf_torsion_units(K, (ord, gen))
    return ord, gen
  end
end

function torsion_units(K::AnticNumberField)
  ord, g = _torsion_units(K)
  return nf_elem[g^i for i = 0:ord-1]
end

function torsion_units_gen(K::AnticNumberField)
  ar, g = _torsion_units(K)
  return g
end

################################################################################
#
#  Intermediate backwards compatibility
#
################################################################################

trace(x...) = tr(x...)

#lufact(x...) = lu(x...)
#
#lufact!(x...) = lu!(x...)

Base.adjoint(x) = transpose(x)

################################################################################
#
#  Version number
#
################################################################################

global VERSION_NUMBER = v"0.6.4"

################################################################################
#
#  Verbose printing
#
################################################################################

global hecke = Hecke

global VERBOSE_SCOPE = Symbol[]

global VERBOSE_LOOKUP = Dict{Symbol, Int}()

global VERBOSE_PRINT_INDENT = [ 0 ]

function add_verbose_scope(s::Symbol)
  !(s in VERBOSE_SCOPE) && push!(VERBOSE_SCOPE, s)
  nothing
end

function pushindent()
  a = VERBOSE_PRINT_INDENT[1]
  VERBOSE_PRINT_INDENT[1] = a + 1
  nothing
end

function clearindent()
  VERBOSE_PRINT_INDENT[1] = 0
  nothing
end

function popindent()
  a = VERBOSE_PRINT_INDENT[1]
  VERBOSE_PRINT_INDENT[1] = a - 1
  nothing
end

function _global_indent()
  s = "  "^VERBOSE_PRINT_INDENT[1]
  return s
end

macro vprint(args...)
  if length(args) == 2
    quote
      if get_verbose_level($(args[1])) >= 1
        print(_global_indent())
        print($(esc((args[2]))))
      end
    end
  elseif length(args) == 3
    quote
      if get_verbose_level($(args[1])) >= $(args[2])
        print(_global_indent())
        print($(esc((args[3]))))
      end
    end
  end
end

macro v_do(args...)
  if length(args) == 2
    quote
      if get_verbose_level($(esc(args[1]))) >= 1
       $(esc(args[2]))
      end
    end
  elseif length(args) == 3
    quote
      if get_verbose_level($(esc(args[1]))) >= $(esc(args[2]))
        $(esc(args[3]))
      end
    end
  end
end

function set_verbose_level(s::Symbol, l::Int)
  !(s in VERBOSE_SCOPE) && error("Not a valid symbol")
  VERBOSE_LOOKUP[s] = l
end

function get_verbose_level(s::Symbol)
  !(s in VERBOSE_SCOPE) && error("Not a valid symbol")
  return get(VERBOSE_LOOKUP, s, 0)::Int
end

################################################################################
#
#  Assertions
#
################################################################################

global ASSERT_SCOPE = Symbol[]

global ASSERT_LOOKUP = Dict{Symbol, Int}()

function add_assert_scope(s::Symbol)
  !(s in ASSERT_SCOPE) && push!(ASSERT_SCOPE, s)
  nothing
end

function set_assert_level(s::Symbol, l::Int)
  !(s in ASSERT_SCOPE) && error("Not a valid symbol")
  ASSERT_LOOKUP[s] = l
end

function get_assert_level(s::Symbol)
  !(s in ASSERT_SCOPE) && error("Not a valid symbol")
  return get(ASSERT_LOOKUP, s, 0)::Int
end

macro hassert(args...)
  if length(args) == 2
    quote
      if get_assert_level($(args[1])) >= 1
        @assert $(esc(args[2]))
      end
    end
  elseif length(args) == 3
    quote
      if get_assert_level($(args[1])) >= $(args[2])
        @assert $(esc(args[3]))
      end
    end
  end
end

######################################################################
# named printing support
######################################################################
# to use:
# in HeckeMap
#   in the show function, start with @show_name(io, map)
# for other objetcs
#   add @declare_other to the struct
#   add @show_name(io, obj) to show
#   optionally, add @show_special(io, obj) as well
# on creation, or whenever, call set_name!(obj, string)
# @show_name will set on printing if bound in the REPL

macro declare_other()
  esc(quote other::Dict{Symbol, Any} end )
end


function set_name!(G, name::String)
  set_special(G, :name => name)
end

function hasspecial(G)
  if isa(G, Map{<:Any, <:Any, HeckeMap, <:Any})
    if isdefined(G.header, :other)
      return true, G.header.other
    else
      return false, nothing
    end
  end
  if !isdefined(G, :other)
    return false, nothing
  else
    return true, G.other
  end
end

import Nemo: get_special, set_special

function get_special(G, s::Symbol)
  fl, D = hasspecial(G)
  fl && return get(D, s, nothing)
  nothing
end

function set_name!(G)
  s = get_special(G, :name)
  s === nothing || return
  sy = find_name(G)
  sy === nothing && return
  set_name!(G, string(sy))
end

function set_special(G, data::Pair{Symbol, <:Any}...)
  if isa(G, Map{<:Any, <:Any, HeckeMap, <:Any})
    if !isdefined(G.header, :other)
      G.header.other = Dict{Symbol, Any}()
    end
    D = G.header.other
  elseif !isdefined(G, :other)
    D = G.other = Dict{Symbol, Any}()
  else
    D = G.other
  end

  for d in data
    push!(D, d)
  end
end

extra_name(G) = nothing

macro show_name(io, O)
  return :( begin
    local i = $(esc(io))
    local o = $(esc(O))
    s = get_special(o, :name)
    if s === nothing
      sy = find_name(o)
      if sy === nothing 
        sy = extra_name(o)
      end
      if sy !== nothing
        s = string(sy)
        set_name!(o, s)
      end
    end
    if get(i, :compact, false) &&
       s !== nothing
      print(i, s)
      return
    end
  end )
end

macro show_special(io, O)
  return :( begin
    local i = $(esc(io))
    local o = $(esc(O))
    s = get_special(o, :show)
    if s !== nothing
      s(i, o)
      return
    end
  end )
end

################################################################################
#
#  Custom test function
#
################################################################################

function test_module(x, new::Bool = true)
   julia_exe = Base.julia_cmd()
   if x == "all"
     test_file = joinpath(pkgdir, "test/runtests.jl")
   else
     test_file = joinpath(pkgdir, "test/$x.jl")
   end

   if new
     cmd = "using Test; using Hecke; include(\"$test_file\");"
     @info("spawning ", `$julia_exe -e \"$cmd\"`)
     run(`$julia_exe -e $cmd`)
   else
     @info("Running tests for $x in same session")
     try
       include(test_file)
     catch e
       if isa(e, LoadError)
         println("You need to do \"using Test\"")
       else
         rethrow(e)
       end
     end
   end
end

################################################################################
#
#  Verbose time printing
#
################################################################################

macro vtime(args...)
  if length(args) == 2
    msg = string(args[2])
    quote
      if get_verbose_level($(args[1])) >= 1
        local t0 = time_ns()
        local val = $(esc(args[2]))
        println((time_ns()-t0)/1e9, " @ ", $msg)
        val
      else
        local val2 = $(esc(args[2]))
        val2
      end
    end
  elseif length(args) == 3
    msg = string(args[3])
    quote
      if get_verbose_level($(args[1])) >= $(args[2])
        local t0 = time_ns()
        local val = $(esc(args[3]))
        println((time_ns()-t0)/1e9, " @ ", $msg)
        val
      else
        local val2 = $(esc(args[3]))
        val2
      end
    end
  end
end

#usage
# @vtime_add_ellapsed :ClassGroup 2 clg :saturate  s= hnf(a)
# @vtime_add :ClassGroup 2 clg :saturate  0.5
# -> clg.time[:saturate] += 
function _vtime_add(D::Dict, k::Any, v::Any)
  if haskey(D, k)
    D[k] += v
  else
    D[k] = v
  end
end

macro vtime_add(flag, level, var, key, value)
  quote
    if get_verbose_level($flag) >= $level
      _vtime_add($(esc(var)).time, $key, $(esc(value)))
    end
  end
end

macro vtime_add_elapsed(flag, level, var, key, stmt)
  quote
    tm = @elapsed $(esc(stmt))
    if get_verbose_level($flag) >= $level
      _vtime_add($(esc(var)).time, $key, tm)
    end
  end  
end

################################################################################
#
#  Exception types
#
################################################################################

mutable struct LowPrecisionCholesky <: Exception end

Base.showerror(io::IO, e::LowPrecisionCholesky) =
    print(io, """
    Negative diagonal in Cholesky decomposition, probably a precision issue""")

mutable struct LowPrecisionLLL <: Exception end

Base.showerror(io::IO, e::LowPrecisionLLL) =
    print(io, """
    Transformation matrix has too large entries relative to precision in LLL""")

# what is this function doing here?
function checkbounds(a::Int, b::Int) nothing; end;

################################################################################
add_assert_scope(:PID_Test)
set_assert_level(:PID_Test, 0)

################################################################################
#
#  "Submodules"
#
################################################################################

include("HeckeTypes.jl")
include("NfRel/Types.jl")
include("AlgAss/Types.jl")
include("Grp.jl")
include("Map.jl")
include("Misc.jl")
include("GrpAb.jl")
include("LinearAlgebra.jl")
include("NfAbs.jl")
include("NumField.jl")
include("NfOrd.jl")
include("Sparse.jl")
include("BigComplex.jl")
include("conjugates.jl")
include("NfRel.jl")
include("analytic.jl")
include("helper.jl")
include("EllCrv.jl")
include("LargeField.jl")
include("RCF.jl")
include("ModAlgAss.jl")
include("AlgAss.jl")
include("AlgAssAbsOrd.jl")
include("AlgAssRelOrd.jl")

################################################################################
#
#  Object overloading for map types
#
################################################################################

for T in subtypes(Map(HeckeMap))
  (M::T)(a) = image(M, a)
end

################################################################################
#
#  Verbose printing
#
################################################################################

@doc Markdown.doc"""
    vshow(A) -> Nothing

Prints all fields of $A$.
"""
function vshow(A)
  for i in fieldnames(typeof(A))
    if isdefined(A, i)
      print("$i: ")
      println(getfield(A, i), "\n")
    else
      println("$i: Not definied")
    end
  end
end

################################################################################
#
#  Element types for parent types
#
################################################################################

# Nemo only provides element_types for parent objects

elem_type(::Type{FacElemMon{T}}) where {T} = FacElem{elem_type(T), T}

elem_type(::Type{Generic.ResRing{T}}) where {T} = Generic.Res{T}

################################################################################
#
#  Aliases
#
################################################################################

hasroot(a...) = ispower(a...)  # catch all... needs revisiting:
                               #hasroot(poly) != ispower(poly)....

################################################################################
#
#  Trace function calls
#
################################################################################

_trace_cache = Dict()

function _trace_call(;cache = _trace_cache, depth = 2, print = false)
  s = Base.stacktrace()[4:4 + depth - 1]
  if !haskey(cache, s)
    if print
      println("\n Trace call ... \n ")
      Base.show_backtrace(stdout, s)
    end
    cache[s] = true
  end
end

function _print_traces(;cache = _trace_cache)
  println(cache)
end

################################################################################
#
# examples
#
################################################################################

export example

function example(s::String)
  Base.include(Main, joinpath(dirname(pathof(Hecke)), "..", "examples", s))
end

#same (copyed) as in stdlib/v1.0/InteractiveUtils/src/InteractiveUtils.jl
#difference: names(m, all = true) to also see non-exported variables, aka
# caches...

function varinfo(m::Module=Main, pattern::Regex=r"")
    rows =
        Any[ let value = getfield(m, v)
                 Any[string(v),
                     (value===Base || value===Main || value===Core ? "" : format_bytes(summarysize(value))),
                     summary(value)]
             end
             for v in sort!(names(m, all = true)) if isdefined(m, v) && occursin(pattern, string(v)) ]

    pushfirst!(rows, Any["name", "size", "summary"])

    return Markdown.MD(Any[Markdown.Table(rows, Symbol[:l, :r, :l])])
end
varinfo(pat::Regex) = varinfo(Main, pat)


function print_cache(sym::Array{Any, 1})
  for f in sym;
    #if f[2] isa Array || f[2] isa Dict || f[2] isa IdDict;
    try
      print(f[1], " ", length(f[2]), "\n");
    catch e
    end
  end
end

function print_cache()
  print_cache(find_cache(Nemo))
  print_cache(find_cache(Nemo.Generic))
  print_cache(find_cache(Hecke))
end

function find_cache(M::Module)
  sym = []
  for a in collect(names(M, all = true))
    d = Meta.parse("$M.$a")
      try 
        z = eval(d); 
        if isa(z, AbstractArray) || isa(z, AbstractDict)
          push!(sym, (d, z))
        end
    catch e
    end
  end
  return sym
end

protect = [:(Hecke.ASSERT_LOOKUP), :(Hecke.VERBOSE_LOOKUP), 
           :(Hecke.ASSERT_SCOPE), :(Hecke.VERBOSE_SCOPE),
           :(Hecke._euler_phi_inverse_maximum), 
           :(Hecke.odlyzko_bound_grh),
           :(Hecke.nC), :(Hecke.B1), #part of ECM
           :(Hecke.VERBOSE_PRINT_INDENT)]

function clear_cache(sym::Array{Any, 1})
  for f in sym;
    if f[1] in protect
      continue
    end
    try
      empty!(f[2])
    catch e
    end
  end
end

function clear_cache()
  clear_cache(find_cache(Nemo))
  clear_cache(find_cache(Nemo.Generic))
  clear_cache(find_cache(Hecke))
end

@inline __get_rounding_mode() = Base.MPFR.rounding_raw(BigFloat)

end # module

