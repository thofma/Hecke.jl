################################################################################
#
#     Hecke.jl : Hecke main file
#
# This file is part of Hecke.
#
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
# (C) 2020-2021 Claus Fieker, Tommy Hofmann, Carlo Sircana
#
################################################################################

@doc Markdown.doc"""
Hecke is a Julia package for algorithmic algebraic number theory.
For more information please visit

    https://github.com/thofma/Hecke.jl

"""
module Hecke

################################################################################
#
#  Import/export
#
################################################################################

import Base: show, minimum, rand, prod, copy, rand, ceil, round, size, in,
             powermod, ^, getindex, ==, <, >, +, *, /, \, -, !=, getindex,
             setindex!, transpose, getindex, //, floor, max, BigFloat,
             precision, first, StepRange, show, inv, div, divrem, one, zero, iseven, isodd,
             convert, angle, abs2, isless, exponent, isfinite, zeros, rem, min,
             numerator, denominator, exp, maximum, intersect, reduce, sqrt, haskey, merge,
	     powermod

# To make all exported Nemo functions visible to someone using "using Hecke"
# we have to export everything again
# dong it the "import" route, we can pick & choose...

using Requires

using LinearAlgebra, Markdown, InteractiveUtils, Libdl, Distributed, Printf, SparseArrays, Serialization, Random, Pkg, Test

import AbstractAlgebra
import AbstractAlgebra: get_cached!

import LinearAlgebra: dot, istriu, nullspace, rank, ishermitian

import SparseArrays: nnz

import Serialization: serialize, deserialize

import Random: rand!
using Random: Sampler, SamplerTrivial, GLOBAL_RNG

using RandomExtensions: RandomExtensions, make, Make2, Make3, Make4

import Nemo

# TODO: remove/simplify the following once Nemo has IntegerUnion
# (and the version adding IntegerUnion is required in Project.toml)
if isdefined(Nemo, :IntegerUnion)
  import Nemo.IntegerUnion
else
  const IntegerUnion = Union{Integer, Nemo.fmpz}
end

import Pkg

exclude = [:Nemo, :AbstractAlgebra, :RealField, :zz, :qq, :factor, :call,
           :factors, :parseint, :strongequal, :window, :xgcd, :rows, :cols,
           :can_solve, :set_entry!]

for i in names(Nemo)
  i in exclude && continue
  eval(Meta.parse("import Nemo." * string(i)))
  eval(Expr(:export, i))
end

import Nemo: acb_struct, Ring, Group, Field, NmodRing, nmod, arf_struct,
             elem_to_mat_row!, elem_from_mat_row, gfp_elem, gfp_mat,
             gfp_fmpz_elem, Zmodn_poly, Zmodn_mat, GaloisField,
             GaloisFmpzField, acb_vec, array, acb_vec_clear, force_coerce,
             force_op, fmpz_mod_ctx_struct, divisors

export show, StepRange, domain, codomain, image, preimage, modord, resultant,
       next_prime, ispower, number_field, factor


###############################################################################
#
#   Library initialisation
#
###############################################################################

const pkgdir = joinpath(dirname(pathof(Hecke)), "..")

global const number_field = NumberField

function MaximalOrder
end

global const maximal_order = MaximalOrder

function __init__()
  # Because of serialization/deserialization problems, the base rings would differ otherwise.
  Hecke.Globals.Zx.base_ring = FlintZZ
  Hecke.Globals.Qx.base_ring = FlintQQ

  # Check if were are non-interactive
  bt = Base.process_backtrace(Base.backtrace())
  isinteractive_manual = all(sf -> sf[1].func != :_tryrequire_from_serialized, bt)

  # Respect the -q flag
  isquiet = Bool(Base.JLOptions().quiet)

  show_banner = !isquiet && isinteractive_manual && isinteractive() &&
                !any(x->x.name in ["Oscar"], keys(Base.package_locks)) &&
                get(ENV, "HECKE_PRINT_BANNER", "true") != "false"

  if show_banner
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
    println("(c) 2015-2021 by Claus Fieker, Tommy Hofmann and Carlo Sircana")
    println()
  end

  #if inNotebook()  # to make toggle work in IJulia
  #  display("text/html", "\$\\require{action}\$")
  #end

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

  t = create_accessors(AnticNumberField, Array, get_handle())

  global _get_cyclotomic_ext_nf = t[1]
  global _set_cyclotomic_ext_nf = t[2]

  t = create_accessors(AnticNumberField, Array, get_handle())

  global _get_automorphisms_nf = t[1]
  global _set_automorphisms_nf = t[2]

  t = create_accessors(AnticNumberField, NfAbsOrd{AnticNumberField, nf_elem}, get_handle())
  global _get_equation_order_of_nf = t[1]
  global _set_equation_order_of_nf = t[2]

  t = create_accessors(SimpleNumField, NfRelOrd, get_handle())

  global _get_maximal_order_of_nf_rel = t[1]
  global _set_maximal_order_of_nf_rel = t[2]

  t = create_accessors(AnticNumberField, FacElemMon{AnticNumberField}, get_handle())

  global _get_fac_elem_mon_of_nf = t[1]
  global _set_fac_elem_mon_of_nf = t[2]

  t = create_accessors(NfRel, Array, get_handle())

  global _get_automorphisms_nf_rel = t[1]
  global _set_automorphisms_nf_rel = t[2]

  t = Hecke.create_accessors(AnticNumberField, Dict{Int, Tuple{qAdicRootCtx, Dict{nf_elem, Any}}}, get_handle())
  global _get_nf_conjugate_data_qAdic = t[1]
  global _set_nf_conjugate_data_qAdic = t[2]

  t = Hecke.create_accessors(AnticNumberField, Any, get_handle())
  global _get_nf_prime_data_lifting = t[1]
  global _set_nf_prime_data_lifting = t[2]

  t = Hecke.create_accessors(AnticNumberField, Any, get_handle())
  global _get_nf_norm_relation = t[1]
  global _set_nf_norm_relation = t[2]

  global R = _RealRing()

  global flint_rand_ctx = flint_rand_state()

  @require GAP="c863536a-3901-11e9-33e7-d5cd0df7b904" begin
    include("FieldFactory/fields.jl")
    include("FieldFactory/FrobeniusExtensions.jl")
    include("ModAlgAss/GAPMeatAxe.jl")
    #@require Revise="295af30f-e4ad-537b-8983-00126c2a3abe" begin
    #  import .Revise
    #  #Revise.track(Hecke, joinpath(pkgdir, "src/FieldFactory/fields.jl"))
    #  #Revise.track(Hecke, "FieldFactory/abelian_layer.jl")
    #  #Revise.track(Hecke, "FieldFactory/brauer.jl")
    #  #Revise.track(Hecke, "FieldFactory/merge.jl")
    #  #Revise.track(Hecke, "FieldFactory/read_write.jl")
    #end
  end

  @require Polymake="d720cf60-89b5-51f5-aff5-213f193123e7" begin
    include("AlgAssRelOrd/NEQ_polymake.jl")
  end

  resize!(_RealRings, Threads.nthreads())
  for i in 1:Threads.nthreads()
     _RealRings[i] = _RealRing()
  end

end

module Globals
  using Hecke
  const Qx, _ = PolynomialRing(FlintQQ, "x", cached = false)
  const Zx, _ = PolynomialRing(FlintZZ, "x", cached = false)
end

using .Globals

################################################################################
#
#  Verbose printing and custom assertions
#
################################################################################

include("Assertions.jl")

################################################################################
#
#  Deprecations
#
################################################################################

include("Deprecations.jl")

################################################################################
#
#  Setter and getter for objects
#
################################################################################

function _get_maximal_order(K::AnticNumberField)
  return _get_maximal_order_of_nf(K)
end

function _set_maximal_order(K::AnticNumberField, O)
  _set_maximal_order_of_nf(K, O)
end

function conjugate_data_arb(K::AnticNumberField)
  return get_attribute!(K, :conjugate_data_arb) do
    return acb_root_ctx(K.pol)
  end::acb_root_ctx
end

function conjugate_data_arb_roots(K::AnticNumberField, p::Int)
  already_set = false
  _c = get_attribute(K, :conjugate_data_arb_roots)
  if _c !== nothing
    c = _c::Dict{Int, acb_roots}
    already_set = true
  else
    c = Dict{Int, acb_roots}()
    set_attribute!(K, :conjugate_data_arb_roots => c)
  end

  if already_set && haskey(c, p)
    return c[p]
  end

  #if p > 2^18
  #  Base.show_backtr(STDOUT, backtr())
  #end
  if Nemo.iscyclo_type(K)
    # There is one real place
    f = get_attribute(K, :cyclo)::Int
    if f == 1
      # x - 1
      rall = [one(AcbField(p, cached = false))]
      rreal = [one(ArbField(p, cached = false))]
      rcomplex = Vector{acb}()
    elseif f == 2
      # x + 1
      rall = [-one(AcbField(p, cached = false))]
      rreal = [-one(ArbField(p, cached = false))]
      rcomplex = Vector{acb}()
    else
      # Use that e^(i phi) = cos(phi) + i sin(phi)
      # Call sincospi to determine these values
      pstart = max(p, 2) # Sometimes this gets called with -1
      local _rall::Vector{Tuple{arb, arb}}
      rreal = arb[]
      rcomplex = Vector{acb}(undef, div(degree(K), 2))
      while true
        R = ArbField(pstart, cached = false)
        # We need to pair them
        _rall = Tuple{arb, arb}[ sincospi(fmpq(2*k, f), R) for k in 1:f if gcd(f, k) == 1]
        if all(x -> radiuslttwopower(x[1], -p) && radiuslttwopower(x[2], -p), _rall)
          CC = AcbField(pstart, cached = false)
          rall = acb[ CC(l[2], l[1]) for l in _rall]
          j = 1
          good = true
          for i in 1:degree(K)
            if ispositive(_rall[i][1])
              rcomplex[j] = rall[i]
              j += 1
            else
              if !isnegative(_rall[i][1])
                # The precision was not large enough to determine the sign of the imaginary part
                good = false
              end
            end
          end
          good && break
        end
        pstart = Int(ceil(1.3 * pstart))
      end
    end
  else
    # Generic case
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
  end

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
#  if !already_set
#    _set_nf_conjugate_data_arb_roots(K, c)
#  end
  return c[p]::acb_roots
end

function signature(K::AnticNumberField)
  return get_attribute!(K, :signature) do
    return signature(defining_polynomial(K))
  end::Tuple{Int, Int}
end

function _get_prime_data_lifting(K::AnticNumberField)
  try
    c = _get_nf_prime_data_lifting(K)
    return c
  catch
    c = Dict()
    _set_nf_prime_data_lifting(K, c)
    return c
  end
end

################################################################################
#
#  Intermediate backwards compatibility
#
################################################################################

trace(x...) = tr(x...)

################################################################################
#
#  Version number
#
################################################################################

deps = Pkg.dependencies()
if haskey(deps, Base.UUID("3e1990a7-5d81-5526-99ce-9ba3ff248f21"))
  ver = Pkg.dependencies()[Base.UUID("3e1990a7-5d81-5526-99ce-9ba3ff248f21")]
  if occursin("/dev/", ver.source)
    global VERSION_NUMBER = VersionNumber("$(ver.version)-dev")
  else
    global VERSION_NUMBER = VersionNumber("$(ver.version)")
  end
else
  global VERSION_NUMBER = "building"
end

# version number determined at compile time
function _get_version()
    return VersionNumber(Pkg.TOML.parsefile(joinpath(dirname(@__DIR__), "Project.toml"))["version"])
end
const pkg_version = _get_version()

######################################################################
# named printing support
######################################################################

# to use:
# in HeckeMap
#   in the show function, start with @show_name(io, map)
# for other objetcs
#   add @attributes to the struct
#   add @show_name(io, obj) to show
#   optionally, add @show_special(io, obj) as well
# on creation, or whenever, call set_name!(obj, string)
# @show_name will set on printing if bound in the REPL
# moved into AbstractAlgebra

#maps are different - as are number fields

################################################################################
#
#  Abstract map type
#
################################################################################

abstract type HeckeMap <: SetMap end  #needed here for the hasspecial stuff
             #maybe move to Maps?

import AbstractAlgebra: get_attribute, set_attribute!, @show_name, @show_special,
       _get_attributes, _get_attributes!, _is_attribute_storing_type,
       @show_special_elem, @attributes, extra_name, set_name!, find_name

# Hecke maps store attributes in the header object
_get_attributes(G::Map{<:Any, <:Any, HeckeMap, <:Any}) = _get_attributes(G.header)
_get_attributes!(G::Map{<:Any, <:Any, HeckeMap, <:Any}) = _get_attributes!(G.header)
_is_attribute_storing_type(::Type{Map{<:Any, <:Any, HeckeMap, <:Any}}) = true

import Nemo: libflint, libantic, libarb  #to be able to reference libraries by full path
                                         #to avoid calling the "wrong" copy

################################################################################
#
#  Custom test function
#
################################################################################

function _adjust_path(x::String)
  if Sys.iswindows()
    return replace(x, "/" => "\\")
  else
    return x
  end
end

function test_module(x, new::Bool = true; long::Bool = false, with_gap::Bool = false, with_polymake::Bool = false)
   julia_exe = Base.julia_cmd()
   # On Windows, we also allow bla/blub"
   x = _adjust_path(x)
   if x == "all"
     test_file = joinpath(pkgdir, "test", "runtests.jl")
   else
     test_file = joinpath(pkgdir, "test", "$x.jl")
   end

   setup_file = joinpath(pkgdir, "test", "setup.jl")

   if new
     cmd = "using Test; using Hecke; $(with_gap ? "using GAP;" : "") $(with_polymake ? "import Polymake;" : "") Hecke.assertions(true); long_test = $long; _with_gap = $with_gap; _with_polymake = $with_polymake; include(\"$(setup_file)\"); include(\"$test_file\");"
     @info("spawning ", `$julia_exe -e \"$cmd\"`)
     proj = Base.active_project()
     run(`$(julia_exe) --project=$(proj) -e $(cmd)`)
   else
     long_test = long
     _with_gap = with_gap
     _with_polymake = with_polymake
     assertions(true)
     @info("Running tests for $x in same session")
     include(test_file)
     assertions(false)
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

mutable struct NotImplemented <: Exception end

Base.showerror(io::IO, ::NotImplemented) =
    print(io, """Not implemented (yet).""")

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
include("NumField/NfRel/Types.jl")
include("AlgAss/Types.jl")
include("AlgAssAbsOrd/Types.jl")
include("AlgAssRelOrd/Types.jl")
include("Grp.jl")
include("Map.jl")
include("GrpAb.jl")
include("Misc.jl")
include("LinearAlgebra.jl")
include("NumField.jl")
include("NumFieldOrd.jl")
include("FunField.jl")
include("Sparse.jl")
include("BigComplex.jl")
include("conjugates.jl")
include("analytic.jl")
include("helper.jl")
include("EllCrv.jl")
include("LargeField.jl")
include("RCF.jl")
include("ModAlgAss.jl")
include("AlgAss.jl")
include("AlgAssAbsOrd.jl")
include("AlgAssRelOrd.jl")
include("LocalField.jl")
include("QuadForm.jl")
include("FieldFactory.jl")
include("../examples/NFDB.jl")

const _RealRings = _RealRing[_RealRing()]

################################################################################
#
#  Download other stuff
#
################################################################################

include("Get.jl")

################################################################################
#
#  Precompilation
#
################################################################################

#precompile(maximal_order, (AnticNumberField, ))

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

Base.issubset(K::NumField, L::NumField) = issubfield(K, L)[1]
Base.issubset(C::ClassField, B::ClassField) = issubfield(C, B)

################################################################################
#
#  Trace function calls
#
################################################################################

_trace_cache = Dict()

function _trace_call(;cache = _trace_cache, depth = 5, print = false)
  s = Base.stacktrace()[3:3 + depth - 1]
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

function example(s::String)
  Base.include(Main, joinpath(dirname(pathof(Hecke)), "..", "examples", s))
end

function revise(s::String)
  s = joinpath(dirname(pathof(Hecke)), "..", "examples", s)
  Main.Revise.track(Main, s)
end

function system(s::String)
  Base.include(Main, joinpath(dirname(pathof(Hecke)), "..", "system", s))
end

function build()
  system("Build.jl")
end

function doc_init(;path=mktempdir())
  global docsproject = path
  if !isfile(joinpath(docsproject,"Project.toml"))
    cp(joinpath(pkgdir, "docs", "Project.toml"), joinpath(docsproject,"Project.toml"))
  end
  Pkg.activate(docsproject) do
    # we dev all packages with the paths from where they are currently loaded
    Pkg.develop(path=pkgdir)
    Pkg.instantiate()
    Base.include(Main, joinpath(pkgdir, "docs", "Build.jl"))
  end
end

#function doc_update_deps()
#  Pkg.activate(Pkg.update, joinpath(oscardir, "docs"))
#end

function open_doc()
    filename = normpath(pkgdir, "docs", "build", "index.html")
    @static if Sys.isapple()
        run(`open $(filename)`; wait = false)
    elseif Sys.islinux() || Sys.isbsd()
        run(`xdg-open $(filename)`; wait = false)
    elseif Sys.iswindows()
        cmd = get(ENV, "COMSPEC", "cmd.exe")
        run(`$(cmd) /c start $(filename)`; wait = false)
    else
        @warn("Opening files the default application is not supported on this OS.",
              KERNEL = Sys.KERNEL)
    end
end

function build_doc(; doctest=false, strict=false, format=:mkdocs)
  if !isdefined(Main, :Build)
    doc_init()
  end
  Pkg.activate(docsproject) do
    Base.invokelatest(Main.Build.make, Hecke; strict=strict, local_build=true, doctest=doctest, format=format)
  end
  if format == :html
    open_doc()
  elseif format == :mkdocs
    println("""Run `mkdocs serve` inside `../Hecke/docs/` to view the documentation.

            Use `format = :html` for a simplified version of the docs which does
            not require `mkdocs`.
            """)
  end
end

#html_build = Ref(false)
#
#function build_doc(html::Bool = false)
#  _html_build = html_build[]
#  html_build[] = html
#  Base.include(Main, joinpath(dirname(pathof(Hecke)), "..", "docs", "make_local.jl"))
#  html_build[] = _html_build
#end

function percent_P()
  s = Base.active_repl.mistate
  REPL = Base.REPL_MODULE_REF.x

  #from Rafael:
  function print_history(hist)
    println()
    for i = hist.start_idx+1:lastindex(hist.history)
      if hist.modes[i] == :julia
        println('[', i-hist.start_idx, "] ", hist.history[i])
      end
    end
  end
  print_history(REPL.LineEdit.mode(s).hist)
end

export percent_P

#same (copied) as in stdlib/v1.0/InteractiveUtils/src/InteractiveUtils.jl
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


function print_cache(sym::Vector{Any})
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
           :(Hecke.VERBOSE_PRINT_INDENT),
           :(Hecke._RealRings),
           :(Hecke.protect)] # We need to protect protect itself :)
                             # Otherwise it might emptied and then everything
                             # is emptied.

function clear_cache(sym::Vector{Any})
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

using .NormRel

end # module
