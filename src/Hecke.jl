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
# (C) 2020-2024 Claus Fieker, Tommy Hofmann, Carlo Sircana
#
################################################################################


@doc raw"""
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

using LazyArtifacts

using LinearAlgebra
using Markdown
using InteractiveUtils
using Libdl
using Distributed
using Printf
using SparseArrays
using Serialization
using Random
using Pkg

import AbstractAlgebra
import AbstractAlgebra: get_cached!, @alias

import AbstractAlgebra: pretty, Lowercase, LowercaseOff, Indent, Dedent, terse, is_terse

import AbstractAlgebra: Solve

import LinearAlgebra: dot, nullspace, rank, ishermitian

import SparseArrays: nnz

import Serialization: serialize, deserialize

import Random: rand!
using Random: Sampler, SamplerTrivial, GLOBAL_RNG

using RandomExtensions: RandomExtensions, make, Make2, Make3, Make4

import Nemo

import Pkg

exclude = [:Nemo, :AbstractAlgebra, :RealNumberField, :zz, :qq, :factor, :call,
           :factors, :parseint, :strongequal, :window, :xgcd, :rows, :cols,
           :set_entry!,]

for i in names(Nemo)
  (i in exclude || !isdefined(Nemo, i)) && continue
  @eval import Nemo: $i
  @eval export $i
end

import Nemo: acb_struct, Ring, Group, Field, zzModRing, zzModRingElem, arf_struct,
             elem_to_mat_row!, elem_from_mat_row, fpFieldElem, fpMatrix,
             FpFieldElem, Zmodn_poly, Zmodn_mat, fpField,
             FpField, acb_vec, array, acb_vec_clear, force_coerce,
             force_op, fmpz_mod_ctx_struct, divisors, is_zero_entry, IntegerUnion, remove!,
             valuation!, is_cyclo_type, is_embedded, is_maxreal_type,
             mat_entry_ptr

AbstractAlgebra.@include_deprecated_bindings()
Nemo.@include_deprecated_bindings()

include("exports.jl")

const RationalUnion = Union{IntegerUnion, Rational{<: Integer}, QQFieldElem}

###############################################################################
#
#   Library initialisation
#
###############################################################################

const pkgdir = joinpath(dirname(pathof(Hecke)), "..")

function MaximalOrder
end

global const maximal_order = MaximalOrder

function __init__()
  # verify some base rings survived serialization/deserialization
  @assert base_ring(Hecke.Globals.Zx) === FlintZZ
  @assert base_ring(Hecke.Globals.Qx) === FlintQQ

  if AbstractAlgebra.should_show_banner() && get(ENV, "HECKE_PRINT_BANNER", "true") != "false"
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
    println("(c) 2015-2024 by Claus Fieker, Tommy Hofmann and Carlo Sircana")
    println()
  end

  #if inNotebook()  # to make toggle work in IJulia
  #  display("text/html", "\$\\require{action}\$")
  #end

  global R = _RealRing()

  global flint_rand_ctx = flint_rand_state()

  resize!(_RealRings, Threads.nthreads())
  for i in 1:Threads.nthreads()
     _RealRings[i] = _RealRing()
  end

end

module Globals
  using Hecke
  const Qx, _ = polynomial_ring(FlintQQ, "x", cached = false)
  const Zx, _ = polynomial_ring(FlintZZ, "x", cached = false)
  const Zxy, _ = polynomial_ring(FlintZZ, ["x", "y"], cached = false)
end

using .Globals

################################################################################
#
#  Aliases
#
################################################################################

include("Aliases.jl")

################################################################################
#
#  AbstractAlgebra/Nemo shenanigans
#
################################################################################

# We have our own factor in Hecke, but some functions in AA fall back to
# AA.factor, so let's add a fallback.

AbstractAlgebra.factor(x::RingElement) = factor(x)

################################################################################
#
#  Verbose printing and custom assertions
#
################################################################################

include("Assertions.jl")

################################################################################
#
#  Setter and getter for objects
#
################################################################################

function is_maximal_order_known(K::AbsSimpleNumField)
  return has_attribute(K, :maximal_order)
end

function conjugate_data_arb(K::AbsSimpleNumField)
  return get_attribute!(K, :conjugate_data_arb) do
    return acb_root_ctx(K.pol)
  end::acb_root_ctx
end

function conjugate_data_arb_roots(K::AbsSimpleNumField, p::Int)
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
  if Nemo.is_cyclo_type(K)
    # There is one real place
    f = get_attribute(K, :cyclo)::Int
    if f == 1
      # x - 1
      p = max(p, 2)
      rall = [one(AcbField(p, cached = false))]
      rreal = [one(ArbField(p, cached = false))]
      rcomplex = Vector{AcbFieldElem}()
    elseif f == 2
      # x + 1
      p = max(p, 2)
      rall = [-one(AcbField(p, cached = false))]
      rreal = [-one(ArbField(p, cached = false))]
      rcomplex = Vector{AcbFieldElem}()
    else
      # Use that e^(i phi) = cos(phi) + i sin(phi)
      # Call sincospi to determine these values
      pstart = max(p, 2) # Sometimes this gets called with -1
      local _rall::Vector{Tuple{ArbFieldElem, ArbFieldElem}}
      rreal = ArbFieldElem[]
      rcomplex = Vector{AcbFieldElem}(undef, div(degree(K), 2))
      while true
        R = ArbField(pstart, cached = false)
        # We need to pair them
        _rall = Tuple{ArbFieldElem, ArbFieldElem}[ sincospi(QQFieldElem(2*k, f), R) for k in 1:f if gcd(f, k) == 1]
        if all(x -> radiuslttwopower(x[1], -p) && radiuslttwopower(x[2], -p), _rall)
          CC = AcbField(pstart, cached = false)
          rall = AcbFieldElem[ CC(l[2], l[1]) for l in _rall]
          j = 1
          good = true
          for i in 1:degree(K)
            if is_positive(_rall[i][1])
              rcomplex[j] = rall[i]
              j += 1
            else
              if !is_negative(_rall[i][1])
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

function signature(K::AbsSimpleNumField)
  return get_attribute!(K, :signature) do
    return signature(defining_polynomial(K))
  end::Tuple{Int, Int}
end

function _get_prime_data_lifting(K::AbsSimpleNumField)
  return get_attribute!(K, :_get_prime_data_lifting) do
    return Dict{Int,Any}()
  end::Dict{Int,Any}
end

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

################################################################################
#
#  Jupyter notebook check
#
################################################################################

function inNotebook()
  return isdefined(Main, :IJulia) && Main.IJulia.inited
end

################################################################################
#
#  Abstract map type
#
################################################################################

abstract type HeckeMap <: SetMap end  #needed here for the hasspecial stuff
             #maybe move to Maps?

import AbstractAlgebra: get_attribute, set_attribute!, @show_name, @show_special,
       _get_attributes, _get_attributes!, _is_attribute_storing_type,
       @show_special_elem, @attributes, extra_name, set_name!, get_name

# Hecke maps store attributes in the header object
_get_attributes(G::Map{<:Any, <:Any, HeckeMap, <:Any}) = _get_attributes(G.header)
_get_attributes!(G::Map{<:Any, <:Any, HeckeMap, <:Any}) = _get_attributes!(G.header)
_is_attribute_storing_type(::Type{Map{<:Any, <:Any, HeckeMap, <:Any}}) = true

import Nemo: libflint  #to be able to reference libraries by full path
                       #to avoid calling the "wrong" copy

const libantic = libflint
const libarb = libflint

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

function test_module(x, new::Bool = true; long::Bool = false, with_gap::Bool = false, with_polymake::Bool = false, coverage = false)
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
     @info("spawning ", `$julia_exe $(coverage ? "--code-coverage" : "") -e \"$cmd\"`)
     proj = Base.active_project()
     if coverage
       run(`$(julia_exe) --code-coverage --project=$(proj) -e $(cmd)`)
     else
       run(`$(julia_exe) --project=$(proj) -e $(cmd)`)
     end
   else
     Hecke.@eval long_test = $long
     Hecke.@eval _with_gap = $with_gap
     Hecke.@eval _with_polymake = $with_polymake
     assertions(true)
     @info("Running tests for $x in same session")
     Base.include(Main, setup_file)
     Base.include(Main, test_file)
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
      if get_verbosity_level($(args[1])) >= 1
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
      if get_verbosity_level($(args[1])) >= $(args[2])
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
    if get_verbosity_level($flag) >= $level
      _vtime_add($(esc(var)).time, $key, $(esc(value)))
    end
  end
end

macro vtime_add_elapsed(flag, level, var, key, stmt)
  quote
    tm = @elapsed $(esc(stmt))
    if get_verbosity_level($flag) >= $level
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
add_assertion_scope(:PID_Test)

################################################################################
#
#  Function stub
#
################################################################################

# - The following function is introduced in src/ModAlgAss/*
# - The Hecke.MPolyFactor submodule wants to extend it, but is loaded earlier
# - Introduce the function here, to make everyone happy
function is_absolutely_irreducible end

################################################################################
#
#  "Submodules"
#
################################################################################

include("HeckeTypes.jl")
include("Sparse.jl")
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
include("GenOrd.jl")
include("FunField.jl")
include("BigComplex.jl")
include("conjugates.jl")
include("analytic.jl")
include("helper.jl")
include("EllCrv.jl")
include("HypellCrv.jl")
include("LargeField.jl")
include("RCF.jl")
include("ModAlgAss.jl")
include("AlgAss.jl")
include("AlgAssAbsOrd.jl")
include("AlgAssRelOrd.jl")
include("LocalField.jl")
include("QuadForm.jl")
include("FieldFactory.jl")
include("RieSrf.jl")
include("../examples/NFDB.jl")

const _RealRings = _RealRing[_RealRing()]

################################################################################
#
#  Precompilation
#
################################################################################

#precompile(maximal_order, (AbsSimpleNumField, ))

################################################################################
#
#  Object overloading for map types
#
################################################################################

#for T in subtypes(Map(HeckeMap))
#  (M::T)(a) = image(M, a)
#end

(f::Map{D, C, <:Hecke.HeckeMap, T} where {D, C, T})(x) = image(f, x)

################################################################################
#
#  Verbose printing
#
################################################################################

@doc raw"""
    vshow(A) -> Nothing

Prints all fields of $A$.
"""
function vshow(A)
  for i in fieldnames(typeof(A))
    if isdefined(A, i)
      print("$i: ")
      println(getfield(A, i), "\n")
    else
      println("$i: Not defined")
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

################################################################################
#
#  Aliases
#
################################################################################

has_root(a...) = is_power(a...)  # catch all... needs revisiting:
                               #has_root(poly) != is_power(poly)....

Base.issubset(K::NumField, L::NumField) = is_subfield(K, L)[1]
Base.issubset(C::ClassField, B::ClassField) = is_subfield(C, B)


################################################################################
#
#  Deprecations
#
################################################################################

include("Deprecations.jl")

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

function build_doc(; doctest=false, strict=false, format=:vitepress)
  if !isdefined(Main, :Build)
    doc_init()
  end
  Pkg.activate(docsproject) do
    Base.invokelatest(Main.Build.make, Hecke; strict=strict, local_build=true, doctest=doctest, format=format)
  end
  if format == :html
    open_doc()
  elseif format == :vitepress
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
  for f in sym
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
      try
        z = getproperty(M, a)
        if isa(z, AbstractArray) || isa(z, AbstractDict)
          push!(sym, ((M,a), z))
        end
    catch e
    end
  end
  return sym
end

const protect = [
  # We need to protect protect itself :)
  # Otherwise it might emptied and then everything
  # is emptied.
  (Hecke, :protect),

  (Hecke, :ASSERT_LOOKUP),
  (Hecke, :VERBOSE_LOOKUP),
  (Hecke, :ASSERT_SCOPE),
  (Hecke, :VERBOSE_SCOPE),
  (Hecke, :_euler_phi_inverse_maximum),
  (Hecke, :odlyzko_bound_grh),
  (Hecke, :nC), (Hecke, :B1), #part of ECM
  (Hecke, :VERBOSE_PRINT_INDENT),
  (Hecke, :_RealRings),
]

function clear_cache(sym::Vector{Any})
  for f in sym
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

precompile(maximal_order, (AbsSimpleNumField, ))
precompile(class_group, (AbsSimpleNumFieldOrder,))

@inline __get_rounding_mode() = Base.MPFR.rounding_raw(BigFloat)

using .NormRel

#if ccall(:jl_generating_output, Cint, ()) == 1   # if we're precompiling the package
#  let
#    include(joinpath("..", "system", "precompile.jl"))
#  end
#end

################################################################################
#
#  Extended methods by GAPExt
#
################################################################################

function fields
end

function IdGroup
end

function check_obstruction
end

function field_context
end

function primitive_frobenius_extensions
end

################################################################################
#
#  Extended methods by PolymakeExt
#
################################################################################

function solve_mixed
end

end # module
