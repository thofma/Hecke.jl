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
# (C) 2015, 2016 Claus Fieker, Tommy Hofmann
#
################################################################################

__precompile__()

module Hecke

using Nemo

################################################################################
#
#  Load FPlll if available
#
################################################################################

if isdir(joinpath(Pkg.dir(),"FPlll"))
  using FPlll
end

################################################################################
#
#  Import/export
#
################################################################################

import Nemo: nf_elem, AnticNumberField, degree,
             den, num, parent, length,
             norm, real, imag, inv, rows, getindex!, lll, hnf, cols, 
             trace, factor, mod, zero, 
             hash, PolynomialRing, coeff,
             var, abs, min, iszero, one, sqrt, isone, deepcopy, rank, in,
             discriminant, log, sub, lift, FlintQQ, FlintZZ, elem_type,
             elem_from_mat_row, elem_to_mat_row!, order, signature,
             base_ring, compose, root, arf_struct, fmpq, valuation, remove,
             Ring, prec, conj, mul!, gen, divexact, derivative, zero!, divrem,
             resultant, evaluate, setcoeff!, div, isodd, iseven, max, floor,
             ceil, //, setindex!, transpose, colon, nf_elem, isreal,
             MatrixSpace, contains, overlaps, solve, unique_integer, gcd,
             minpoly, charpoly, det, howell_form, needs_parentheses, ishnf,
             isnegative, parent_type, intersect, lcm, strong_echelon_form,
             strong_echelon_form!, howell_form!, add!, mul!, fmpq_poly,
             FmpzPolyRing, FlintFiniteField, addeq!, acb_vec, array,
             acb_struct, acb_vec_clear, lufact!, agm, height, characteristic,
             roots, isprime


export AnticNumberField, hash, update, nf, next_prime, dot, maximal_order

import Base: show, minimum, rand, prod, copy, rand!, call, rand, ceil, round, 
             size, dot, in, powermod, ^, getindex, ==, <, >, +, *, /, \, -, !=,
             getindex, setindex!, transpose, getindex, //, colon, exp, div,
             floor, max, BigFloat, promote_rule, precision, dot,
             first, StepRange, show, one, zero, inv, iseven, isodd, convert,
             angle, abs2, isless, exponent, base, isfinite, zeros

# To make all exported Nemo functions visible to someone using "using Hecke"
# we have to export everything again

for i in names(Nemo)
  eval(Expr(:export, i))
end

export @vprint, @hassert, @vtime, add_verbose_scope, get_verbose_level,
       set_verbose_level, add_assert_scope, get_assert_level, set_assert_level,
       update, @timeit, show, StepRange, domain, codomain, image, preimage,
       modord, resultant, @test_and_infer

###############################################################################
#
#   Library initialisation
#
###############################################################################

const pkgdir = realpath(joinpath(dirname(@__FILE__), ".."))
const libhecke = joinpath(pkgdir, "local", "lib", "libhecke")
const libdir = joinpath(pkgdir, "local", "lib")

function __init__()

  println("")
  print("Welcome to \n")
  print_with_color(:red, "
  _    _           _        
 | |  | |         | |       
 | |__| | ___  ___| | _____ 
 |  __  |/ _ \\\/ __| |/ / _ \\
 | |  | |  __/ (__|   <  __/
 |_|  |_|\\___|\\___|_|\\_\\___|
  ")

  println()
  print("Version")
  print_with_color(:green, " $VERSION_NUMBER ")
  print("... \n ... which comes with absolutely no warranty whatsoever")
  println()
  println("(c) 2015, 2016, 2017 by Claus Fieker and Tommy Hofmann")
  println()
  
  if "HOSTNAME" in keys(ENV) && ENV["HOSTNAME"] == "juliabox"
    push!(Libdl.DL_LOAD_PATH, "/usr/local/lib")
  elseif is_linux()
    push!(Libdl.DL_LOAD_PATH, libdir)
    Libdl.dlopen(libhecke)
  else
    push!(Libdl.DL_LOAD_PATH, libdir)
	ENV["PATH"] = ENV["PATH"] * ";" * joinpath(Pkg.dir("Nemo"), "local", "lib")
  end
  
  t = create_accessors(AnticNumberField, acb_root_ctx, get_handle())
  global _get_nf_conjugate_data_arb = t[1]
  global _set_nf_conjugate_data_arb = t[2]

  t = create_accessors(AnticNumberField,
                       Tuple{Array{nf_elem, 1}, nf_elem},
                       get_handle())
  global _get_nf_torsion_units = t[1]
  global _set_nf_torsion_units = t[2]

  t = create_accessors(AnticNumberField, NfMaxOrd, get_handle())

  global _get_maximal_order_of_nf = t[1]
  global _set_maximal_order_of_nf = t[2]

  t = create_accessors(NfMaxOrd, ClassGrpCtx, get_handle())

  global _get_ClassGrpCtx_of_order = t[1]
  global _set_ClassGrpCtx_of_order = t[2]

  t = create_accessors(AnticNumberField, roots_ctx, get_handle())

  global _get_roots_ctx_of_nf = t[1]
  global _set_roots_ctx_of_nf = t[2]

  global R = _RealRing()
  
  # Stuff for elliptic curves
  # polynomial rings Zx = ZZ[x] and _Zxy = ZZ[x,y]
  # will be removed eventually
  global const _Zx = PolynomialRing(FlintZZ, "_x")[1]
  global const _Zxy = PolynomialRing(_Zx, "_y")[1]
  global const _x = gen(_Zx)
  global const _y = gen(_Zxy)

end

function conjugate_data_arb(K::AnticNumberField)
  try
    c = _get_nf_conjugate_data_arb(K)::acb_root_ctx
    return c
  catch
    c = acb_root_ctx(K.pol)
    _set_nf_conjugate_data_arb(K, c)
    return c
  end
end

function _torsion_units(K::AnticNumberField)
  try
    c = _get_nf_torsion_units(K)::Tuple{Array{nf_elem, 1}, nf_elem}
    return c
  catch
    O = maximal_order(K)
    tor, gen = _torsion_units(O)
    tornf = [ elem_in_nf(x) for x in tor]
    gennf = elem_in_nf(gen)
    _set_nf_torsion_units(K, (tornf, gennf))
    return tornf, gennf
  end
end

function torsion_units(K::AnticNumberField)
  ar, g = _torsion_units(K)
  return ar
end

function torsion_units_gen(K::AnticNumberField)
  ar, g = _torsion_units(K)
  return g
end

################################################################################
#
#  Version number
#
################################################################################

global VERSION_NUMBER = v"0.1.5"

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
      if get_verbose_level($(args[1])) >= 1
       $(esc(args[2]))
      end
    end
  elseif length(args) == 3
    quote
      if get_verbose_level($(args[1])) >= $(args[2])
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

################################################################################
#   Do @infert and @test simultanously
#
################################################################################

macro test_and_infer(f,args,res)
  quote
    if isa($(esc(args)), Tuple)
      Base.Test.@inferred $(esc(f))($(esc(args))...)
      Base.Test.@test $(esc(f))($(esc(args))...) == $(esc(res))
    else
      Base.Test.@inferred $(esc(f))($(esc(args)))
      local t = $(esc(res))
      Base.Test.@test $(esc(f))($(esc(args))) == t
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

################################################################################
#
#  Functions for timings
#
################################################################################

macro timeit(args...)
  loops = 50
  if length(args) == 2
    loops = esc(args[2])
  end

  quote
    gc_enable(false)
    # warm-up
    local val = $(esc(args[1]))

    local min = Inf
    local max = 0
    local sum = 0.0
    local t0, diff
    local i
    for i in 1:$(loops)
      t0 = time_ns()
      local val = $(esc(args[1]))
      diff = time_ns() - t0
      if diff > max
        max = diff
      end
      if diff < min
        min = diff
      end
      sum += diff
    end
    sum = sum/$(loops)
    print("max: $(max/1e9)\nmin: $(min/1e9)\nsum: $(sum/1e9)\n")
    gc_enable(true)
    nothing
  end
end

function timeit(expr::Expr)
  @timeit expr
end

################################################################################
#
#  Exception types
#
################################################################################

type LowPrecisionCholesky <: Exception end

Base.showerror(io::IO, e::LowPrecisionCholesky) =
    print(io, e.var, """
    Negative diagonal in Cholesky decomposition, probably a precision issue""")

type LowPrecisionLLL <: Exception end

Base.showerror(io::IO, e::LowPrecisionLLL) =
    print(io, e.var, """
    Transformation matrix has too large entries relative to precision in LLL""")

# what is this function doing here?
function checkbounds(a::Int, b::Int) nothing; end;

################################################################################
#
#  "Submodules"
#
################################################################################

include("HeckeTypes.jl")
include("Misc.jl")
include("LinearAlgebra.jl")
include("BigComplex.jl")
include("conjugates.jl")
#include("NfMaxOrd/NfOrdCls.jl")
include("NfOrd.jl")
include("analytic.jl")
include("NfMaxOrd.jl")
include("Map.jl")
include("helper.jl")
include("EllCrv.jl")
include("LargeField.jl")

for T in subtypes(Map)
  (M::T)(a) = image(M, a)
end

################################################################################
#
#  Verbose printing
#
################################################################################

doc"""
***
    vshow(A) -> Void

> Prints all fields of $A$.
"""
function vshow(A)
  for i in fieldnames(typeof(A))
    if isdefined(A, i)
      println("$i: ")
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

elem_type(::NfMaxOrd) = NfOrdElem{NfMaxOrd}

elem_type(::Type{NfMaxOrd}) = NfOrdElem{NfMaxOrd}

elem_type(::NfOrdGen) = NfOrdElem{NfOrdGen}

elem_type(::Type{NfOrdGen}) = NfOrdElem{NfOrdGen}

elem_type{T}(::Type{FacElemMon{T}}) = FacElem{T}

elem_type(::Type{AnticNumberField}) = nf_elem

elem_type(::Type{FqNmodFiniteField}) = fq_nmod

elem_type{T}(::Type{GenResRing{T}}) = GenRes{T}

################################################################################
#
#  Parent types for element types
#
################################################################################

parent_type(::Type{NfOrdElem{NfMaxOrd}}) = NfMaxOrd

################################################################################
#
#  An update function 
#
################################################################################

function update()

  olddir = pwd()

  println("Updating Hecke ... ")
  cd(Pkg.dir("Hecke"))
  run(`git pull`)
  
  pkgdir = Pkg.dir("Nemo")

  println("Updating Nemo ... ")
  cd("$pkgdir")
  run(`git pull`)

  println("Updating antic ... ")
  cd("$pkgdir/deps/antic")
  run(`git pull`)

  println("Updating flint ... ")
  cd("$pkgdir/deps/flint2")
  run(`git pull`)
  run(`make -j`)
  run(`make install`)

  println("Updating arb ... ")
  cd("$pkgdir/deps/arb")
  run(`git pull`)
  run(`make -j`)
  run(`make install`)

 
  cd(olddir)
end

function whos(io::IO=STDOUT, m::Module=current_module(), pattern::Regex=r"")
    maxline = Base.tty_size()[2]
    line = zeros(UInt8, maxline)
    head = PipeBuffer(maxline + 1)
    for v in sort!(names(m, true)) # show also NON exported stuff!
        s = string(v)
        if isdefined(m, v) && ismatch(pattern, s)
            value = getfield(m, v)
            @printf head "%30s " s
            try
                bytes = Base.summarysize(value)
                if bytes < 10_000
                    @printf(head, "%6d bytes  ", bytes)
                else
                    @printf(head, "%6d KB     ", bytes ÷ (1024))
                end
                print(head, Base.summary(value))
            catch e
                print(head, "#=ERROR: unable to show value=#")
                println(e)
            end

            newline = search(head, UInt8('\n')) - 1
            if newline < 0
                newline = nb_available(head)
            end
            if newline > maxline
                newline = maxline - 1 # make space for ...
            end
            line = resize!(line, newline)
            line = read!(head, line)

            Base.write(io, line)
            if nb_available(head) > 0 # more to read? replace with ...
                print(io, '\u2026') # hdots
            end
            println(io)
            seekend(head) # skip the rest of the text
        end
    end
end

whos(m::Module, pat::Regex=r"") = whos(STDOUT, m, pat)
whos(pat::Regex) = whos(STDOUT, current_module(), pat)

################################################################################
#
#  Testing only "submodules"
#
################################################################################

function test_module(x, y = :all)
   julia_exe = Base.julia_cmd()
   if y == :all
     test_file = joinpath(pkgdir, "test/$x.jl")
   else
     test_file = joinpath(pkgdir, "test/$x/$y.jl")
   end

   cmd = "using Base.Test; using Hecke; include(\"$test_file\");"
   info("spawning ", `$julia_exe -e \"$cmd\"`)
   run(`$julia_exe --color=yes -e $cmd`)
end

#
# stuff for 0.5
# 

if VERSION > v"0.5.0-"
  @inline __get_rounding_mode() = Base.MPFR.rounding_raw(BigFloat)
end

if VERSION < v"0.5.0-"
  @inline __get_rounding_mode() = Base.MPFR.ROUNDING_MODE[end]
end

end
