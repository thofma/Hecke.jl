################################################################################
#
#     Assertions.jl : Verbose printing and custom assertions
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

export @vprint, @hassert, @vtime, add_verbose_scope, get_verbose_level,
       set_verbose_level, add_assert_scope, get_assert_level, set_assert_level
 
################################################################################
#
#  Verbose
#
################################################################################

# Example:
# julia> add_verbose_scope(:Test)
# 
# julia> function f()
#        @vprint :Test 1 "test"
#        end
# f (generic function with 1 method)
# 
# julia> f()
# 
# julia> set_verbose_level(:Test, 1)
# 1
# 
# julia> f()
# test

global const VERBOSE_SCOPE = Symbol[]

global const VERBOSE_LOOKUP = Dict{Symbol, Int}()

global const VERBOSE_PRINT_INDENT = Int[ 0 ]

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
        flush(stdout)
      end
    end
  elseif length(args) == 3
    quote
      if get_verbose_level($(args[1])) >= $(args[2])
        print(_global_indent())
        print($(esc((args[3]))))
        flush(stdout)
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

# Example:
# julia> add_assert_scope(:Test)
# 
# julia> function f()
#        @hassert :Test true == false # the default level is 1
#        end
# f (generic function with 1 method)
# 
# julia> f()
# 
# julia> set_assert_level(:Test, 1)
# 1
# 
# julia> f()
# ERROR: AssertionError: $(Expr(:escape, :(true == false)))
# Stacktrace:
#  [1] macro expansion at /home/thofmann/.julia/dev/Hecke/src/Hecke.jl:482 [inlined]
#  [2] f() at ./REPL[6]:2
#  [3] top-level scope at REPL[11]:1
# 
# julia> function f()
#        @hassert :Test 2 true == false
#        end
# f (generic function with 1 method)
# 
# julia> f()
# 
# julia> set_assert_level(:Test, 3)
# 3
# 
# julia> f()
# ERROR: AssertionError: $(Expr(:escape, :(true == false)))
# Stacktrace:
#  [1] macro expansion at /home/thofmann/.julia/dev/Hecke/src/Hecke.jl:488 [inlined]
#  [2] f() at ./REPL[12]:2
#  [3] top-level scope at REPL[15]:1


global const ASSERT_SCOPE = Symbol[]

global const ASSERT_LOOKUP = Dict{Symbol, Int}()

function add_assert_scope(s::Symbol)
  !(s in ASSERT_SCOPE) && push!(ASSERT_SCOPE, s)
  nothing
end

function set_assert_level(s::Symbol, l::Int)
  !(s in ASSERT_SCOPE) && error("Not a valid symbol")
  if l >= 9000
    @info "Assertion level over 9000! This might be slow"
  end
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

function assertions(flag::Bool)
  for s in Hecke.ASSERT_SCOPE
    flag ? set_assert_level(s, 8999) : set_assert_level(s, 0)
  end
end

################################################################################
#
#  Require
#
################################################################################

macro req(args...)
  @assert length(args) == 2
  quote
    if !($(esc(args[1])))
      throw(ArgumentError($(esc(args[2]))))
    end
  end
end
