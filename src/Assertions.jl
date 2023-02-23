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

@doc Markdown.doc"""
   add_verbose_scope(s::Symbol) -> Nothing

Add the symbol `s` to the list of (global) verbose scopes.

# Examples

```jldoctest

julia> add_verbose_scope(:MyScope)

```
"""
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

@doc Markdown.doc"""
    @vprint :S k str

This macro can be used to control printing contexts inside the code.

It has to be followed by two or three arguments: a symbol `:S` refered as a
*verbose scope*, an optional integer `k` and a string `str`.

To each verbose scope `:S` is associated a *verbose level* `l` which is cached.
The macro `@vprint` triggers the printing of the associated string `str` if the
verbose level `l` of `S` is bigger or equal to `k.`

One can add a new verbose scope by calling the function [`add_verbose_scope`](@ref).

When starting a new instance, all the verbose levels are set to 0. One can adjust the
verbose level of any scope by calling the function [`set_verbose_level`](@ref).

One can access the current verbose level of any scope at any time by calling the
function [`get_verbose_level`](@ref).

# Example

We will set up different scopes with different scope levels in a custom function
to show how to use this macro.

```jldoctest

julia> add_verbose_scope(:Test1)

julia> add_verbose_scope(:Test2)

julia> add_verbose_scope(:Test3)

julia> set_verbose_level(:Test1, 1)
1

julia> set_verbose_level(:Test2, 3)
3

julia> function vprint_example()
       @vprint :Test1 "Triggering level 1 by default, verbose level 1: to be printed\n"
       @vprint :Test2 2 "Triggering level 2, verbose level 3: to be printed\n"
       @vprint :Test3 "Triggering level 1 by default, verbose level 0 by default: not to be printed\n"
       @vprint :Test2 4 "Triggering level 4, verbose level 3: not to be printed\n"
       end
vprint_example (generic function with 1 method)

julia> vprint_example()
Triggering level 1 by default, verbose level 1: to be printed
Triggering level 2, verbose level 3: to be printed
```

If one does not setup in advance a verbose scope, the macro will trigger an
ExceptionError showing "Not a valid symbol" since no verbose scope would have been
attached to the input symbol.
"""
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

@doc Markdown.doc"""
    set_verbose_level(s::Symbol, l::Int) -> Int

If `s` represents a symbol of a known verbose scope, set the current
verbose level of `s` to `l`.

One can access the current verbose level of `s` by calling the function
[`get_verbose_level`](@ref).

If `s` is not yet known as a verbose scope, the function triggers an ErrorException
showing "Not a valid symbol". One can add `s` to the list of verbose scopes by calling
the function [`add_verbose_scope`](@ref).

# Example

```jldoctest
julia> add_verbose_scope(:MyScope)

julia> set_verbose_level(:MyScope, 4)
4
```
"""
function set_verbose_level(s::Symbol, l::Int)
  !(s in VERBOSE_SCOPE) && error("Not a valid symbol")
  VERBOSE_LOOKUP[s] = l
end

@doc Markdown.doc"""
    get_verbose_level(s::Symbol) -> Int

If `s` represents a symbol of a known verbose scope, return the current
verbose level of `s`.

One can modify the current verbose level of `s` by calling the function
[`set_verbose_level`](@ref).

If `s` is not yet known as a verbose scope, the function triggers an ErrorException
showing "Not a valid symbol". One can add `s` to the list of verbose scopes by calling
the function [`add_verbose_scope`](@ref).

# E
"""
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
