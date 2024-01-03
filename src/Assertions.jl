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

################################################################################
#
#  Verbose
#
################################################################################

global const VERBOSE_SCOPE = Symbol[]

global const VERBOSE_LOOKUP = Dict{Symbol, Int}()

global const VERBOSE_PRINT_INDENT = Int[ 0 ]

@doc raw"""
    add_verbosity_scope(s::Symbol) -> Nothing

Add the symbol `s` to the list of (global) verbosity scopes.

# Examples

```jldoctest
julia> add_verbosity_scope(:MyScope)

```
"""
function add_verbosity_scope(s::Symbol)
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
  @assert VERBOSE_PRINT_INDENT[1] >= 0
  nothing
end

function _global_indent()
  s = "  "^VERBOSE_PRINT_INDENT[1]
  return s
end

@doc raw"""
    @vprintln(S::Symbol, k::Int, msg::String)
    @vprintln S k msg

    @vprintln(S::Symbol, msg::String)
    @vprintln S msg

This macro can be used to control printings inside the code.

The macro `@vprintln` takes two or three arguments: a symbol `S` specifying a
*verbosity scope*, an optional integer `k` and a string `msg`. If `k` is not
specified, it is set by default to $1$.

To each verbosity scope `S` is associated a *verbosity level* `l` which is cached.
If the verbosity level $l$ of `S` is bigger than or equal to $k$, the macro `@vprintln`
triggers the printing of the associated string `msg` followed by a newline.

One can add a new verbosity scope by calling the function [`add_verbosity_scope`](@ref).

When starting a new instance, all the verbosity levels are set to $0$. One can adjust the
verbosity level of a verbosity scope by calling the function [`set_verbosity_level`](@ref).

One can access the current verbosity level of a verbosity scope by calling the
function [`get_verbosity_level`](@ref).

# Examples

We will set up different verbosity scopes with different verbosity levels in a
custom function to show how to use this macro.

```jldoctest
julia> add_verbosity_scope(:Test1);

julia> add_verbosity_scope(:Test2);

julia> add_verbosity_scope(:Test3);

julia> set_verbosity_level(:Test1, 1);

julia> set_verbosity_level(:Test2, 3);

julia> function vprint_example()
       @vprintln :Test1 "Triggered"
       @vprintln :Test2 2 "Triggered"
       @vprintln :Test3 "Not triggered"
       @vprintln :Test2 4 "Not triggered"
       end
vprint_example (generic function with 1 method)

julia> vprint_example()
Triggered
Triggered
```

If one does not setup in advance a verbosity scope, the macro will raise an
`ExceptionError` showing the error message "Not a valid symbol".
"""
macro vprintln(s, msg)
  quote
    if get_verbosity_level($s) >= 1
      print(_global_indent())
      println($(esc(msg)))
      flush(stdout)
    end
  end
end

macro vprintln(s, l::Int, msg)
  quote
    if get_verbosity_level($s) >= $l
      print(_global_indent())
      println($(esc(msg)))
      flush(stdout)
    end
  end
end

@doc raw"""
    @vprint(S::Symbol, k::Int, msg::String)
    @vprint S k msg

    @vprint(S::Symbol, msg::String)
    @vprint S msg

The same as [`@vprintln`](@ref), but without the final newline.
"""
macro vprint(s, msg)
  quote
    if get_verbosity_level($s) >= 1
      print(_global_indent())
      print($(esc(msg)))
      flush(stdout)
    end
  end
end

macro vprint(s, l::Int, msg)
  quote
    if get_verbosity_level($s) >= $l
      print(_global_indent())
      print($(esc(msg)))
      flush(stdout)
    end
  end
end

@doc raw"""
    @v_do(S::Symbol, k::Int, act::Expr)
    @v_do S k act

    @v_do(S::Symbol, act::Expr)
    @v_do S act

This macro can be used to control actions inside the code.

The macro `@v_do` takes two or three arguments: a symbol `S` specifying a
*verbosity scope*, an optional integer `k` and an action `act`. If `k` is not
specified, it is set by default to $1$.

To each verbosity scope `S` is associated a *verbosity level* `l`.
If the verbosity level $l$ of `S` is bigger than or equal to $k$, the macro `@v_do` triggers
the action `act`.

One can add a new verbosity scope by calling the function [`add_verbosity_scope`](@ref).

When starting a new instance, all the verbosity levels are set to $0$. One can adjust the
verbosity level of a verbosity scope by calling the function [`set_verbosity_level`](@ref).

One can access the current verbosity level of a verbosity scope by calling the
function [`get_verbosity_level`](@ref).

# Examples

We will set up different verbosity scopes with different verbosity levels in a
custom function to show how to use this macro.

```jldoctest
julia> add_verbosity_scope(:Test1);

julia> add_verbosity_scope(:Test2);

julia> add_verbosity_scope(:Test3);

julia> set_verbosity_level(:Test1, 1);

julia> set_verbosity_level(:Test2, 3);

julia> function v_do_example(a::Int, b::Int, c::Int, d::Int)
       @v_do :Test1 a = 2*a
       @v_do :Test2 2 b = 3*b
       @v_do :Test3 c = 4*c
       @v_do :Test2 4 d = 5*d
       return (a, b, c, d)
       end
v_do_example (generic function with 1 method)

julia> v_do_example(1,1,1,1)
(2, 3, 1, 1)
```

If one does not setup in advance a verbosity scope, the macro will raise an
`ExceptionError` showing the error message "Not a valid symbol".
"""
macro v_do(s, action)
  quote
    if get_verbosity_level($s) >= 1
      $(esc(action))
    end
  end
end

macro v_do(s, l::Int, action)
  quote
    if get_verbosity_level($s) >= $l
      $(esc(action))
    end
  end
end

@doc raw"""
    set_verbosity_level(s::Symbol, l::Int) -> Int

If `s` represents a known verbosity scope, set the current verbosity level of
`s` to `l`.

One can access the current verbosity level of `s` by calling the function
[`get_verbosity_level`](@ref).

If `s` is not yet known as a verbosity scope, the function raises an `ErrorException`
showing the error message "Not a valid symbol". One can add `s` to the list of
verbosity scopes by calling the function [`add_verbosity_scope`](@ref).

# Examples

```jldoctest
julia> add_verbosity_scope(:MyScope)

julia> set_verbosity_level(:MyScope, 4)
4

julia> set_verbosity_level(:MyScope, 0)
0
```
"""
function set_verbosity_level(s::Symbol, l::Int)
  !(s in VERBOSE_SCOPE) && error("Not a valid symbol")
  VERBOSE_LOOKUP[s] = l
end

@doc raw"""
    get_verbosity_level(s::Symbol) -> Int

If `s` represents a known verbosity scope, return the current verbosity level
of `s`.

One can modify the current verbosity level of `s` by calling the function
[`set_verbosity_level`](@ref).

If `s` is not yet known as a verbosity scope, the function raises an `ErrorException`
showing the error message "Not a valid symbol". One can add `s` to the list of
verbosity scopes by calling the function [`add_verbosity_scope`](@ref).

# Examples

```jldoctest
julia> add_verbosity_scope(:MyScope)

julia> get_verbosity_level(:MyScope)
0

julia> set_verbosity_level(:MyScope, 4)
4

julia> get_verbosity_level(:MyScope)
4

julia> set_verbosity_level(:MyScope, 0)
0

julia> get_verbosity_level(:MyScope)
0
```
"""
function get_verbosity_level(s::Symbol)
  !(s in VERBOSE_SCOPE) && error("Not a valid symbol")
  return get(VERBOSE_LOOKUP, s, 0)::Int
end

################################################################################
#
#  Assertions
#
################################################################################

global const ASSERT_SCOPE = Symbol[]

global const ASSERT_LOOKUP = Dict{Symbol, Int}()

@doc raw"""
    add_assertion_scope(s::Symbol) -> Nothing

Add the symbol `s` to the list of (global) assertion scopes.

# Examples

```jldoctest
julia> add_assertion_scope(:MyScope)

```
"""
function add_assertion_scope(s::Symbol)
  !(s in ASSERT_SCOPE) && push!(ASSERT_SCOPE, s)
  nothing
end

@doc raw"""
    set_assertion_level(s::Symbol, l::Int) -> Int

If `s` represents a known assertion scope, set the current assertion level
of `s` to `l`.

One can access the current assertion level of `s` by calling the function
[`get_assertion_level`](@ref).

If `s` is not yet known as an assertion scope, the function raises an `ErrorException`
showing the error message "Not a valid symbol". One can add `s` to the list of
assertion scopes by calling the function [`add_assertion_scope`](@ref).

# Examples

```jldoctest
julia> add_assertion_scope(:MyScope)

julia> set_assertion_level(:MyScope, 4)
4

julia> set_assertion_level(:MyScope, 0)
0
```
"""
function set_assertion_level(s::Symbol, l::Int)
  !(s in ASSERT_SCOPE) && error("Not a valid symbol")
  if l >= 9000
    @info "Assertion level over 9000! This might be slow"
  end
  ASSERT_LOOKUP[s] = l
end

@doc raw"""
    get_assertion_level(s::Symbol) -> Int

If `s` represents a symbol of a known assertion scope, return the current
assertion level of `s`.

One can modify the current assertion level of `s` by calling the function
[`set_assertion_level`](@ref).

If `s` is not yet known as an assertion scope, the function raises an `ErrorException`
showing the error message "Not a valid symbol". One can add `s` to the list of
assertion scopes by calling the function [`add_assertion_scope`](@ref).

# Examples

```jldoctest
julia> add_assertion_scope(:MyScope)

julia> get_assertion_level(:MyScope)
0

julia> set_assertion_level(:MyScope, 1)
1

julia> get_assertion_level(:MyScope)
1

julia> set_assertion_level(:MyScope, 0)
0

julia> get_assertion_level(:MyScope)
0
```
"""
function get_assertion_level(s::Symbol)
  !(s in ASSERT_SCOPE) && error("Not a valid symbol")
  return get(ASSERT_LOOKUP, s, 0)::Int
end

@doc raw"""
    @hassert(S::Symbol, k::Int, assert::Expr)
    @hassert S k assert

    @hassert(S::Symbol, assert::Expr)
    @hassert S assert

This macro can be used to control assertion checks inside the code.

The macro `@hassert` takes two or three arguments: a symbol `S` specifying an
*assertion scope*, an optional integer `k` and an assertion `assert`. If `k`
is not specified, it is set by default to $1$.

To each assertion scope `S` is associated an *assertion level* `l` which is cached.
If the assertion level $l$ of `S` is bigger than or equal to $k$, the macro `@hassert`
triggers the check of the assertion `assert`. If `assert` is wrong, an `AssertionError`
is thrown.

One can add a new assertion scope by calling the function [`add_assertion_scope`](@ref).

When starting a new instance, all the assertion levels are set to $0$. One can adjust the
assertion level of an assertion scope by calling the function [`set_assertion_level`](@ref).

One can access the current assertion level of an assertion scope by calling the
function [`get_assertion_level`](@ref).

# Examples

We will set up different assertion scopes with different assertion levels in a
custom function to show how to use this macro.

```jldoctest
julia> add_assertion_scope(:MyScope)

julia> get_assertion_level(:MyScope)
0

julia> function hassert_test(x::Int)
       @hassert :MyScope 700 mod(x, 3) == 0
       return div(x, 3)
       end
hassert_test (generic function with 1 method)

julia> hassert_test(2)
0

julia> set_assertion_level(:MyScope, 701);

julia> try hassert_test(2)
       catch e e
       end
AssertionError("\$(Expr(:escape, :(mod(x, 3) == 0)))")

julia> hassert_test(3)
1

julia> set_assertion_level(:MyScope, 0)
0
```

If one does not setup in advance an assertion scope, the macro will raise an
`ExceptionError` showing the error message "Not a valid symbol".
"""
macro hassert(s, cond)
  quote
    if get_assertion_level($s) >= 1
      @assert $(esc(cond))
    end
  end
end

macro hassert(s, l::Int, cond)
  quote
    if get_assertion_level($s) >= $l
      @assert $(esc(cond))
    end
  end
end

function assertions(flag::Bool)
  for s in Hecke.ASSERT_SCOPE
    flag ? set_assertion_level(s, 8999) : set_assertion_level(s, 0)
  end
end

################################################################################
#
#  Require
#
################################################################################

@doc raw"""
    @req(assert, msg)
    @req assert msg

Check whether the assertion `assert` is true. If not, throw an `ArgumentError`
with error message `msg`.

The macro `@req` takes two arguments: the first one is an assertion `assert`
(an expression which returns a boolean) and a string `msg` corresponding to the desired
error message to be returned whenever `assert` is false.

If the number of arguments is not 2, an `AssertionError` is raised.

# Examples

```jldoctest
julia> function req_test(x::Int)
       @req iseven(x) "x must be even"
       return div(x,2)
       end
req_test (generic function with 1 method)

julia> try req_test(3)
       catch e e
       end
ArgumentError("x must be even")

julia> try req_test(2)
       catch e e
       end
1

```
"""
macro req(cond, msg)
  quote
    if !($(esc(cond)))
      throw(ArgumentError($(esc(msg))))
    end
  end
end
