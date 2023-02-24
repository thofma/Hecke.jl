#$##############################################################################
#
#    Misc/Infinite.jl: Infinity
#
# This file is part of Hecke.
#
# Copyright (c) 2015-2019: Claus Fieker, Tommy Hofmann
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
#  Copyright (C) 2019 Tommy Hofmann
#
################################################################################

export PosInf, inf, IntExt

# This is a type for positive infinity for use in valuations.

struct PosInf
end

const inf = PosInf()

+(::Int, ::PosInf) = inf

+(::PosInf, ::Int) = inf

+(::PosInf, ::PosInf) = inf

-(::PosInf, ::Int) = inf

max(::Int, ::PosInf) = inf

max(::PosInf, ::Int) = inf

Base.isless(::Int, ::PosInf) = true

Base.isless(x::Rational{Int}, ::PosInf) = denominator(x) != 0

Base.isless(::PosInf, ::PosInf) = false

Base.isless(::PosInf, ::Int) = false

Base.isless(::PosInf, ::Rational{Int}) = false

Base.isfinite(::PosInf) = false

Base.isinf(::PosInf) = true

Base.isone(::PosInf) = false

Base.iszero(::PosInf) = false

Base.one(::PosInf) = 1

Base.zero(::PosInf) = 0

Base.isless(::PosInf, ::ZZRingElem) = false

Base.isless(::ZZRingElem, ::PosInf) = true

Base.isless(::PosInf, ::QQFieldElem) = false

Base.isless(::QQFieldElem, ::PosInf) = true

const IntExt = Union{Int, PosInf}

is_positive(::PosInf) = true

@doc Markdown.doc"""
    is_infinite(x::Any) -> Bool

Tests whether $x$ is infinite, by returning `!isfinite(x)`.
"""
is_infinite(x::Any) = !isfinite(x)
