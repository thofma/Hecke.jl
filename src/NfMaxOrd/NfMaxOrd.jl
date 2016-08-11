################################################################################
#
#       NfMaxOrd.jl : Maximal orders in absolute number fields
#
# This file is part of Hecke.
#
# Copyright (c) 2015, 2016: Claus Fieker, Tommy Hofmann
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
# (C) 2015, 2016 Tommy Hofmann
#
################################################################################

export maximal_order, ring_of_integers

################################################################################
#
#  Constructors for users
#
################################################################################

doc"""
***
    MaximalOrder(K::AnticNumberField) -> NfMaxOrd

> Returns the maximal order of $K$.

**Example**

    julia> Qx, x = QQ["x"]
    julia> K, a = NumberField(x^3 + 2, "a")
    julia> O = MaximalOrder(K)
"""
function _MaximalOrder(K::AnticNumberField)
  O = EquationOrder(K)
  @vprint :NfMaxOrd 1 "Computing the maximal order ...\n"
  O = _MaximalOrder(O)
  @vprint :NfMaxOrd 1 "... done\n"
  return NfMaxOrd(K, basis_mat(O))
end

doc"""
    MaximalOrder(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfMaxOrd

> Assuming that ``primes`` contains all the prime numbers at which the equation
> order $\mathbf{Z}[\alpha]$ of $K = \mathbf{Q}(\alpha)$ is not maximal,
> this function returns the maximal order of $K$.
"""
function _MaximalOrder(K::AnticNumberField, primes::Array{fmpz, 1})
  O = EquationOrder(K)
  @vprint :NfMaxOrd 1 "Computing the maximal order ...\n"
  O = _MaximalOrder(O, primes)
  @vprint :NfMaxOrd 1 "... done\n"
  return NfMaxOrd(K, basis_mat(O))
end

doc"""
    make_maximal(O::NfOrd) -> NfMaxOrd

> Assuming that $\mathcal O$ is an order, this function returns the same order
> as a maximal order.
"""
function make_maximal(O::NfOrd)
  return NfMaxOrd(nf(O), basis_mat(O))
end

doc"""
    maximal_order(K::AnticNumberField) -> NfMaxOrd
    ring_of_integers(K::AnticNumberField) -> NfMaxOrd

> Returns the maximal order of $K$.
"""
function maximal_order(K::AnticNumberField)
#  try
#    c = _get_maximal_order_of_nf(K)::NfMaxOrd
#    return c
#  catch
    O = _MaximalOrder(K)::NfMaxOrd
#    _set_maximal_order_of_nf(K, O)
    return O
#  end
end

doc"""
    maximal_order(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfMaxOrd
    maximal_order(K::AnticNumberField, primes::Array{Integer, 1}) -> NfMaxOrd
    ring_of_integers(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfMaxOrd
    ring_of_integers(K::AnticNumberField, primes::Array{Integer, 1}) -> NfMaxOrd

> Assuming that ``primes`` contains all the prime numbers at which the equation
> order $\mathbf{Z}[\alpha]$ of $K = \mathbf{Q}(\alpha)$ is not maximal
> (e.g. ``primes`` may contain all prime divisors of the discriminant of
> $\mathbf Z[\alpha]$), this function returns the maximal order of $K$.
"""
function maximal_order(K::AnticNumberField, primes::Array{fmpz, 1})
  O = _MaximalOrder(K, primes)
  return O
end

maximal_order{T}(K::AnticNumberField, primes::Array{T, 1}) =
  maximal_order(K, map(FlintZZ, primes))

doc"""
    maximal_order(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfMaxOrd
    maximal_order(K::AnticNumberField, primes::Array{Integer, 1}) -> NfMaxOrd
    ring_of_integers(K::AnticNumberField, primes::Array{fmpz, 1}) -> NfMaxOrd
    ring_of_integers(K::AnticNumberField, primes::Array{Integer, 1}) -> NfMaxOrd

> Assuming that ``primes`` contains all the prime numbers at which the equation
> order $\mathbf{Z}[\alpha]$ of $K = \mathbf{Q}(\alpha)$ is not maximal,
> this function returns the maximal order of $K$.
"""
ring_of_integers(x...) = maximal_order(x...)

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, O::NfMaxOrd)
  print(io, "Maximal order of $(nf(O)) \nwith basis $(O.basis_nf)")
end

Base.promote_rule(::Type{NfOrdElem{NfMaxOrd}}, ::Type{Int}) = NfOrdElem{NfMaxOrd}

function addeq!(a::NfOrdElem{NfMaxOrd}, b::NfOrdElem{NfMaxOrd})
  addeq!(a.elem_in_nf, b.elem_in_nf)
end

