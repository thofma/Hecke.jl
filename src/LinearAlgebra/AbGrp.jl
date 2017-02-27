################################################################################
#
#             AbGrp.jl : Finitely generated abelian groups
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
#  Copyright (C) 2015, 2016 Tommy Hofmann
#
################################################################################

export AbGrp, AbGrpElem, parent, is_finite, is_infinite, rank, length,
       getindex, show, +, *

################################################################################
#
#  Parent and element types
#
################################################################################

# At the moment support only for diagonal relation matrices
# We hash the sorted diagonal

const AbGrpID = Dict{Array{fmpz, 1}, Nemo.Set}()

type AbGrp <: Nemo.Set
  diagonal::Array{fmpz, 1}
  inf_num::Int
  fin_num::Int
  
  function AbGrp(a::Array{fmpz, 1})
    sort!(a)
    #println(a, " ",hash(a))
    if haskey(AbGrpID, a)
      return AbGrpID[a]::AbGrp
    else
      z = new()
      z.diagonal = a
      z.inf_num = findfirst(x -> x != 0, a) - 1
      z.fin_num = length(a) - z.inf_num
      AbGrpID[a] = z
      return z
    end
  end
  
  function AbGrp(a::Array{Int, 1})
    return AbGrp(map(fmpz, a))
  end
end

type AbGrpElem
  parent::AbGrp
  coord::Array{fmpz, 1}

  function AbGrpElem(A::AbGrp, a::Array{fmpz, 1})
    z = new()
    z.parent = A
    z.coord = a
    return z
  end
end

################################################################################
#
#  Field access
#
################################################################################

doc"""
***
    parent(x::AbGrpElem) -> AbGrp
 
> Returns the parent of $x$.
"""
function parent(x::AbGrpElem)
  return x.parent
end

################################################################################
#
#  Predicates and basic invariants
#
################################################################################

doc"""
***
    is_finite(A::AbGrp) -> Bool

> Returns whether $A$ is finite.
"""
is_finite(A::AbGrp) = A.inf_num == 0 ? true : false

doc"""
***
    is_infinite(A::AbGrp) -> Bool

> Returns whether $A$ is infinite.
"""
is_infinite(A::AbGrp) = !is_finite(A)

doc"""
***
    rank(A::AbGrp) -> Int

> Returns the rank of $A$, that is, the dimension of the
> $\mathbf{Q}$-vectorspace $A \otimes_{\mathbf Z} \mathbf Q$.
"""
rank(A::AbGrp) = A.inf_num

doc"""
***
    length(A::AbGrp) -> Int

> ??
"""
length(A::AbGrp) = length(A.diagonal)

doc"""
***
    getindex(x::AbGrpElem, i::Int) -> fmpz

> Returns the $i$-th component of the element $x$.
"""
function getindex(x::AbGrpElem, i::Int)
  return x.coord[i]
end

doc"""
***
    order(A::AbGrpElem, i::Int) -> fmpz

> Returns the order of $A$. It is assumed that $A$ is not infinite.
"""
function order(A::AbGrp)
  is_infinite(A) && error("Group must be finite")
  return prod(A.diagonal)
end

################################################################################
#
#  I/O
#
################################################################################

function show(io::IO, A::AbGrp)
  print(io, "Abelian group\n")

  if A.inf_num > 0
    print(io, "Z")
  end

  for i in 1:A.inf_num - 1
    print(io, " x Z")
  end

  if A.fin_num > 0 && A.inf_num > 0
    print(io, " x ")
  end

  if A.fin_num > 0
    print(io, "Z/$(A.diagonal[A.inf_num + 1])")
  end

  for i in 2:A.fin_num 
    print(io, " x Z/$(A.diagonal[A.inf_num + i])")
  end
end

function show(io::IO, a::AbGrpElem)
  print(io, "Element of\n$(a.parent)\n with components\n$(a.coord)")
end

################################################################################
#
#  Addition
#
################################################################################

doc"""
***
    +(x::AbGrpElem, y::AbGrpElem) -> AbGrpElem

> Computes $x + y$.
"""
function +(x::AbGrpElem, y::AbGrpElem)
  parent(x) != parent(y) && error("Parents must coincide")
  z = Array{fmpz}(length(x.coord))
  for i in 1:length(z)
    z[i] = x.coord[i] + y.coord[i]
  end
  return parent(x)(z) # this gives the reduced element
end

################################################################################
#
#  Scalar multiplication
#
################################################################################

doc"""
***
    *(x::Integer, y::AbGrpElem) -> AbGrpElem

> Computes $x \cdot y$.
"""
function *(x::Integer, y::AbGrpElem)
  z = parent(x)()
  for i in 1:length(z)
    z.coord[i] = x*y.coord[i]
  end
  return z
end

*(x::AbGrpElem, y::Integer) = y*x

doc"""
***
    *(x::fmpz, y::AbGrpElem) -> AbGrpElem

> Computes $x \cdot y$.
"""
function *(x::fmpz, y::AbGrpElem)
  z = parent(x)()
  for i in 1:length(z)
    z.coord[i] = x*y.coord[i]
  end
  return z
end

*(x::AbGrpElem, y::fmpz) = y*x

################################################################################
#
#  Parent object overloading
#
################################################################################

doc"""
***
    (A::AbGrp)(x::Array{fmpz, 1}) -> AbGrpElem

> Given an array of elements of type `fmpz` of the same length as $A$, this
> function returns the element of $A$ with components `x`.
"""
function (A::AbGrp)(x::Array{fmpz, 1})
  length(A) != length(x) && error("Lengths do not coincide")
  y = deepcopy(x)
  for i in A.inf_num + 1:length(y)
    y[i] = mod(x[i], A.diagonal[i])
  end
  z = AbGrpElem(A, y)
  return z
end

doc"""
***
    (A::AbGrp, x::Array{Integer, 1}) -> AbGrpElem

> Given an array of elements of type `Integer` of the same length as $A$, this
> function returns the element of $A$ with components `x`.
"""
function (A::AbGrp){T <: Integer}(x::Array{T, 1})
  length(A) != length(x) && error("Lengths do not coincide")
  z = A(map(fmpz, x))
  return z
end

doc"""
***
    getindex(A::AbGrp, i::Int) -> AbGrpElem

> Returns the element of $A$ with components $(0,\dotsc,0,1,0,\dotsc,0)$,
> where the $1$ is at the $i$-th position.
"""
function getindex(A::AbGrp, i::Int)
  z = Array{fmpz}(length(A.diagonal))
  for j in 1:length(A.diagonal)
    z[j] = fmpz()
  end
  z[i] = fmpz(1)
  return AbGrpElem(A, z)
end

