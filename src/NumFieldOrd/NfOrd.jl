################################################################################
#
#  AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}.jl
#
################################################################################
#
# Copyright (c) 2015: Tommy Hofmann
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
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

add_verbosity_scope(:AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
add_assertion_scope(:AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})

include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/Clgp/Types.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/LLL.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/LLLctx.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/MaxOrd/MaxOrd.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/MaxOrd/Polygons.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/MaxOrd/MaxOrdNS.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/Elem.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/Ideal.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/FracIdeal.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/Zeta.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/Clgp.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/Unit.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/ResidueField.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/ResidueRing.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/Hensel.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/ResidueRingMultGrp.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/FactorBaseBound.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/FacElem.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/norm_eqn.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/RayClassGrp.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/MaxOrd/DedekindCriterion.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/TorsionUnits.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/StrongEchelonForm.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/LinearAlgebra.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/Overorders.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/PicardGroup.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/NarrowPicardGroup.jl")
