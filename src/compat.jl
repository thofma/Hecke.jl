################################################################################
# Copyright (c) 2009-2014: Jeff Bezanson, Stefan Karpinski, Viral B. Shah,
# and other contributors:
# 
# https://github.com/JuliaLang/julia/contributors
#
# Copyright (C) 2015, Tommy Hofmann
# 
# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:
# 
# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

if v"0.4" <= VERSION < v"0.5-"
  import Base: precision

  precision(::Type{BigFloat}) = Base.MPFR.DEFAULT_PRECISION[end]

  function setprecision(::Type{BigFloat}, precision::Int)
    if precision < 2
      throw(DomainError())
    end
    Base.MPFR.DEFAULT_PRECISION[end] = precision
  end

  setprecision(precision::Int) = setprecision(BigFloat, precision)

  function setprecision{T}(f::Function, ::Type{T}, prec::Integer)
    old_prec = precision(T)
    setprecision(T, prec)
    try
      return f()
    finally
      setprecision(T, old_prec)
    end
  end

  setprecision(f::Function, precision::Integer) = setprecision(f, BigFloat, precision)

else
  import Base: precision, setprecision
end

