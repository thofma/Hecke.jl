function _arb_get_fmpq(x::ArbFieldElem)
  mid = ccall((:arb_mid_ptr, libarb), Ptr{arf_struct}, (Ref{ArbFieldElem}, ), x)
  e = ZZRingElem()
  m = ZZRingElem()
  b = ccall((:arf_get_fmpz_2exp, libarb), Cint, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{arf_struct}), m, e, mid)
  @assert abs(e) < typemax(Int)
  ee = Int(e)
  return QQFieldElem(m, ZZRingElem(1))*QQFieldElem(2)^(ee)
end

function mul2exp!(z::ArbFieldElem, x::ArbFieldElem, y::Int)
  ccall((:arb_mul_2exp_si, libarb), Nothing, (Ref{ArbFieldElem}, Ref{ArbFieldElem}, Int), z, x, y)
  return nothing
end

function muleq!(z::ArbFieldElem, x::ArbFieldElem, y::ArbFieldElem)
  q = max(bits(x), bits(y))
  ccall((:arb_mul, libarb), Nothing, (Ref{ArbFieldElem}, Ref{ArbFieldElem}, Ref{ArbFieldElem}, Int), z, x, y, q)
  return nothing
end

function muleq!(z::ArbFieldElem, x::ArbFieldElem, y::ZZRingElem)
  ccall((:arb_mul_fmpz, libarb), Nothing, (Ref{ArbFieldElem}, Ref{ArbFieldElem}, Ref{ZZRingElem}, Int), z, x, y, bits(x))
  return nothing
end

function abs!(z::ArbFieldElem, x::ArbFieldElem)
  ccall((:arb_abs, libarb), Nothing, (Ref{ArbFieldElem}, Ref{ArbFieldElem}, Int), z, x, parent(x).prec)
  return nothing
end

function abs!(z::ArbFieldElem, x::AcbFieldElem)
  ccall((:acb_abs, libarb), Nothing, (Ref{ArbFieldElem}, Ref{AcbFieldElem}, Int), z, x, parent(x).prec)
  return nothing
end

function log!(z::ArbFieldElem, x::ArbFieldElem)
  ccall((:arb_log, libarb), Nothing, (Ref{ArbFieldElem}, Ref{ArbFieldElem}, Int), z, x, parent(x).prec)
  return nothing
end

################################################################################
#
#  Get upper bounds for absolute value
#
################################################################################

# 1 = ARF_RND_UP = round away from zero
# 2 = ARF_RND_FLOOR = round towards -infinity
# 3 = ARF_RND_CEIL = round towards +infinity

@doc raw"""
    abs_upper_bound(::Type{ZZRingElem}, x::ArbFieldElem) -> ZZRingElem

Returns a positive integer $b$ of type `ZZRingElem` such that $\lvert x \rvert \leq
b$. It is not guaranteed that $b$ is as tight as possible.
"""
function abs_upper_bound(::Type{ZZRingElem}, x::ArbFieldElem)
  tarf = arf_struct(0, 0, 0, 0)

  ccall((:arf_init, libarb), Nothing, (Ref{arf_struct}, ), tarf)
  ccall((:arb_get_abs_ubound_arf, libarb), Nothing,
        (Ref{arf_struct}, Ref{ArbFieldElem}, Int), tarf, x, 64)

  if ccall((:arf_is_nan, Nemo.libarb), Bool, (Ref{arf_struct}, ), tarf)
    throw(Base.InexactError(:abs_upper_bound, x, ZZRingElem))
  end

  bound = ZZRingElem()
  # round towards +oo
  ccall((:arf_get_fmpz, libarb), Nothing,
        (Ref{ZZRingElem}, Ref{arf_struct}, Cint), bound, tarf, 3)

  ccall((:arf_clear, libarb), Nothing, (Ref{arf_struct}, ), tarf)

  return bound
end

@doc raw"""
    abs_upper_bound(::Type{Float64}, x::Float64) -> Float64

Returns a positive double $b$ such that $\lvert x \rvert \leq b$. It is not
guaranteed that $b$ is as tight as possible.
"""
function abs_upper_bound(::Type{Float64}, x::ArbFieldElem)
  tarf = arf_struct(0, 0, 0, 0)

  ccall((:arf_init, libarb), Nothing, (Ref{arf_struct}, ), tarf)
  ccall((:arb_get_abs_ubound_arf, libarb), Nothing,
        (Ref{arf_struct}, Ref{ArbFieldElem}, Int),
          tarf, x, 64)

  # round towards -oo
  bound = ccall((:arf_get_d, libarb), Cdouble,
                (Ref{arf_struct}, Cint), tarf, 3)

  ccall((:arf_clear, libarb), Nothing, (Ref{arf_struct}, ), tarf)

  return bound
end

@doc raw"""
    upper_bound(::Type{ZZRingElem}, x::ArbFieldElem) -> ZZRingElem

Returns an integer $b$ of type `ZZRingElem` such that $x \leq
b$. It is not guaranteed that $b$ is as tight as possible.
"""
function upper_bound(::Type{ZZRingElem}, x::ArbFieldElem)
  tarf = arf_struct(0, 0, 0, 0)

  ccall((:arf_init, libarb), Nothing, (Ref{arf_struct}, ), tarf)
  ccall((:arb_get_ubound_arf, libarb), Nothing,
        (Ref{arf_struct}, Ref{ArbFieldElem}, Int), tarf, x, 64)

  bound = ZZRingElem()

  # round towards +oo
  ccall((:arf_get_fmpz, libarb), Nothing,
        (Ref{ZZRingElem}, Ref{arf_struct}, Cint), bound, tarf, 3)

  ccall((:arf_clear, libarb), Nothing, (Ref{arf_struct}, ), tarf)

  return bound
end

@doc raw"""
    lower_bound(x::ArbFieldElem, ::Type{ZZRingElem}) -> ZZRingElem

Returns an integer $b$ of type `ZZRingElem` such that $x \geq
b$. It is not guaranteed that $b$ is as tight as possible.
"""
function lower_bound(x::ArbFieldElem, ::Type{ZZRingElem})
  tarf = arf_struct(0, 0, 0, 0)

  ccall((:arf_init, libarb), Nothing, (Ref{arf_struct}, ), tarf)
  ccall((:arb_get_lbound_arf, libarb), Nothing,
        (Ref{arf_struct}, Ref{ArbFieldElem}, Int), tarf, x, 64)

  bound = ZZRingElem()

  # round towards +oo
  ccall((:arf_get_fmpz, libarb), Nothing,
        (Ref{ZZRingElem}, Ref{arf_struct}, Cint), bound, tarf, 2)

  ccall((:arf_clear, libarb), Nothing, (Ref{arf_struct}, ), tarf)

  return bound
end

################################################################################
#
#  Maximum
#
################################################################################

function _max(a::ArbFieldElem, b::ArbFieldElem)
  RR = parent(a)
  c = RR()
  ccall((:arb_max, libarb), Cvoid, (Ref{ArbFieldElem}, Ref{ArbFieldElem}, Ref{ArbFieldElem}, Int), c, a, b, precision(RR))
  return c
end

function _min(a::ArbFieldElem, b::ArbFieldElem)
  RR = parent(a)
  c = RR()
  ccall((:arb_min, libarb), Cvoid, (Ref{ArbFieldElem}, Ref{ArbFieldElem}, Ref{ArbFieldElem}, Int), c, a, b, precision(RR))
  return c
end
