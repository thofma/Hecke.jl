export abs_upper_bound

function _arb_get_fmpq(x::arb)
  mid = ccall((:arb_mid_ptr, :libarb), Ptr{arf_struct}, (Ptr{arb}, ), &x)
  e = fmpz()
  m = fmpz()
  b = ccall((:arf_get_fmpz_2exp, :libarb), Cint, (Ptr{fmpz}, Ptr{fmpz}, Ptr{arf_struct}), &m, &e, mid)
  @assert abs(e) < typemax(Int)
  ee = Int(e)
  return fmpq(m, fmpz(1))*fmpq(2)^(ee)
end

function mul2exp!(z::arb, x::arb, y::Int)
  ccall((:arb_mul_2exp_si, :libarb), Void, (Ptr{arb}, Ptr{arb}, Int), &z, &x, y)
  return nothing
end

function muleq!(z::arb, x::arb, y::arb)
  q = max(bits(x), bits(y))
  ccall((:arb_mul, :libarb), Void, (Ptr{arb}, Ptr{arb}, Ptr{arb}, Int), &z, &x, &y, q)
  return nothing
end

function muleq!(z::arb, x::arb, y::fmpz)
  ccall((:arb_mul_fmpz, :libarb), Void, (Ptr{arb}, Ptr{arb}, Ptr{fmpz}, Int), &z, &x, &y, bits(x))
  return nothing
end

function addmul!(z::arb, x::arb, y::fmpz)
  q = max(bits(z), bits(x))
  ccall((:arb_addmul_fmpz, :libarb), Void, (Ptr{arb}, Ptr{arb}, Ptr{fmpz}, Int), &z, &x, &y, q)
  return nothing
end

function abs!(z::arb, x::arb)
  ccall((:arb_abs, :libarb), Void, (Ptr{arb}, Ptr{arb}, Int), &z, &x, parent(x).prec)
  return nothing
end

function abs!(z::arb, x::acb)
  ccall((:acb_abs, :libarb), Void, (Ptr{arb}, Ptr{acb}, Int), &z, &x, parent(x).prec)
  return nothing
end

function log!(z::arb, x::arb)
  ccall((:arb_log, :libarb), Void, (Ptr{arb}, Ptr{arb}, Int), &z, &x, parent(x).prec)
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

doc"""
***
    abs_upper_bound(x::arb, ::Type{fmpz}) -> fmpz

Returns a positive integer $b$ of type `fmpz` such that $\lvert x \rvert \leq
b$. It is not guarenteed that $b$ is as tight as possible.
"""
function abs_upper_bound(x::arb, ::Type{fmpz})
  tarf = arf_struct(0, 0, 0, 0)

  ccall((:arf_init, :libarb), Void, (Ptr{arf_struct}, ), &tarf)
  ccall((:arb_get_abs_ubound_arf, :libarb), Void,
        (Ptr{arf_struct}, Ptr{arb}, Int), &tarf, &x, 64)

  bound = fmpz()

  # round towards +oo
  ccall((:arf_get_fmpz, :libarb), Void,
        (Ptr{fmpz}, Ptr{arf_struct}, Cint), &bound, &tarf, 3)

  ccall((:arf_clear, :libarb), Void, (Ptr{arf_struct}, ), &tarf)

  return bound
end

doc"""
***
    abs_upper_bound(x::arb, ::Type{Float64}) -> Float64

Returns a positive double $b$ such that $\lvert x \rvert \leq b$. It is not
guarenteed that $b$ is as tight as possible.
"""
function abs_upper_bound(x::arb, ::Type{Float64})
  tarf = arf_struct(0, 0, 0, 0)

  ccall((:arf_init, :libarb), Void, (Ptr{arf_struct}, ), &tarf)
  ccall((:arb_get_abs_ubound_arf, :libarb), Void,
        (Ptr{arf_struct}, Ptr{arb}, Int),
          &tarf, &x, 64)

  # round towards -oo
  bound = ccall((:arf_get_d, :libarb), Cdouble,
                (Ptr{arf_struct}, Cint), &tarf, 3)

  ccall((:arf_clear, :libarb), Void, (Ptr{arf_struct}, ), &tarf)

  return bound
end

doc"""
***
    upper_bound(x::arb, ::Type{fmpz}) -> fmpz

Returns an integer $b$ of type `fmpz` such that $x \leq
b$. It is not guarenteed that $b$ is as tight as possible.
"""
function upper_bound(x::arb, ::Type{fmpz})
  tarf = arf_struct(0, 0, 0, 0)

  ccall((:arf_init, :libarb), Void, (Ptr{arf_struct}, ), &tarf)
  ccall((:arb_get_ubound_arf, :libarb), Void,
        (Ptr{arf_struct}, Ptr{arb}, Int), &tarf, &x, 64)

  bound = fmpz()

  # round towards +oo
  ccall((:arf_get_fmpz, :libarb), Void,
        (Ptr{fmpz}, Ptr{arf_struct}, Cint), &bound, &tarf, 3)

  ccall((:arf_clear, :libarb), Void, (Ptr{arf_struct}, ), &tarf)

  return bound
end

doc"""
***
    lower_bound(x::arb, ::Type{fmpz}) -> fmpz

Returns an integer $b$ of type `fmpz` such that $x \geq
b$. It is not guarenteed that $b$ is as tight as possible.
"""
function lower_bound(x::arb, ::Type{fmpz})
  tarf = arf_struct(0, 0, 0, 0)

  ccall((:arf_init, :libarb), Void, (Ptr{arf_struct}, ), &tarf)
  ccall((:arb_get_lbound_arf, :libarb), Void,
        (Ptr{arf_struct}, Ptr{arb}, Int), &tarf, &x, 64)

  bound = fmpz()

  # round towards +oo
  ccall((:arf_get_fmpz, :libarb), Void,
        (Ptr{fmpz}, Ptr{arf_struct}, Cint), &bound, &tarf, 2)

  ccall((:arf_clear, :libarb), Void, (Ptr{arf_struct}, ), &tarf)

  return bound
end


