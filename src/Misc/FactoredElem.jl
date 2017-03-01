export FacElem, FacElemMon

export transform

################################################################################
#
#  Multiplicative representation
#
################################################################################

# abstract nonsense

const FacElemMonDict = ObjectIdDict()

function (x::FacElemMon{S}){S}()
  z = FacElem{elem_type(S), S}()
  z.fac = Dict{elem_type(S), fmpz}()
  z.parent = x
  return z
end
    
function FacElem{B}(base::Array{B, 1}, exp::Array{fmpz, 1})

  length(base) == 0 && error("Array must not be empty")

  length(base) != length(exp) && error("not the same length")

  z = FacElem{B, typeof(parent(base[1]))}()

  for i in 1:length(base)
    if exp[i] == 0
      continue
    end
    z.fac[base[i]] = exp[i]
  end

  z.parent = FacElemMon(parent(base[1]))
  return z
end

parent(x::FacElem) = x.parent

base_ring(x::FacElemMon) = x.base_ring

base_ring(x::FacElem) = base_ring(parent(x))

base(x::FacElem) = keys(x.fac)

function Base.deepcopy_internal{B, S}(x::FacElem{B, S}, dict::ObjectIdDict)
  z = FacElem{B, S}()
  z.fac = deepcopy(x.fac)
  if isdefined(x, :parent)
    z.parent = x.parent
  end
  return z
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, x::FacElemMon)
  print(io, "Factored elements over $(x.base_ring)")
end

function show(io::IO, x::FacElem)
  print(io, "Factored element with data\n$(x.fac)")
end

################################################################################
#
#  Inverse
#
################################################################################

function inv(x::FacElem{nf_elem, AnticNumberField})
  y = deepcopy(x)
  for a in base(y)
    y.fac[a] = -y.fac[a]
  end
  return y
end

################################################################################
#
#  Exponentiation
#
################################################################################

function pow!{T <: Union{fmpz, Integer}}(z::FacElem, x::FacElem, y::T)
  z.fac = deepcopy(x.fac)
  for a in base(x)
    # this should be inplac
    z.fac[a] = y*x.fac[a]
  end
end

# ^(x::FacElem, y::Union{fmpz, Integer}) is ambiguous
for T in [:Integer, fmpz]
  @eval begin
    function ^(x::FacElem, y::($T))
      z = parent(x)()
      if y == 0
        return z
      end
      if y == 1
        return deepcopy(x)
      else
        z.fac = deepcopy(x.fac)
        for a in base(x)
          # this should be inplac
          z.fac[a] = y*x.fac[a]
        end
        return z
      end
    end
  end
end

################################################################################
#
#  Multiplication
#
################################################################################

function mul!{B, S}(z::FacElem{B, S}, x::FacElem{B, S}, y::FacElem{B, S})
  z.fac = deepcopy(x.fac)
  for a in base(y)
    if haskey(x.fac, a)
      z.fac[a] = z.fac[a] + y.fac[a]
    else
      z.fac[a] = y.fac[a]
    end
  end
end

function *{B, S}(x::FacElem{B, S}, y::FacElem{B, S})
  if length(x.fac) == 0
    return deepcopy(y)
  end

  if length(y.fac) == 0
    return deepcopy(x)
  end

  z = deepcopy(x)
  for a in base(y)
    if haskey(x.fac, a)
      z.fac[a] = z.fac[a] + y.fac[a]
    else
      z.fac[a] = y.fac[a]
    end
  end
  return z
end

function *{B}(x::FacElem{B}, y::B)
  z = deepcopy(x)
  if haskey(x.fac, y)
    z.fac[y] = z.fac[y] + 1
  else
    z.fac[y] = 1
  end
  return z
end

function div{B}(x::FacElem{B}, y::FacElem{B})
  z = deepcopy(x)
  for a in base(y)
    if haskey(x.fac, a)
      z.fac[a] = z.fac[a] - y.fac[a]
    else
      z.fac[a] = -y.fac[a]
    end
  end
  return z
end

################################################################################
#
#  Apply transformation
#
################################################################################

# return (x1,...,xr)*y
function _transform{T, S}(x::Array{FacElem{T, S}, 1}, y::fmpz_mat)
  length(x) != rows(y) &&
              error("Length of array must be number of rows of matrix")

  z = Array{FacElem{T, S}}(cols(y))

  t = parent(x[1])()

  for i in 1:cols(y)
    z[i] = x[1]^y[1,i]
    for j in 2:rows(y)
      if y[j, i] == 0
        continue
      end
      pow!(t, x[j], y[j, i])
      mul!(z[i], z[i], t)
    end
  end
  return z
end

function transform{S, T}(x::Array{FacElem{S, T}, 1}, y::fmpz_mat)
  return _transform(x, y)
end

function transform_left!{S, T}(x::Array{FacElem{S, T}, 1}, y::TrafoSwap{fmpz})
  x[y.i], x[y.j] = x[y.j], x[y.i]
  nothing
end

function transform_left!{S, T}(x::Array{FacElem{S, T}, 1}, y::TrafoAddScaled{fmpz})
  x[y.j] = x[y.j] * x[y.i]^y.s
  nothing
end

function transform_left!{S, T, R}(x::Array{FacElem{S, T}, 1}, y::TrafoPartialDense{R})
  z = view(deepcopy(x), y.rows)
  xx = view(x, y.rows)
  for i in 1:rows(y.U)
    xx[i] = z[1]^Int(y.U[i, 1])
    for j in 2:cols(y.U)
      xx[i] *= z[j]^Int(y.U[i, j])
    end
  end
end

function transform_left!{S, T}(x::Array{T, 1}, t::TrafoDeleteZero{S})
  # move ith position to the back
  for j in t.i:length(x)-1
    r = x[j]
    x[j] = x[j + 1]
    x[j + 1] = r
  end
end

function transform_left!{S, T, R}(x::Array{FacElem{S, T}, 1}, y::TrafoParaAddScaled{R})
  # [ Ri; Rj] <- [a b; c d]* [ Ri; Rj ]
  ri = deepcopy(x[y.i])
  rj = deepcopy(x[y.j])
  x[y.i] = ri^y.a * rj^y.b
  x[y.j] = ri^y.c * rj^y.d
end

################################################################################
#
#  Evaluate
#
################################################################################

doc"""
***
  evaluate{T}(x::FacElem{T}) -> T

> Expands or evaluates the factored element, i.e. actually computes the
> value. 
"""
function evaluate{T}(x::FacElem{T})
  function ev(d)#d::Dict{T, fmpz})
    z = one(base_ring(x))
    if length(d)==0
      return z
    elseif length(d)==1
      x = first(d)
      return x[1]^x[2]
    end
    b = similar(d)
    for (k,v) in d
      if v>-10 && v<10
        z *= k^v
      else
        r = isodd(v) ? 1 :0
        vv = div(v-r, 2)
        if vv!=0
          b[k] = vv
        end
        if r!=0
          z*= k
        end
      end
    end
    return ev(b)^2*z
  end

  return ev(x.fac)
end

doc"""
***
  naive_evaluate{T}(x::FacElem{T}) -> T

> Expands or evaluates the factored element, i.e. actually computes the
> value. Uses the obvious naive algorithm. Faster for input in finite rings.
"""
function naive_evaluate{T}(x::FacElem{T})
  z = one(base_ring(x))
  d = x.fac
  if length(d)==0
    return z
  end
  for (k,v) in d
    z *= k^v
  end
  return z
end


#################################################################################
##
##  Auxillary deep copy functions
##
#################################################################################
#
#function _deepcopy{K, V}(x::Dict{K, V})
#  z = typeof(x)()
#  for a in keys(x)
#    z[a] = deepcopy(x[a])
#  end
#  return z
#end

################################################################################
#
#  Parent object overloading
#
################################################################################

function (F::FacElemMon{T}){T}(a::T)
  z = F()
  z.fac[a] = fmpz(1)
  return z
end
