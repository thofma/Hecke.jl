export FacElem, FacElemMon

export transform

################################################################################
#
#  Multiplicative representation
#
################################################################################

# abstract nonsense

const FacElemMonDict = ObjectIdDict()

function call{T}(x::FacElemMon{T})
  z = FacElem{T}()
  z.parent = x
  return z
end
    
function FacElem{B}(base::Array{B, 1}, exp::Array{fmpz, 1})

  length(base) == 0 && error("Array must not be empty")

  length(base) != length(exp) && error("not the same length")

  z = FacElem{B}()

  for i in 1:length(base)
    if exp[i] == 0
      continue
    end
    z.fac[base[i]] = exp[i]
  end

  z.parent = FacElemMon{typeof(base[1])}(parent(base[1]))
  return z
end

parent(x::FacElem) = x.parent

base_ring(x::FacElemMon) = x.base_ring

base_ring(x::FacElem) = base_ring(parent(x))

base(x::FacElem) = keys(x.fac)

function deepcopy{B}(x::FacElem{B})
  z = FacElem{B}()
  z.fac = _deepcopy(x.fac)
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

function inv(x::FacElem{nf_elem})
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
  z.fac = _deepcopy(x.fac)
  for a in base(x)
    # this should be inplac
    z.fac[a] = y*x.fac[a]
  end
end

function ^(x::FacElem, y::fmpz)
  z = parent(x)()
  if y == 0
    return z
  else
    z.fac = _deepcopy(x.fac)
    for a in base(x)
      # this should be inplac
      z.fac[a] = y*x.fac[a]
    end
    return z
  end
end

^(x::FacElem, y::Integer) = ^(x, fmpz(y))

################################################################################
#
#  Multiplication
#
################################################################################

function mul!{B}(z::FacElem{B}, x::FacElem{B}, y::FacElem{B})
  z.fac = _deepcopy(x.fac)
  for a in base(y)
    if haskey(x.fac, a)
      z.fac[a] = z.fac[a] + y.fac[a]
    else
      z.fac[a] = y.fac[a]
    end
  end
end

function *{B}(x::FacElem{B}, y::FacElem{B})
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

function _transform{T}(x::Array{FacElem{T}, 1}, y::fmpz_mat)
  length(x) != rows(y) &&
              error("Length of array must be number of rows of matrix")

  z = Array(FacElem{T}, cols(y))

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

function transform{T}(x::Array{FacElem{T}, 1}, y::fmpz_mat)
  return _transform(x, y)
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


################################################################################
#
#  Auxillary deep copy functions
#
################################################################################

function _deepcopy{K, V}(x::Dict{K, V})
  z = typeof(x)()
  for a in keys(x)
    z[a] = deepcopy(x[a])
  end
  return z
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function call{T}(F::FacElemMon{T}, a::T)
  z = F()
  z.fac[a] = fmpz(1)
  return z
end
