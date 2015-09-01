export FactoredElem, FactoredElemMon

export transform

################################################################################
#
#  Multiplicative representation
#
################################################################################

# abstract nonsense

const FactoredElemMonDict = ObjectIdDict()

type FactoredElemMon{T <: RingElem} <: Ring
  base_ring::Ring  # for the base
  basis_conjugates_log::Dict{RingElem, Tuple{Int, Array{arb, 1}}}
  basis_conjugates::Dict{RingElem, Tuple{Int, Array{arb, 1}}}

  function FactoredElemMon(R::Ring)
    if haskey(FactoredElemMonDict, R)
      return FactoredElemMonDict[R]::FactoredElemMon
    else
      z = new()
      z.base_ring = R
      z.basis_conjugates_log = Dict{RingElem, Array{arb, 1}}()
      z.basis_conjugates = Dict{RingElem, Array{arb, 1}}()
      FactoredElemMonDict[R] = z
      return z
    end
  end
end

type FactoredElem{B}
  fac::Dict{B, fmpz}
  parent::FactoredElemMon

  function FactoredElem()
    z = new()
    z.fac = Dict{B, fmpz}()
    return z
  end
end

function call{T}(x::FactoredElemMon{T})
  z = FactoredElem{T}()
  z.parent = x
  return z
end
    
function FactoredElem{B}(base::Array{B, 1}, exp::Array{fmpz, 1})

  length(base) == 0 && error("Array must not be empty")

  length(base) != length(exp) && error("not the same length")

  z = FactoredElem{B}()

  for i in 1:length(base)
    if exp[i] == 0
      continue
    end
    z.fac[base[i]] = exp[i]
  end

  z.parent = FactoredElemMon{typeof(base[1])}(parent(base[1]))
  return z
end

parent(x::FactoredElem) = x.parent

base_ring(x::FactoredElemMon) = x.base_ring

base_ring(x::FactoredElem) = base_ring(parent(x))

base(x::FactoredElem) = keys(x.fac)

function deepcopy{B}(x::FactoredElem{B})
  z = FactoredElem{B}()
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

function show(io::IO, x::FactoredElemMon)
  print(io, "Factored elements over $(x.base_ring)")
end

function show(io::IO, x::FactoredElem)
  print(io, "Factored element with data\n$(x.fac)")
end

################################################################################
#
#  Exponentiation
#
################################################################################


function pow!{T <: Union{fmpz, Integer}}(z::FactoredElem, x::FactoredElem, y::T)
  z.fac = _deepcopy(x.fac)
  for a in base(x)
    # this should be inplac
    z.fac[a] = y*x.fac[a]
  end
end

function ^{T <: Union{fmpz, Integer}}(x::FactoredElem, y::T)
  z = parent(x)()
  z.fac = _deepcopy(x.fac)
  for a in base(x)
    # this should be inplac
    z.fac[a] = y*x.fac[a]
  end
  return z
end

################################################################################
#
#  Multiplication
#
################################################################################

function mul!{B}(z::FactoredElem{B}, x::FactoredElem{B}, y::FactoredElem{B})
  z.fac = _deepcopy(x.fac)
  for a in base(y)
    if haskey(x.fac, a)
      z.fac[a] = z.fac[a] + y.fac[a]
    else
      z.fac[a] = y.fac[a]
    end
  end
end

function *{B}(x::FactoredElem{B}, y::FactoredElem{B})
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

function div{B}(x::FactoredElem{B}, y::FactoredElem{B})
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

function transform{T}(x::Array{FactoredElem{T}, 1}, y::fmpz_mat)
  length(x) != rows(y) &&
              error("Length of array must be number of rows of matrix")

  z = Array(FactoredElem{T}, cols(y))

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

################################################################################
#
#  Evaluate
#
################################################################################

function evaluate{T}(x::FactoredElem{T})
  z = one(base_ring(x))

  for a in base(x)
    z = z*a^x.fac[a]
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
