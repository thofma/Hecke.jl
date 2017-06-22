export FacElem, FacElemMon, simplify, factor_coprime

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
doc"""
    FacElem{B}(base::Array{B, 1}, exp::Array{fmpz, 1}) -> FacElem{B}
> Returns the element $\prod b_i^{e_i}$, un-expanded.
"""
function FacElem{B}(base::Array{B, 1}, exp::Array{fmpz, 1})

  length(base) == 0 && error("Array must not be empty")

  length(base) != length(exp) && error("not the same length")

  z = FacElem{B, typeof(parent(base[1]))}()

  for i in 1:length(base)
    if exp[i] == 0
      continue
    end
    if haskey(z.fac, base[i])
      z.fac[base[i]] += exp[i]
    else
      z.fac[base[i]] = exp[i]
    end
  end

  z.parent = FacElemMon(parent(base[1]))
  return z
end

doc"""
    FacElem{B}(d::Dict{B, fmpz}) -> FacElem{B}
    FacElem{B}(d::Dict{B, Integer}) -> FacElem{B}
> Returns the element $\prod b^{d[p]}$, un-expanded.
"""
function FacElem{B}(d::Dict{B, fmpz})

  length(d) == 0 && error("Dictionary must not be empty")

  z = FacElem{B, typeof(parent(first(keys(d))))}()
  z.fac = d

  z.parent = FacElemMon(parent(first(keys(d))))
  return z
end

function FacElem{B, T <: Integer}(d::Dict{B, T})

  length(d) == 0 && error("Dictionary must not be empty")

  z = FacElem{B, typeof(parent(first(keys(d))))}()
  z.fac = Dict{B, fmpz}((k,fmpz(v)) for (k,v) = d) 

  z.parent = FacElemMon(parent(first(keys(d))))
  return z
end


parent(x::FacElem) = x.parent

base_ring(x::FacElemMon) = x.base_ring

base_ring(x::FacElem) = base_ring(parent(x))

base(x::FacElem) = keys(x.fac)

function Base.deepcopy_internal{B, S}(x::FacElem{B, S}, dict::ObjectIdDict)
  z = FacElem{B, S}()
  z.fac = Base.deepcopy_internal(x.fac, dict)
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
function inv!(x::FacElem)
  for a in base(x)
    x.fac[a] = -x.fac[a]
  end
end

function inv(x::FacElem)
  y = deepcopy(x)
  inv!(y)
  return y
end

################################################################################
#
#  Exponentiation
#
################################################################################

#needed for FacElem{fmpq/fmpz, fmpz}^pow...
elem_type(::Type{FlintRationalField}) = fmpq
elem_type(::Type{FlintIntegerRing}) = fmpz

function pow!{T <: Union{fmpz, Integer}}(z::FacElem, x::FacElem, y::T)
  z.fac = deepcopy(x.fac)
  for a in base(x)
    # this should be inplace
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

function evaluate(x::FacElem{NfMaxOrdIdl, NfMaxOrdIdlSet})
  x = simplify(x) # the other method won't work due to one()
  return prod([(p//1)^Int(k) for (p,k) = x.fac])
end

doc"""
***
  evaluate{T}(x::FacElem{T}) -> T

> Expands or evaluates the factored element, i.e. actually computes the
> value. 
> Does "square-and-multiply" on the exponent vectors.
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
        z *= k^Int(v)
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
    evaluate(x::FacElem{fmpq}) -> fmpq
    evaluate(x::FacElem{fmpz}) -> fmpz

> Expands or evaluates the factored element, i.e. actually computes the
> the element. 
> Works by first obtaining a simplified version of the power product
> into coprime base elements.
"""
function evaluate(x::FacElem{fmpq})
  return evaluate_naive(simplify(x))
end

function evaluate(x::FacElem{fmpz})
  return evaluate_naive(simplify(x))
end
doc"""
***
  simplify(x::FacElem{fmpq}) -> FacElem{fmpq}
  simplify(x::FacElem{fmpz}) -> FacElem{fmpz}

> Simplfies the factored element, i.e. arranges for the base to be coprime.
"""
function simplify(x::FacElem{fmpq})
  y = deepcopy(x)
  simplify!(y)
  return y
end

function simplify(x::FacElem{fmpz})
  y = deepcopy(x)
  simplify!(y)
  return y
end

function simplify!(x::FacElem{fmpq})
  if length(x.fac) <= 1
    return
  end
  cp = coprime_base(vcat([den(y) for y = base(x)], [num(y) for y=base(x)]))
  ev = Dict{fmpq, fmpz}()
  for p = cp
    if p == 1 || p == -1
      continue
    end
    v = fmpz(0)
    for b = base(x)
      v += valuation(b, abs(p))*x.fac[b]
    end
    if v != 0
      ev[fmpq(abs(p))] = v
    end
  end
  s = prod(map(b -> b < 0 && isodd(x.fac[b]) ? -1 : 1, base(x)))
  if s == -1
    ev[fmpq(-1)] = 1
  else
    if length(ev) == 0
      ev[fmpq(1)] = 0
    end
  end
  x.fac = ev
  nothing
end

function simplify!(x::FacElem{fmpz})
  if length(x.fac) <= 1
    return
  end
  cp = coprime_base(collect(base(x)))
  ev = Dict{fmpz, fmpz}()
  for p = cp
    if p == 1 || p == -1
      continue
    end
    v = fmpz(0)
    for b = base(x)
      v += valuation(b, abs(p))*x.fac[b]
    end
    if v < 0 
      throw(DomainError())
    end
    if v != 0
      ev[abs(p)] = v
    end
  end
  s = prod(map(b -> b < 0 && isodd(x.fac[b]) ? -1 : 1, base(x)))
  if s == -1
    ev[-1] = 1
  else
    if length(ev) == 0
      ev[fmpz(1)] = 0
    end
  end
  x.fac = ev
  nothing
end

doc"""
***
    isone(x::FacElem{fmpq}) -> Bool
    isone(x::FacElem{fmpz}) -> Bool
> Tests if $x$ represents $1$ without an evaluation.
"""
function isone(x::FacElem{fmpq})
  y = simplify(x)
  return all(iszero, values(y.fac))
end

function isone(x::FacElem{fmpz})
  y = simplify(x)
  return all(iszero, values(y.fac))
end


#TODO: expand the coprime stuff to automatically also get the exponents
function simplify(x::FacElem{NfMaxOrdIdl, NfMaxOrdIdlSet})
  z = deepcopy(x)
  simplify!(z)
  return z
end

function simplify!(x::FacElem{NfMaxOrdIdl, NfMaxOrdIdlSet})
  if length(x.fac) <= 1
    p = first(keys(x.fac))
    x.fac =  Dict(abs(p) => x.fac[p])
    return 
  end
  cp = coprime_base(collect(base(x)))
  ev = Dict{NfMaxOrdIdl, fmpz}()
  for p = cp
    if isone(p)
      continue
    end
    v = fmpz(0)
    for b = base(x)
      v += valuation(b, p)*x.fac[b]
    end
    if v != 0
      ev[p] = v
    end
  end
  x.fac = ev
end  

function factor_coprime(x::FacElem{NfMaxOrdIdl, NfMaxOrdIdlSet})
  x = deepcopy(x)
  simplify!(x)
  return Dict(p=>Int(v) for (p,v) = x.fac)
end

function factor_coprime(x::FacElem{fmpz})
  x = deepcopy(x)
  simplify!(x)
  d = Dict(abs(p) => Int(v) for (p,v) = x.fac)
  if haskey(d, fmpz(-1))
    delete!(d, fmpz(-1))
    return Fac(fmpz(-1), d)
  else
    return Fac(fmpz(1), d)
  end
end

doc"""
***
  evaluate_naive{T}(x::FacElem{T}) -> T

> Expands or evaluates the factored element, i.e. actually computes the
> value. Uses the obvious naive algorithm. Faster for input in finite rings.
"""
function evaluate_naive{T}(x::FacElem{T})
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

function ^(a::fmpz, k::fmpz)
  if a == 0
    if k == 0
      return fmpz(1)
    end
    return fmpz(0)
  end
 
  if a == 1
    return fmpz(1)
  end
  if a == -1
    if isodd(k)
      return fmpz(-1)
    else
      return fmpz(1)
    end
  end
  return a^Int(k)
end

function ^(a::fmpq, k::fmpz)
  if a == 0
    if k == 0
      return fmpq(1)
    end
    return fmpq(0)
  end
 
  if a == 1
    return fmpq(1)
  end
  if a == -1
    if isodd(k)
      return fmpq(-1)
    else
      return fmpq(1)
    end
  end
  return a^Int(k)
end



#################################################################################
doc"""
    max_exp(a::FacElem)
> Finds the largest exponent in the factored element $a$
"""
function max_exp(a::FacElem)
  return maximum(values(a.fac))
end

doc"""
    min_exp(a::FacElem)
> Finds the smallest exponent in the factored element $a$
"""
function min_exp(a::FacElem)
  return minimum(values(a.fac))
end

doc"""
    maxabs_exp(a::FacElem)
> Finds the largest exponent by absolute value the factored element $a$
"""
function maxabs_exp(a::FacElem)
  return maxabs(values(a.fac))
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
