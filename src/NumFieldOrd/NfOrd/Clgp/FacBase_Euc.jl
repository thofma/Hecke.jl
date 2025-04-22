################################################################################
#
#  Factor base over (Euclidean) Rings
#
################################################################################

# Note that T must admit gcd's and base must consist of elements x for which
# valuation(_, x) is defined.
# works (at least) for ZZRingElem and zzModPolyRingElem, so it can be used for the
# smoothness test

function _compose(a::node{T}, b::node{T}, check = false) where T
  if check && !isone(gcd(a.content, b.content))
    error("input not coprime")
  end
  return node{T}(a.content * b.content, a, b)
end

# assume that the set or array consists of pairwise coprime elements
function FactorBase(x::Union{Set{T}, AbstractVector{T}}; check::Bool = true) where T
  if length(x)==0
    z = FactorBase{T}(T(1), x)
    return z
  end
  ax = [ node{T}(p) for p in x]
  while length(ax) > 1
    bx = [ _compose(ax[2*i-1], ax[2*i], check) for i=1:div(length(ax), 2)]
    if isodd(length(ax))
      push!(bx, ax[end])
    end
    ax = bx
  end
  z = FactorBase{T}(ax[1].content, x)
  z.ptree = ax[1]
  return z
end

function show(io::IO, B::FactorBase{T}) where T
  print(io, "Factor base with \n$(B.base) and type $T")
end

function ring(B::FactorBase)
  return parent(B.prod)
end

function is_smooth(c::FactorBase{T}, a::T) where T
  @assert a != 0
  g = gcd(c.prod, a)
  while !isone(g)
    a = divexact(a, g)
    g = gcd(g, a)
  end
  return is_unit(a)
end

function is_smooth!(c::FactorBase{ZZRingElem}, a::ZZRingElem)
  @assert a != 0
  g = gcd(c.prod, a)
  if isone(g)
    return is_unit(a), a
  end
  b = copy(a)
  while !isone(g)
    divexact!(b, b, g)
    gcd!(g, g, b)
  end
  return is_unit(b), b
end


function is_leaf(a::node{T}) where T
  return !(isdefined(a, :left) || isdefined(a, :right))
end

function _split(c::node{T}, a::T) where T
  if is_leaf(c)
    return [gcd(a, c.content)]
  end
  if isdefined(c, :left)
    l = gcd(a, c.left.content)
    if l != 1
      ls = _split(c.left, l)
    else
      ls = Vector{T}()
    end
  else
    ls = Vector{T}()
  end
  if isdefined(c, :right)
    r = gcd(a, c.right.content)
    if r != 1
      rs = _split(c.right, r)
    else
      rs = Vector{T}()
    end
  else
    rs = Vector{T}()
  end
  return vcat(ls, rs)
end

function factor(c::FactorBase{T}, a::T, do_error::Bool = true) where T
  @assert a != 0
  f = Dict{T, Int}()
  is_unit(a) && return f
  lp = _split(c.ptree, a)
  for i in lp
    if mod(a, i)==0  ## combine: use divmod and do val of rest
                     ## to save a division
      v = remove(a, i)
      f[i] = v[1]
      a = v[2]
      if is_unit(a)
        break
      end
    end
  end
  @assert (!do_error || a==1 || a==-1)
  return f
end

function factor(c::FactorBase{ZZRingElem}, a::QQFieldElem)
  @assert a != 0
  a = deepcopy(a)
  f = Dict{ZZRingElem, Int}()
  n = abs(numerator(a))
  d = denominator(a)
  lp = _split(c.ptree, n*d)
  for i in lp
    v = remove!(a, i)
    if isdefined(f, :i)
      f[i] += v
    else
      f[i] = v
    end
    if isone(a)
      break
    end
  end
  @hassert :ClassGroup 1 isone(a)
  return f
end

