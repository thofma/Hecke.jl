import Nemo.isone, Nemo.divexact, Base.copy

function gcd_into!(a::ZZRingElem, b::ZZRingElem, c::ZZRingElem)
  ccall((:fmpz_gcd, libflint), Nothing,
          (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), a, b, c)
  return a
end

function gcd_into!(a::T, b::T, c::T) where T <: Integer
  return gcd(b, c)::T
end

function mul_into!(a::T, b::T, c::T) where T
  return (b*c)::T
end

function mul_into!(a::ZZRingElem, b::ZZRingElem, c::ZZRingElem)
  mul!(a, b, c)
  return a
end

function copy_into!(a, b)
  return b
end

function copy_into!(a::MPolyRingElem, b::MPolyRingElem)
  return copy(b)
end

function copy_into!(a::ZZRingElem, b::ZZRingElem)
  ccall((:fmpz_set, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}), a, b)
  return a
end

function copy_into!(a::QQFieldElem, b::QQFieldElem)
  ccall((:fmpq_set, libflint), Nothing, (Ref{QQFieldElem}, Ref{QQFieldElem}), a, b)
  return a
end

#for larger lists much better than Bill's (Nemo's) prod function
# the built-in Julia is better than Bill's Nemo function anyway
"""
  Data structure for a product-tree evaluation, need only
    O(nbits(length)) storage in comparison to O(n) for the julia
  or flint version.

  See implementation of `my_prod` for usage.
"""
mutable struct ProdEnv{T}
  level :: Vector{Int}
  val   :: Vector{T}
  last  :: Int

  function ProdEnv{T}(n::Int) where {T}
    r = new{T}()
    m = nbits(n)
    r.level = Array{Int}(undef, m)
    r.val   = Array{T}(undef, m)
    r.last = 0
    for i=1:m
      r.val[i] = T()
    end
    return r
  end
end

function Base.push!(A::ProdEnv{T}, b::T) where T
  if A.last == 0
    A.level[1] = 1
    A.val[1] = copy_into!(A.val[1], b)
    A.last = 1
    return
  end
  if A.level[A.last] > 1
    A.last += 1
    A.level[A.last] = 1
    A.val[A.last] = copy_into!(A.val[A.last], b)
    return
  end

  lev = 1
  while A.last > 0 && A.level[A.last] <= lev
    b = mul_into!(A.val[A.last], A.val[A.last], b)
    lev += A.level[A.last]
    A.last -= 1
  end
  A.last += 1
  A.level[A.last] = lev
  A.val[A.last] = b
  return
end

function finish(A::ProdEnv)
  b = A.val[A.last]
  while A.last >1
    A.last -= 1
    b = mul_into!(b, A.val[A.last], b)
  end
  return b
end

function my_prod(a::AbstractVector{T}) where T
  b = ProdEnv{T}(length(a))
  for x in a
    push!(b, x)
  end
  return finish(b)
end

"""
 A specialized version of the ProdEnv for 2x2 matrices representing
 polynomials

 f = sum a_i x^i

 can be computed via

    x   0      x   0    ...    x   0  =  x^(n+1   0)
    a_0 1      a_1 1           a_n 1     f(x)     1

 clearly, the second col is not necessary, and (slightly more complicated)
 the only powers if x that are used in the prod tree are x^(2^i)
 for 0<= i <= nbits(n)
"""
mutable struct EvalEnv{T}
  level :: Vector{Int}
  pow   :: Vector{T}
  val   :: Vector{T}
  last  :: Int

  function EvalEnv{T}(x::T, n::Int) where {T}
    r = new{T}()
    m = nbits(n)
    r.level = Array{Int}(undef, m)
    r.val   = Array{T}(undef, m)
    r.pow   = Array{T}(undef, m+1) #as a temp. var.
    r.last = 0
    r.pow[1] = x
    for i=1:m
      r.val[i] = parent(x)()
    end
    for i=2:m
      r.pow[i] = r.pow[i-1]^2
    end
    r.pow[end] = parent(x)()
    return r
  end
end

function Base.push!(A::EvalEnv{T}, b::T) where T
  if A.last == 0
    A.level[1] = 1
    A.val[1] = copy_into!(A.val[1], b)
    A.last = 1
    return
  end
  if A.level[A.last] > 1
    A.last += 1
    A.level[A.last] = 1
    A.val[A.last] = copy_into!(A.val[A.last], b)
    return
  end

  lev = 1
  #= b enters at level 1:
     x
     b 1
  its multiplied by level 1:
     x
     c 1
  to get
     x^2
     bx+c  1
  this is multiplied by level 2
     x^2
     d 1
  to get
     x^4
     bx^3+cx^2+d 1
  ...
  =#
  b = copy_into!(A.pow[end], b)
  while A.last > 0 && A.level[A.last] <= lev
#    b = b*A.pow[lev] + A.val[A.last]
    b = mul!(b, b, A.pow[lev])
    b = add!(b, b, A.val[A.last])
    lev += 1
    A.last -= 1
  end
  A.last += 1
  A.level[A.last] = lev
  A.val[A.last] = copy_into!(A.val[A.last], b)
  return
end

function finish(A::EvalEnv)
  lst = A.last
  b = A.val[lst]
  while lst >1
    lst -= 1
    lev = A.level[lst]
    b = mul!(b, b, A.pow[lev])
    b = add!(b, b, A.val[lst])
  end
  return b
end

function _my_eval(a, x::T) where T
  b = EvalEnv{T}(x, length(a))
  for x in a
    push!(b, x)
  end
  return finish(b)
end
my_eval(a::AbstractVector{T}, x::T) where {T} = _my_eval(a, x)
function my_eval(f::PolyRingElem{T}, x::T) where T
  return _my_eval(coefficients(f), x)
end

#coprime base Bach/ Schallit/ ???

function pair_bach(a::E, b::E) where E
  if is_unit(a)
    if is_unit(b)
      return Vector{E}()
    else
      return [b]
    end
  end
  if is_unit(b)
    return [a]
  end

  n = [a, b]
  i = 1
  while i < length(n)
    g = gcd(n[i], n[i+1])
    if isone(g)
      i += 1
    else
      n[i] = divexact!(n[i], g)
      n[i+1] = divexact!(n[i+1], g)
      insert!(n, i+1, g)
      if is_unit(n[i+2])
        deleteat!(n, i+2)
      end
      if is_unit(n[i])
        deleteat!(n, i)
      end
    end
  end

  return n
end



function augment_bach(S::Vector{E}, m::E) where E
  T = Vector{E}()
  i = 1
  while i <= length(S) && !is_unit(m)
    if !is_unit(S[i])
      Ts = pair_bach(m, S[i])
      T = vcat(T, view(Ts, 2:length(Ts)))
      m = Ts[1]
    end
    i += 1
  end
  if i <= length(S)
    T = vcat(T, view(S, i:length(S)))
  end
  if !is_unit(m)
    push!(T, m)
  end
  return T
end


function coprime_base_bach(a::Vector{E}) where E #T need to support GCDs
  if length(a) < 2
    return a
  end

  T = pair_bach(a[1], a[2])
  j = 3
  while j <= length(a)
    T = augment_bach(T, a[j])
    j += 1
  end
  return T
end

# Bernstein: coprime bases
#
#Note: Bernstein needs bigints, either Integer or ZZRingElem
#      well, polys are also OK, small integers are not.

# could/ should be optimsed using divexact! and gcd_into!
# probably should also be combined with ppio somewhere

function ppgle(a::E, b::E) where E
  n = gcd(a,b)
  r = divexact(a, n)
  m = n
  g = gcd(r, n)
  while !isone(g)
    r *= g
    n = divexact(n, g)
    g = gcd(r, n)
  end
  return m, r, n
end

function pair_bernstein(a::E, b::E) where E
  T = Vector{E}()
  if is_unit(b)
    if is_unit(a)
      return T
    else
      return push!(T, a)
    end
  end
  if is_unit(a)
    return push!(T, b)
  end

  a,r = ppio(a,b)
  if !is_unit(r)
    push!(T, r)
  end
  g,h,c = ppgle(a, b)
  c0 = c
  r = c0
  k = 1
  while !isone(h)
    g,h,c = ppgle(h, g^2)
    d = gcd(c, b)
    if isone(d)
      push!(T, c)
      continue
    end
    r *= d
    n = d^(2^(k-1))
    T = vcat(T, pair_bernstein(divexact(c, n), d))
    k += 1
  end
  T = vcat(T, pair_bernstein(divexact(b, r), c0))
  return T
end

function split_bernstein(a::T, P::Hecke.node{T}) where T
  b = Hecke.ppio(a, P.content)[1]
  if !isdefined(P, :left)
    if !isdefined(P, :right)
      return [(P.content, b)]
    else
      return split_bernstein(b, P.right)
    end
  else
    if !isdefined(P, :right)
      return split_bernstein(b, P.left)
    else
      return vcat(split_bernstein(b, P.left), split_bernstein(b, P.right))
    end
  end
end

function split_bernstein(a::T, P::Vector{T}) where T
  if length(P) == 0
    return P
  end
  F = FactorBase(P, check = false)
  b = Hecke.ppio(a, F.prod)[1]
  if length(P)==1
    return [(P[1], b)]
  end
  return vcat(split_bernstein(b, F.ptree.left), split_bernstein(b, F.ptree.right))
end

function augment_bernstein(P::Vector{E}, b::E) where E
  T = Vector{E}()
  if length(P) == 0
    if is_unit(b)
      return T
    else
      return push!(T, b)
    end
  end
  F = FactorBase(P, check = false)
  a,r = Hecke.ppio(b, F.prod)
  if ! is_unit(r)
    push!(T, r)
  end
  S = split_bernstein(a, F.ptree)
  for X in S
    T = vcat(T, pair_bach(X[1], X[2]))
  end
  return T
end

function merge_bernstein(P::Vector{E}, Q::Vector{E}) where E
  m = length(Q)
  b = nbits(m)
  S = P
  i = 0
  while i<=b
    R = prod(view(Q, findall(x -> x & (2^i) ==0, 1:length(Q))))
    T = augment_bernstein(S, R)
    R = prod(view(Q, findall(x -> x & (2^i) !=0, 1:length(Q))))
    S = augment_bernstein(T, R)
    i += 1
  end
  return S
end


function coprime_base_bernstein(S::Vector{E}) where E
  if length(S)<2
    return S
  end
  P1 = coprime_base_bernstein([S[i] for i=1:div(length(S), 2)])
  P2 = coprime_base_bernstein([S[i] for i=(div(length(S), 2)+1):length(S)])
  return merge_bernstein(P1, P2)
end

function augment_steel(S::Vector{E}, a::E, start::Int = 1) where E
  i = start
  if is_unit(a)
    return S
  end

  g = a
  new = true

  while i<=length(S) && !isone(a)
    if new
      g = gcd(S[i], a)
      new = false
    else
      g = gcd_into!(g, S[i], a)
    end
    if is_unit(g)
      i += 1
      continue
    end
    si = divexact(S[i], g)
    a = divexact(a, g)
    if is_unit(si) # g = S[i] and S[i] | a
      continue
    end
    S[i] = si
    if is_unit(a) # g = a and a | S[i]
      a = copy(g)
      continue
    end
    augment_steel(S, copy(g), i)
    continue
  end
  if !is_unit(a)
    push!(S, a)
  end

  return S;
end

function coprime_base_steel(S::Vector{E}) where E
  @assert !isempty(S)
  T = Array{E}(undef, 1)
  T[1] = S[1]
  for i=2:length(S)
    augment_steel(T, S[i])
  end
  return T
end

##implemented
# Bernstein: asymptotically fastest, linear in the total input size
#   pointless for small ints as it requires intermediate numbers to be
#   huge
# Bach/Shallit/???: not too bad, source Epure's Masters thesis
#   can operate on Int types as no intermediate is larger than the input
# Steel: a misnomer: similar to Magma, basically implements a memory
#   optimised version of Bach
#   faster than Magma on
# > I := [Random(1, 10000) * Random(1, 10000) : x in [1..10000]];
# > time c := CoprimeBasis(I);
# julia> I = [ZZRingElem(rand(1:10000))*rand(1:10000) for i in 1:10000];
#
# experimentally, unless the input is enormous, Steel wins
# on smallish input Bach is better than Bernstein, on larger this
# changes
#
# needs
# isone, gcd_into!, divexact!, copy
# (some more for Bernstein: FactorBase, gcd, divexact)

@doc raw"""
    coprime_base{E}(S::Vector{E}) -> Vector{E}

Returns a coprime base for $S$, i.e. the resulting array contains pairwise coprime objects that multiplicatively generate the same set as the input array.
"""
coprime_base(x) = coprime_base_steel(x)

@doc raw"""
    coprime_base_insert{E}(S::Vector{E}, a::E) -> Vector{E}

Given a coprime array $S$, insert a new element, i.e. find a coprime base for `push(S, a)`.
"""
coprime_base_insert(S, a) = augment_steel(S, a)
