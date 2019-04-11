import Nemo.isone, Nemo.divexact, Base.copy
export divexact!, gcd_into!, coprime_base, coprime_base_insert

function divexact!(a::fmpz, b::fmpz)
  ccall((:fmpz_divexact, :libflint), Nothing, 
          (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), a, a, b)
  return a
end

function gcd_into!(a::fmpz, b::fmpz, c::fmpz)
  ccall((:fmpz_gcd, :libflint), Nothing, 
          (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), a, b, c)
  return a
end

function gcd_into!(a::T, b::T, c::T) where T <: Integer
  return gcd(b, c)::T
end

function mul_into!(a::T, b::T, c::T) where T
  return (b*c)::T
end

function mul_into!(a::fmpz, b::fmpz, c::fmpz)
  mul!(a, b, c)
  return a
end

function copy(a::fmpz) 
  return deepcopy(a)
end

function copy_into!(a, b)
  return b
end

function copy_into!(a::fmpz, b::fmpz)
  ccall((:fmpz_set, :libflint), Nothing, (Ref{fmpz}, Ref{fmpz}), a, b)
  return a
end

#for larger lists much better than Bill's (Nemo's) prod function
# the build-in Julia is better than Bill's Nemo function anyway

mutable struct ProdEnv{T}
  level :: Array{Int, 1}
  val   :: Array{T, 1}
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

function prod_mul!(A::ProdEnv{T}, b::T) where T
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

function prod_end(A::ProdEnv)
  b = A.val[A.last]
  while A.last >1
    A.last -= 1
    b = mul_into!(b, b, A.val[A.last])
  end
  return b
end

function my_prod(a::AbstractArray{T, 1}) where T 
  if length(a) <100
    return prod(a)
  end

  b = ProdEnv{T}(length(a))
  for x in a
    prod_mul!(b, x)
  end
  return prod_end(b)
end

#coprime base Bach/ Schallit/ ???

function pair_bach(a::E, b::E) where E
  if isunit(a)
    if isunit(b)
      return Vector{E}()
    else
      return [b]
    end
  end
  if isunit(b)
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
      if isunit(n[i+2])
        deleteat!(n, i+2)
      end
      if isunit(n[i])
        deleteat!(n, i)
      end
    end
  end

  return n
end

function augment_bach(S::Array{E, 1}, m::E) where E
  T = Vector{E}()
  i = 1
  while i <= length(S) && !isunit(m)
    if !isunit(S[i])
      Ts = pair_bach(m, S[i])
      T = vcat(T, view(Ts, 2:length(Ts)))
      m = Ts[1]
    end
    i += 1
  end
  if i <= length(S)
    T = vcat(T, view(S, i:length(S)))
  end
  if !isunit(m) 
    push!(T, m)
  end
  return T
end


function coprime_base_bach(a::Array{E, 1}) where E #T need to support GCDs
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
#Note: Bernstein needs bigints, either Integer or fmpz 
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
  if isunit(b)
    if isunit(a)
      return T
    else
      return push!(T, a)
    end
  end
  if isunit(a)
    return push!(T, b)
  end

  a,r = ppio(a,b)
  if !isunit(r)
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

function split_bernstein(a::T, P::Array{T, 1}) where T
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

function augment_bernstein(P::Array{E, 1}, b::E) where E
  T = Vector{E}()
  if length(P) == 0
    if isunit(b)
      return T
    else
      return push!(T, b)
    end
  end
  F = FactorBase(P, check = false)
  a,r = Hecke.ppio(b, F.prod)
  if ! isunit(r)
    push!(T, r)
  end
  S = split_bernstein(a, F.ptree)
  for X in S 
    T = vcat(T, pair_bach(X[1], X[2]))
  end
  return T
end

function merge_bernstein(P::Array{E, 1}, Q::Array{E, 1}) where E
  m = length(Q)
  b = nbits(m)
  S = P
  i = 0
  while i<=b
    R = prod(view(Q, find(x -> x & (2^i) ==0, 1:length(Q))))
    T = augment_bernstein(S, R)
    R = prod(view(Q, find(x -> x & (2^i) !=0, 1:length(Q))))
    S = augment_bernstein(T, R)
    i += 1
  end
  return S
end


function coprime_base_bernstein(S::Array{E, 1}) where E
  if length(S)<2
    return S
  end
  P1 = coprime_base_bernstein([S[i] for i=1:div(length(S), 2)])
  P2 = coprime_base_bernstein([S[i] for i=(div(length(S), 2)+1):length(S)])
  return merge_bernstein(P1, P2)
end

function augment_steel(S::Array{E, 1}, a::E, start::Int = 1) where E
  i = start
  if isunit(a)
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
    if isunit(g)
      i += 1
      continue
    end
    si = divexact(S[i], g)
    a = divexact(a, g)
    if isunit(si) # g = S[i] and S[i] | a
      continue
    end
    S[i] = si
    if isunit(a) # g = a and a | S[i]
      a = copy(g)
      continue
    end
    augment_steel(S, copy(g), i)
    continue
  end
  if !isunit(a)
    push!(S, a)
  end

  return S;
end

function coprime_base_steel(S::Array{E, 1}) where E
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
# julia> I = [fmpz(rand(1:10000))*rand(1:10000) for i in 1:10000];
# 
# experimentally, unless the input is enormous, Steel wins
# on smallish input Bach is better than Bernstein, on larger this
# changes
# 
# needs
# isone, gcd_into!, divexact!, copy
# (some more for Bernstein: FactorBase, gcd, divexact)

@doc Markdown.doc"""
    coprime_base{E}(S::Array{E, 1}) -> Array{E, 1}

Returns a coprime base for S, ie. the resulting array contains pairwise coprime objects that multiplicatively generate the same set as the input array.
"""
coprime_base(x) = coprime_base_steel(x)

@doc Markdown.doc"""
    coprime_base_insert{E}(S::Array{E, 1}, a::E) -> Array{E, 1}

Given a coprime array S, insert a new element, ie. find a coprime base for push(S, a)
"""
coprime_base_insert(S, a) = augment_steel(S, a)


