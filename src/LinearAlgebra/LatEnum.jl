################################################################################
#
#                 LatEnum.jl : Basic lattice enumeration
#
# This file is part of hecke.
#
# Copyright (c) 2015: Claus Fieker, Tommy Hofmann
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
#
# (C) 2015 Claus Fieker
# (C) 2015 Tommy Hofmann
#
################################################################################
#  TODO:
#   - (sh/c)ould be indexed by the type of G and C
#     in fact, since G is not used after the creation, maybe we should drop it.
#     realisticly, x (hence L, U) can be small types mostly
#   - support for lower bound
#   - reference vector
#   - support for all points
#   - if all points are wanted, the spiraling out, enumerating coordinates from
#     the center outwards is counter-productive
#   - lower bounds should be non-trivial speed-up by effectively generating the
#     L, U for the other bound as well and using this for exclusion.
#     (see other comment below)

add_assertion_scope(:LatEnum)
add_verbosity_scope(:LatEnum)

function show(io::IO, E::enum_ctx)
  println(io, "EnumCtx")
  if isdefined(E, :c)
    println(io, "curr. length ", E.c, " elt ", E.x, "(", (typeof(E.x), typeof(E.C), typeof(E.U)), ")")
  end
end

#need to only compute the top l x l submatrix when using limited enum
function pseudo_cholesky(G::ZZMatrix, den=1;
                 TC::Type=Rational{BigInt}, limit = nrows(G))
  n = ncols(G)
  @hassert :LatEnum 1 nrows(G) == n
  limit = min(limit, n)
  t = ZZRingElem()
  C = Array{TC}(undef, limit, limit)
  for i=1:limit
    for j=1:limit
      getindex!(t, G, i, j)
      C[i,j] = TC(t//den)
    end
  end
  for i = 1:limit-1
    for j = i+1:limit
      C[j,i] = C[i,j]
      C[i,j] = C[i,j]/C[i,i]
    end
    for k = i+1:limit
      for l = i+1:limit
        C[k,l] = C[k,l] - C[k,i]*C[i,l]
      end
    end
  end
  for j = 1:limit-1
    if C[j,j] <= 0
      throw(LowPrecisionCholesky())
    end
    for i=j+1:limit
      C[i,j] = 0
    end
  end
  if C[limit, limit] <= 0
    throw(LowPrecisionCholesky())
  end
  return C
end

function enum_ctx_from_basis(B::FakeFmpqMat; Tx::Type = BigInt, TC::Type = Rational{BigInt}, TU::Type = Rational{BigInt}, limit = nrows(B))
  G = gram(numerator(B))
  return enum_ctx_from_gram(G, denominator(B)^2, Tx=Tx, TC=TC, TU=TU, limit = limit)
end

function enum_ctx_from_gram(G::FakeFmpqMat; Tx = BigInt, TC = Rational{BigInt}, TU = Rational{BigInt}, limit = nrows(G))
  return enum_ctx_from_gram(numerator(G), denominator(G), Tx=Tx, TC=TC, TU=TU, limit = limit)
end

function enum_ctx_from_basis(B::ZZMatrix, den::ZZRingElem = ZZRingElem(1); Tx::Type = BigInt, TC::Type = Rational{BigInt}, TU::Type = Rational{BigInt}, limit = nrows(B))
  G = gram(B)
  return enum_ctx_from_gram(G, den*den, Tx=Tx, TC=TC, TU=TU, limit = limit)
end

function enum_ctx_from_gram(G::ZZMatrix, den = 1; Tx = BigInt, TC = Rational{BigInt}, TU = Rational{BigInt}, limit = nrows(G))
  E = enum_ctx{Tx, TC, TU}()
  E.G = G
  n = nrows(G)
  E.n = n
  limit = min(limit, n)
  E.limit = limit
  E.d = den
  E.C = pseudo_cholesky(E.G, den, TC = TC, limit = limit)
  E.x = zero_matrix(FlintZZ, 1, n)
    #coeffs limit+1:n are going to be zero, always
  E.L = Vector{TU}(undef, limit) #lower and
  E.U = Vector{TU}(undef, limit) #upper bounds for the coordinates

  E.l = Vector{TU}(undef, limit) #current length
  E.tail = Vector{TU}(undef, limit)
  return E
end

function enum_ctx_local_bound(a::Rational{T}, b::Rational{T}) where T
  #return L <= U sth.
  #L = ceil(a-sqrt(b)), U = floor(a+sqrt(b))
  #solves (gives bounds) for (a-x)^2 <= b
  b >= 0 || return a, a-1
  @hassert :LatEnum 1 b >= 0
  d = denominator(b)
  i = isqrt(numerator(b*d*d))
  L = Base.ceil(a-(i+1)//d)
  U = Base.floor(a+(i+1)//d)
#  @show L, U, Base.ceil(BigFloat(a) - sqrt(BigFloat(b))), Base.floor(BigFloat(a) + sqrt(BigFloat(b)))
  if (a-L)^2 >b
    L +=1
  end
  if (a-U)^2>b
    U -= 1
  end

#println("local bound for ", a, " and ", b)
#println("is ", L, " and ", U)
  return L, U
end

function enum_ctx_local_bound(a::Number, b::Number) where Number
  #return L <= U sth.
  #L = ceil(a-sqrt(b)), U = floor(a+sqrt(b))
  #solves (gives bounds) for (a-x)^2 <= b
  b >= 0 || return a, a-1
  @hassert :LatEnum 1 b >= 0
  i = sqrt(b)
  L = Base.ceil(a-i)
  U = Base.floor(a+i)
#println("local bound for ", a, " and ", b)
#println("is ", L, " and ", U)
  return L, U
end

function enum_ctx_start(E::enum_ctx{A,B,C}, c::ZZRingElem) where {A,B,C}
  E.c = c
  zero!(E.x)
  for i=1:E.limit
    E.l[i] = C(E.c//E.d)
    E.tail[i] = 0
    L, U = enum_ctx_local_bound(C(0), C(B(E.c//E.d)/E.C[i,i]))
    @hassert :LatEnum 1 typeof(L) == C
    @hassert :LatEnum 1 typeof(U) == C
    @hassert :LatEnum 1 typeof(E.L) == Vector{C}
    E.U[i] = U
    E.L[i] = L
  end
  E.U[1] = max(E.U[1], 1)
  E.L[1] = -E.U[1]
  E.last_non_zero = 1
  E.cnt = 0
end

#start enumeration at the element x, the bound on the length
#is the length of x * eps
function enum_ctx_start(E::enum_ctx{A,B,C}, x::ZZMatrix; eps::Float64=1.0) where {A,B,C}
  E.x = x
  for i=E.limit-1:-1:1
    E.tail[i] = sum(E.C[i, j]*C(E.x[1,j]) for j=i+1:E.limit)
  end
  b = sum(E.C[i,i]*(C(E.x[1,i]) + E.tail[i])^2 for i=1:E.limit) #curr. length
  #@show b, C((x*E.G*x')[1,1])
  #@assert b == C((x*E.G*x')[1,1])
  E.c = ceil(ZZRingElem, b*C(E.d)*eps)
  E.l[E.limit] = C(E.c//E.d)
  for i=E.limit-1:-1:1
    E.l[i] = E.l[i+1] - E.C[i+1,i+1]*(C(E.x[1,i+1]) + E.tail[i+1])^2
  end
  for i=1:E.limit
    E.L[i], E.U[i] = enum_ctx_local_bound(-E.tail[i], E.l[i]/E.C[i,i])
  end
  E.last_non_zero = maximum(findall(i->E.x[1, i] != 0, 1:E.limit))+1
end

#start enumeration at the first element having a 1 at position i (and zeros
#for all j>i.
#the length is going to be the length of the i-th unit vector * eps
#(the actual vector might be shorter)
function enum_ctx_start(E::enum_ctx{A,B,C}, i::Int; eps::Float64=1.0) where {A,B,C}
  for j=1:E.limit
    if j == i
      E.x[1, j] = 1
    else
      E.x[1, j] = 0
    end
  end
  E.last_non_zero = i+1

  for k=E.limit-1:-1:1
    E.tail[k] = sum(E.C[k, j]*C(E.x[1,j]) for j=k+1:E.limit)
  end
  b = sum(E.C[j,j]*(C(E.x[1,j]) + E.tail[j])^2 for j=1:E.limit) #curr. length
  #@show b, C((x*E.G*x')[1,1])
  #@assert b == C((x*E.G*x')[1,1])
  E.c = ceil(ZZRingElem, b*C(E.d)*eps)
  E.l[E.limit] = C(E.c//E.d)
  for j=E.limit-1:-1:1
    E.l[j] = E.l[j+1] - E.C[j+1,j+1]*(C(E.x[1,j+1]) + E.tail[j+1])^2
  end
  for j=E.limit:-1:1
    E.L[j], E.U[j] = enum_ctx_local_bound(-E.tail[j], E.l[j]/E.C[j,j])
    if j < i
      E.x[1, j] = A(Base.ceil((E.L[j] +E.U[j])/2))
      E.tail[j] = sum(E.C[j, k]*C(E.x[1,k]) for k=j+1:E.limit)
      E.l[j] = E.l[j+1] - E.C[j+1,j+1]*(C(E.x[1,j+1]) + E.tail[j+1])^2
    end
  end
end

#
#missing: lower bound
#         reference vector (eventually)
#         length
#         proper lattice type

@inline function fmpz_mat_entry_incref!(a::ZZMatrix, r::Int, c::Int)
  z = Nemo.mat_entry_ptr(a, r, c)
  ccall((:fmpz_add_ui, libflint), Nothing, (Ptr{ZZRingElem}, Ptr{ZZRingElem}, Int), z, z, 1)
end

function fmpz_mat_entry_add_ui!(a::ZZMatrix, r::Int, c::Int, v::UInt)
  z = Nemo.mat_entry_ptr(a, r, c)
  ccall((:fmpz_add_ui, libflint), Nothing, (Ptr{ZZRingElem}, Ptr{ZZRingElem}, Int), z, z, v)
end

function enum_ctx_advance_level(E::enum_ctx{A,B,C}, i::Int) where {A,B,C}
#  println("i: ", i, "                                   "[1:2*i], "|")
  t = ZZRingElem()
  if i == E.last_non_zero-1
    fmpz_mat_entry_incref!(E.x, 1, i)
#    E.x[1, i] = getindex!(t, E.x, 1, i) + 1
  elseif i == E.last_non_zero
#    @hassert :LatEnum 1 E.x[1, i] == 0
    E.last_non_zero += 1
    fmpz_mat_entry_incref!(E.x, 1, i)
#    E.x[1, i] = getindex!(t, E.x, 1, i) + 1
  else
    s = E.U[i] + E.L[i]
    getindex!(t, E.x, 1, i)
    x = A(t)
    if s < 2*x  # larger than the middle
      setindex!(E.x, -x + A(Base.floor(s)), 1, i)
    else
      setindex!(E.x, -x + A(Base.floor(s)) + 1, 1, i)
    end
  end
end

_next = 0.0

function enum_ctx_next(E::enum_ctx{A,B,C}) where {A,B,C}
  global _next
  @v_do :ClassGroup_time 2 rt = time_ns()
  E.cnt += 1
  n::Int = 1
  n = E.limit
  i=1
  t = ZZRingElem()
  while true
    enum_ctx_advance_level(E, i)
    getindex!(t, E.x, 1, i)
    if E.L[i] <= A(t) <= E.U[i] #coordinate is valid
      if i==1
        @v_do :ClassGroup_time 2 _next += time_ns()-rt
        return true
      else
        i -= 1
      end
    else # coordinate is invalid
      i += 1
      if i>n
        @v_do :ClassGroup_time 2 _next += time_ns()-rt
        return false
      end
      continue
    end

    @hassert :LatEnum 1 i < n
    while true
      getindex!(t, E.x, 1, i+1)
      t1 = A(t)
      E.tail[i] = E.C[i, i+1]*t1
      for j = i+2:n
        getindex!(t, E.x, 1, j)
        E.tail[i] += E.C[i, j] * A(t)
      end
      #E.tail[i] = sum C[i,j]x[j]
      E.l[i]    = E.l[i+1] - E.C[i+1, i+1]*(t1 + E.tail[i+1])^2
      #l[i] = l[i+1] - C[i+1, i+1]^2*(x[i+1] + tail[i+1])

      if E.l[i] >= 0
        Z = C(B(E.l[i])/E.C[i,i])
#        @hassert :LatEnum 1 E.l[i] >= 0
#        @hassert :LatEnum 1 E.C[i,i] > 0
#        @hassert :LatEnum 1 Z >= 0
        L, U = enum_ctx_local_bound(-E.tail[i], Z)
#        @hassert :LatEnum 1 typeof(L) == C
        E.L[i] = L
        E.U[i] = U

        x = A(Base.ceil((E.L[i] +E.U[i])/2))
        E.x[1, i] = x
        if -E.L[i] == E.U[i] && E.last_non_zero == i+1
          E.last_non_zero = i
#          @hassert :LatEnum 1 x == 0
        end
        if x <= E.U[i] # coordinate is valid
          i -= 1       # go further up
          if i==0
            @v_do :ClassGroup_time 2 _next += time_ns()-rt
            return true
          end
          continue
        else  # coordinate invalid, need to try next on i+1
          i += 1
          if i>n
            @v_do :ClassGroup_time 2 _next += time_ns()-rt
            return false
          end
          break
        end
      else # interval too short
        i += 1
        if i>n
          @v_do :ClassGroup_time 2 _next += time_ns()-rt
          return false
        end
        break
      end
    end
  end
  @v_do :ClassGroup_time 2 _next += time_ns()-rt
  return true
end

function enum_ctx_short_elements(E::enum_ctx{A,B,C}, c::T, limit=-1) where {A,B,C} where T <: IntegerUnion
  enum_ctx_start(E, ZZRingElem(c))
  if enum_ctx_next(E)
    l = deepcopy(E.x) # else the 1st element is not returned....
  else
    l = matrix(FlintZZ, 0, E.n, ZZRingElem[])
  end
  while enum_ctx_next(E) && (limit == -1 || limit >= Base.size(l, 1))
    l = vcat(l, E.x)
  end
  return l
end

################################################################################
#
#  Enumerating using ArbFieldElem objects
#
################################################################################

function pseudo_cholesky(G::ArbMatrix)
  n = ncols(G)
  C = deepcopy(G)
  for i = 1:n-1
    for j = i+1:n
      C[j,i] = C[i,j]
      C[i,j] = C[i,j]//C[i,i]
      if !isfinite(C[i,j])
          error("Precision not high enough")
      end
    end
    for k = i+1:n
      for l = i+1:n
        C[k,l] = C[k,l] - C[k,i]*C[i,l]
        if !isfinite(C[k,l])
          error("Precision not high enough")
        end
      end
    end
  end
  for j = 1:n-1
    for i=j+1:n
      C[i,j] = parent(C[i,j])(0)
    end
  end
  for i in 1:n
    #println(C[i,i])
    if contains_zero(C[i,i])
      error("Precision not high enough")
    end
  end

  return C
end


function enumerate_using_gram(G::ArbMatrix, c::ArbFieldElem)
  E = EnumCtxArb(pseudo_cholesky(G))
  return _enumerate(E, c, nrows(G), zero_matrix(FlintZZ, 1, nrows(G)))
end

function _enumerate(E::EnumCtxArb, c::ArbFieldElem, i::Int, x::ZZMatrix)
  # assume x_n,x_n-1,...,x_i+1 are set
  # compute the bound for x_i
  G = E.G
  n = nrows(G)
  p = E.p
  #recprint(n-i)
  #println("I am at level $i with $x")

  @vprintln :LatEnum "$(recprint(n - i)) Gii: , $(G[i,i])"
  @vprintln :LatEnum "$(recprint(n - i)) c: $(ArbField(p)(c))"

  C = ArbField(p)(c)//G[i,i]

  @vprintln :LatEnum "$(recprint(n - i)) C: $C"

  if !contains_zero(C)
    C = sqrt(C)
  else
    # Element C contains zero, this is a bad when taking square root
    # (this would ive NaN).
    # The elements abs(C) also contains zero.
    # The only(?) way to do it is to invoke arb_get_abs_ubound_arf.
    # This should work, potentially we enumerate more elements

    tm = arf_struct(0, 0, 0, 0)
    ccall((:arf_init, libarb), Nothing, (Ref{arf_struct}, ), tm)

    ccall((:arb_get_abs_ubound_arf, libarb), Nothing, (Ref{arf_struct}, Ref{ArbFieldElem}), tm, C)
    ccall((:arb_set_arf, libarb), Nothing, (Ref{ArbFieldElem}, Ref{arf_struct}), C, tm)

    ccall((:arf_clear, libarb), Nothing, (Ref{arf_struct}, ), tm)

    @hassert :LatEnum !contains_zero(C)
  end

  @vprintln :LatEnum "$(recprint(n - i)) C: $C"

  CC = ArbField(p)(0)

  for j in i+1:n
    CC = CC + G[i,j]*x[1,j]
  end

  lb = -CC - C
  ub = -CC + C

  tr_ptr = ccall((:arb_rad_ptr, libarb), Ptr{Nemo.mag_struct}, (Ref{ArbFieldElem}, ), lb)

  tm_ptr = ccall((:arb_mid_ptr, libarb), Ptr{arf_struct}, (Ref{ArbFieldElem}, ), lb)
  u = arf_struct(0, 0, 0, 0)
  ccall((:arf_init, libarb), Nothing, (Ref{arf_struct}, ), u)

  ccall((:arf_set_mag, libarb), Nothing, (Ref{arf_struct}, Ptr{Nemo.mag_struct}), u, tr_ptr)
  ccall((:arf_sub, libarb), Nothing, (Ref{arf_struct}, Ptr{arf_struct}, Ref{arf_struct}, Int, Cint), u, tm_ptr, u, p, 4) # 4 is round to -infty
  lbfmpz = ZZRingElem()
  ccall((:arf_get_fmpz, libarb), Nothing, (Ref{ZZRingElem}, Ref{arf_struct}, Cint), lbfmpz, u, 4)

  tr = ccall((:arb_rad_ptr, libarb), Ptr{Nemo.mag_struct}, (Ref{ArbFieldElem}, ), ub)
  tm = ccall((:arb_mid_ptr, libarb), Ptr{arf_struct}, (Ref{ArbFieldElem}, ), ub)

  ccall((:arf_set_mag, libarb), Nothing, (Ref{arf_struct}, Ptr{Nemo.mag_struct}), u, tr)
  ccall((:arf_sub, libarb), Nothing, (Ref{arf_struct}, Ptr{arf_struct}, Ref{arf_struct}, Int, Cint), u, tm, u, p, 3) # 3 is round to +infty
  ubfmpz = ZZRingElem()
  ccall((:arf_get_fmpz, libarb), Nothing, (Ref{ZZRingElem}, Ref{arf_struct}, Cint), ubfmpz, u, 3)

  ccall((:arf_clear, libarb), Nothing, (Ref{arf_struct}, ), u)

  @vprintln :LatEnum "$(recprint(n - i)) Coordinate $i between $lbfmpz and $ubfmpz"

  A = Vector{Vector{ZZRingElem}}()

  if i == 1
    @vprintln :LatEnum "$(recprint(n - i)) his is depth $i"

    for j in Int(lbfmpz):Int(ubfmpz)
      @vprintln :LatEnum "$(recprint(n - i)) j is $j"
      if is_negative(c - G[i,i]*(j + CC)^2)
        @vprintln :LatEnum "$(recprint(n - i)) Something is negative"
        continue
      end
      push!(A, [ ZZRingElem(j) ])
    end
  else
    for j in Int(lbfmpz):Int(ubfmpz)
      @vprintln :LatEnum "$(recprint(n - i)) $x $i $j: $c $(G[i,i]) $CC"
      @vprintln :LatEnum "$(recprint(n - i)) $x $i $j $(G[i,i]*j^2)"
      @vprintln :LatEnum "$(recprint(n - i)) $x $i $j: $(c - G[i,i]*(j + CC)^2)"
      t = c - G[i,i]*(j + CC)^2

      if is_negative(t)
        continue
      end

      x[1,i] = j
      l = _enumerate(E, t, i - 1, x)
      for k in 1:length(l)
        if n == length(l[k]) + 1 && iszero(j) && all(iszero, l[k])
          continue
        end
        push!(A, push!(l[k], ZZRingElem(j)))
      end
    end
  end

  return A
end

function recprint(n::Int)
  s = "  "^n
  return s
end

@doc raw"""
    hermite_constant(n::Int, R=ArbField(100))

The $n$-th Hermite constant (for lattices) to the power $n$.
Exact value if $1 \le n \le 8$ and Blichfeld's upper bound
otherwise.
"""
function hermite_constant(n::Int, R=ArbField(20))
  if n <= 8
    return R([1, 4/3, 2, 4, 8, 64/3, 64, 256][n])
  end
  return (2/pi)^n*gamma(R(2+n/2))^2
end

#using semi_factorial and gamma_half we can write the Blichfeld bound
#as rational * pi^1-n (if we want)
#Blichfeld = pi^(1-n) /8 * semi_factorial(n+2)^2
#
function semi_factorial(n::Int)
  if isodd(n)
    return prod([ZZRingElem(2*i-1) for i=1:div(n+1, 2)])
  else
    return prod([ZZRingElem(2*i) for i=1:div(n, 2)])
  end
end

function gamma_half(n::Int)
  #gamma(n/2)
  return sqrt(pi)*semi_factorial(n-2)/2^((n-1)/2)
end


