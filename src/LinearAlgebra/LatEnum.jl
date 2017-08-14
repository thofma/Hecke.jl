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
#  Todo:
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

add_assert_scope(:LatEnum)
add_verbose_scope(:LatEnum)

function show(io::IO, E::enum_ctx)
  println(io, "EnumCtx")
  if isdefined(E, :c)
    println(io, "curr. length ", E.c, " elt ", E.x, "(", (typeof(E.x), typeof(E.C), typeof(E.U)), ")")
  end  
end

#need to only compute the top l x l submatrix when using limited enum
function pseudo_cholesky(G::fmpz_mat, den=1; 
                 TC::Type=Rational{BigInt}, limit = rows(G))
  n = cols(G)
  @hassert :LatEnum 1 rows(G) == n
  limit = min(limit, n)
  t = ZZ()
  C = Array{TC}(limit, limit)
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

function enum_ctx_from_basis(B::FakeFmpqMat; Tx::Type = BigInt, TC::Type = Rational{BigInt}, TU::Type = Rational{BigInt}, limit = rows(B))
  G = gram(num(B))
  return enum_ctx_from_gram(G, den(B)^2, Tx=Tx, TC=TC, TU=TU, limit = limit)
end

function enum_ctx_from_gram(G::FakeFmpqMat; Tx = BigInt, TC = Rational{BigInt}, TU = Rational{BigInt}, limit = rows(G))
  return enum_ctx_from_gram(num(G), den(G), Tx=Tx, TC=TC, TU=TU, limit = limit)
end  
 
function enum_ctx_from_basis(B::fmpz_mat, den::fmpz = ZZ(1); Tx::Type = BigInt, TC::Type = Rational{BigInt}, TU::Type = Rational{BigInt}, limit = rows(B))
  G = gram(B)
  return enum_ctx_from_gram(G, den*den, Tx=Tx, TC=TC, TU=TU, limit = limit)
end

function enum_ctx_from_gram(G::fmpz_mat, den = 1; Tx = BigInt, TC = Rational{BigInt}, TU = Rational{BigInt}, limit = rows(G))
  E = enum_ctx{Tx, TC, TU}()
  E.G = G
  n = E.n =rows(G) 
  E.limit = limit = min(limit, n)
  E.d = den
  E.C = pseudo_cholesky(E.G, den, TC = TC, limit = limit)
  E.x = MatrixSpace(ZZ, 1, n)()
    #coeffs limit+1:n are going to be zero, always
  E.L = Array{TU}(limit) #lower and
  E.U = Array{TU}(limit) #upper bounds for the coordinates

  E.l = Array{TU}(limit) #current length
  E.tail = Array{TU}(limit)
  return E
end

function enum_ctx_local_bound(a::Rational{T}, b::Rational{T}) where T
  #return L <= U sth.
  #L = ceil(a-sqrt(b)), U = floor(a+sqrt(b))
  #solves (gives bounds) for (a-x)^2 <= b
  b >= 0 || return a, a-1
  @hassert :LatEnum 1 b >= 0
  d = den(b)
  i = isqrt(num(b*d*d))
  L = Base.ceil(a-i//d)
  U = Base.floor(a+i//d)
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
  @hassert :LatEnum b >= 0
  i = sqrt(b)
  L = Base.ceil(a-i)
  U = Base.floor(a+i)
#println("local bound for ", a, " and ", b)
#println("is ", L, " and ", U)
  return L, U
end


function enum_ctx_start(E::enum_ctx{A,B,C}, c::fmpz) where {A,B,C}
  E.c = c
  zero!(E.x)
  for i=1:E.limit
    E.l[i] = C(E.c//E.d)
    E.tail[i] = 0
    L, U = enum_ctx_local_bound(C(0), C(B(E.c//E.d)/E.C[i,i]))
    @hassert :LatEnum 1 typeof(L) == C
    @hassert :LatEnum 1 typeof(U) == C
    @hassert :LatEnum 1 typeof(E.L) == Array{C, 1}
    E.U[i] = U
    E.L[i] = L
  end
  E.U[1] = min(E.U[1], 1)
  E.L[1] = -E.U[1]
  E.last_non_zero = 1
  E.cnt = 0
end

#for pol-red-abs we need s.th. else I think
#
#
#missing: lower bound
#         reference vector (eventually)
#         length
#         proper lattice type

function fmpz_mat_entry(a::fmpz_mat, r::Int, c::Int)
  return ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz},
               (Ptr{fmpz_mat}, Int, Int), &a, r - 1, c - 1)
end

function fmpz_mat_entry_incref!(a::fmpz_mat, r::Int, c::Int)
  z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz},
               (Ptr{fmpz_mat}, Int, Int), &a, r - 1, c - 1)
  ccall((:fmpz_add_ui, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Int), z, z, 1)
end

function fmpz_mat_entry_add_ui!(a::fmpz_mat, r::Int, c::Int, v::UInt)
  z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz},
               (Ptr{fmpz_mat}, Int, Int), &a, r - 1, c - 1)
  ccall((:fmpz_add_ui, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Int), z, z, v)
end

function enum_ctx_advance_level(E::enum_ctx{A,B,C}, i::Int) where {A,B,C}
#  println("i: ", i, "                                   "[1:2*i], "|")
  t = ZZ()
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
  t = fmpz()
  while true 
    enum_ctx_advance_level(E, i)
    getindex!(t, E.x, 1, i)
    if E.L[i] <= C(t) <= E.U[i] #coordinate is valid
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
      E.l[i]    = E.l[i+1] - E.C[i+1, i+1]*(t1 + E.tail[i+1])^2
      
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
        if x <= E.U[i] # coordinate is valid`
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
      else # intervall too short
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

function enum_ctx_short_elements(E::enum_ctx{A,B,C}, c::fmpz, limit=-1) where {A,B,C}
  enum_ctx_start(E, c)
  if enum_ctx_next(E)
    l = E.x
  end
  while enum_ctx_next(E) && (limit == -1 || limit >= Base.size(l, 1))
    l = vcat(l, E.x)
  end
  return l
end

################################################################################
#
#  Enumerating using arb objects
#
################################################################################

function pseudo_cholesky(G::arb_mat)
  n = cols(G)
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


function enumerate_using_gram(G::arb_mat, c::arb)
  E = EnumCtxArb(pseudo_cholesky(G))
  return _enumerate(E, c, rows(G), MatrixSpace(ZZ, 1, rows(G))())
end

function _enumerate(E::EnumCtxArb, c::arb, i::Int, x::fmpz_mat)
  # assume x_n,x_n-1,...,x_i+1 are set
  # compute the bound for x_i
  G = E.G
  n = rows(G)
  p = E.p
  #recprint(n-i)
  #println("I am at level $i with $x")

  @vprint :LatEnum "$(recprint(n - i)) Gii: , $(G[i,i])\n"
  @vprint :LatEnum "$(recprint(n - i)) c: $(ArbField(p)(c))\n"

  C = ArbField(p)(c)//G[i,i]

  @vprint :LatEnum "$(recprint(n - i)) C: $C\n"

  if !contains_zero(C)
    C = sqrt(C)
  else
    # Element C contains zero, this is a bad when taking square root
    # (this would ive NaN).
    # The elements abs(C) also contains zero.
    # The only(?) way to do it is to invoke arb_get_abs_ubound_arf.
    # This should work, potentially we enumerate more elements

    tm = arf_struct(0, 0, 0, 0)
    ccall((:arf_init, :libarb), Void, (Ptr{arf_struct}, ), &tm)

    ccall((:arb_get_abs_ubound_arf, :libarb), Void, (Ptr{arf_struct}, Ptr{arb}), &tm, &C)
    ccall((:arb_set_arf, :libarb), Void, (Ptr{arb}, Ptr{arf_struct}), &C, &tm)

    ccall((:arf_clear, :libarb), Void, (Ptr{arf_struct}, ), &tm)

    @hassert :LatEnum !contains_zero(C)
  end

  @vprint :LatEnum "$(recprint(n - i)) C: $C\n"

  CC = ArbField(p)(0)

  for j in i+1:n
    CC = CC + G[i,j]*x[1,j]
  end

  lb = -CC - C
  ub = -CC + C

  #tr = ccall((:arb_get_rad, :libarb), Ptr{mag}, (Ptr{arb}, ), &lb)
  #tm = ccall((:arb_get_mid, :libarb), Ptr{arf}, (Ptr{arb}, ), &lb)

  tr_ptr = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), &lb)
  
  tm_ptr = ccall((:arb_mid_ptr, :libarb), Ptr{arf_struct}, (Ptr{arb}, ), &lb)
  u = arf_struct(0, 0, 0, 0)
  ccall((:arf_init, :libarb), Void, (Ptr{arf_struct}, ), &u)

  ccall((:arf_set_mag, :libarb), Void, (Ptr{arf_struct}, Ptr{Nemo.mag_struct}), &u, tr_ptr)
  ccall((:arf_sub, :libarb), Void, (Ptr{arf_struct}, Ptr{arf_struct}, Ptr{arf_struct}, Int, Cint), &u, tm_ptr, &u, p, 4) # 4 is round to -infty
  lbfmpz = fmpz()
  ccall((:arf_get_fmpz, :libarb), Void, (Ptr{fmpz}, Ptr{arf_struct}, Cint), &lbfmpz, &u, 4)

  #tr = ccall((:arb_get_rad, :libarb), Ptr{mag}, (Ptr{arb}, ), &ub)
  #tm = ccall((:arb_get_mid, :libarb), Ptr{arf}, (Ptr{arb}, ), &ub)
  tr = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), &ub)
  tm = ccall((:arb_mid_ptr, :libarb), Ptr{arf_struct}, (Ptr{arb}, ), &ub)

  ccall((:arf_set_mag, :libarb), Void, (Ptr{arf_struct}, Ptr{Nemo.mag_struct}), &u, tr)
  ccall((:arf_sub, :libarb), Void, (Ptr{arf_struct}, Ptr{arf_struct}, Ptr{arf_struct}, Int, Cint), &u, tm, &u, p, 3) # 3 is round to +infty
  ubfmpz = fmpz()
  ccall((:arf_get_fmpz, :libarb), Void, (Ptr{fmpz}, Ptr{arf_struct}, Cint), &ubfmpz, &u, 3)

  ccall((:arf_clear, :libarb), Void, (Ptr{arf_struct}, ), &u)

  @vprint :LatEnum "$(recprint(n - i)) Coordinate $i between $lbfmpz and $ubfmpz\n"

  A = Array{Array{fmpz, 1}, 1}()

  if i == 1
    @vprint :LatEnum "$(recprint(n - i)) his is depth $i\n"

    for j in Int(lbfmpz):Int(ubfmpz)
      @vprint :LatEnum "$(recprint(n - i)) j is $j\n"
      if isnegative(c - G[i,i]*(j + CC)^2)
        @vprint :LatEnum "$(recprint(n - i)) Something is negative\n"
        continue
      end
      push!(A, [ fmpz(j) ])
    end
  else
    for j in Int(lbfmpz):Int(ubfmpz)
      @vprint :LatEnum "$(recprint(n - i)) $x $i $j: $c $(G[i,i]) $CC\n"
      @vprint :LatEnum "$(recprint(n - i)) $x $i $j $(G[i,i]*j^2)\n"
      @vprint :LatEnum "$(recprint(n - i)) $x $i $j: $(c - G[i,i]*(j + CC)^2)\n"
      t = c - G[i,i]*(j + CC)^2

      if isnegative(t)
        continue
      end

      x[1,i] = j
      l = _enumerate(E, t, i - 1, x)
      for k in 1:length(l)
        push!(A, push!(l[k], fmpz(j)))
      end
    end
  end
  return A
end

function recprint(n::Int)
  s = "  "^n
  return s
end
