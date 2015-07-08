################################################################################
#
#  LatEnum.jl : Basic lattice enumeration
#
################################################################################

# (C) 2015 Claus Fieker

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

# now that x is a fmpz_mat, the type for x is not really used
type enum_ctx{Tx, TC, TU}
  G::fmpz_mat
  n::Int
  limit :: Int # stop recursion at level limit, defaults to n
  d::Union(Integer, fmpz) #we actually want G/d
  C::Array{TC, 2} # the pseudo-cholesky form - we don't have fmpq_mat
  last_non_zero::Int
  x::fmpz_mat # 1 x n
  U::Array{TU, 1}
  L::Array{TU, 1}
  l::Array{TU, 1}
  tail::Array{TU, 1}
  c::fmpz # the length of the elements we want
  t::fmpz_mat # if set, a transformation to be applied to all elements
  t_den::fmpz
  function enum_ctx()
    return new()
  end
end

function show(io::IO, E::enum_ctx)
  println(io, "EnumCtx")
  println(io, "curr. length ", E.c, " elt ", E.x, "(", (typeof(E.x), typeof(E.C), typeof(E.U)), ")")
end

#need to only compute the top l x l submatrix when using limited enum
function pseudo_cholesky(G::fmpz_mat, den=1; 
                 TC::Type=Rational{BigInt}, limit = rows(G))
  n = cols(G)
  @hassert :LatEnum 1 rows(G) == n
  limit = min(limit, n)
  t = ZZ()
  C = Array(TC,limit,limit)
  for i=1:limit
    for j=1:limit
      getindex!(t, G, i, j)
      C[i,j] = TC(t)/TC(den)
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
    @hassert :LatEnum 1 C[j,j] > 0
    for i=j+1:limit
      C[i,j] = 0
    end
  end
  @hassert :LatEnum 1 C[limit,limit] > 0
  return C
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
  E.L = Array(TU, limit) #lower and
  E.U = Array(TU, limit) #upper bounds for the coordinates

  E.l = Array(TU, limit) #current length
  E.tail = Array(TU, limit)
  return E
end

function enum_ctx_local_bound{T}(a::Rational{T}, b::Rational{T})
  #return L <= U sth.
  #L = ceil(a-sqrt(b)), U = floor(a+sqrt(b))
  #solves (gives bounds) for (a-x)^2 <= b
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

function enum_ctx_local_bound{Number}(a::Number, b::Number)
  #return L <= U sth.
  #L = ceil(a-sqrt(b)), U = floor(a+sqrt(b))
  #solves (gives bounds) for (a-x)^2 <= b
  @hassert :LatEnum b >= 0
  i = sqrt(b)
  L = Base.ceil(a-i)
  U = Base.floor(a+i)
#println("local bound for ", a, " and ", b)
#println("is ", L, " and ", U)
  return L, U
end


function enum_ctx_start{A,B,C}(E::enum_ctx{A,B,C}, c::fmpz)
  E.c = c
  zero!(E.x)
  for i=1:E.limit
    E.l[i] = C(E.c)/C(E.d)
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
               

function enum_ctx_advance_level{A,B,C}(E::enum_ctx{A,B,C}, i::Int)
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

global _next = 0.0
function enum_ctx_next{A,B,C}(E::enum_ctx{A,B,C})
  global _next
  @v_do :ClassGroup_time 2 rt = time_ns()
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

function enum_ctx_short_elements{A,B,C}(E::enum_ctx{A,B,C}, c::fmpz, limit=-1)
  enum_ctx_start(E, c)
  if enum_ctx_next(E)
    l = transpose(E.x)
  end
  while enum_ctx_next{A,B,C}(E) && (limit == -1 || limit >= Base.size(l, 1))
    l = vcat(l, transpose(E.x))
  end
  return l
end
