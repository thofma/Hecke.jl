################################################################################
#
#  Lifting again
#
################################################################################

mutable struct Emat
  R
  n
  i
  j
  a
end

function matrix(e::Emat)
  z = identity_matrix(e.R, e.n)
  z[e.i, e.j] = e.a
  return z
end

inv(e::Emat) = Emat(e.R, e.n, e.i, e.j, -e.a)

function elementary_matrix(R, n, i, j, a)
  M = identity_matrix(R, n)
  M[i, j] = a
  return M
end

function _lift2(MM)
  M = deepcopy(MM)
  R = base_ring(M)
  S = _base_ring(R)
  @assert det(M) == 1
  k = 1
  n = nrows(M)
  left = []
  left2 = []
  while k < ncols(M)
    @assert det(M) == 1
    # scan the first column for a unit
    v = Int[euclid(M[i, k]) for i in k:n]
    #@show v
    if isone(minimum(abs.(v)))
      l = findfirst(isone, v) + (k - 1)
      #@show k, M
      #@show is_unit(M[l, k])
      #@show M[l, k]
      if l != k
        @assert l isa Int
        #@show l
        b = M[l, k]
        @assert det(M) == 1
        E1 = elementary_matrix(R, n, k, l, one(R))
        E2 = elementary_matrix(R, n, l, k, -one(R))
        E3 = elementary_matrix(R, n, k, l, one(R))
        M = (E1 * E2 * E3) * M
        @assert det(M) == 1
        # push first E3
        push!(left, elementary_matrix(S, n, k, l, one(S)))
        @assert map_entries(R, left[end]) == E3
        push!(left2, Emat(S, n, k, l, one(S)))
        push!(left, elementary_matrix(S, n, l, k, -one(S)))
        push!(left2, Emat(S, n, l, k, -one(S)))
        @assert map_entries(R, left[end]) == E2
        push!(left, elementary_matrix(S, n, k, l, one(S)))
        push!(left2, Emat(S, n, k, l, one(S)))
        @assert map_entries(R, left[end]) == E1
      end
      @assert det(M) == 1
      @assert is_unit(M[k, k])
      for j in (k+1):n
        if !iszero(M[j, k])
          N = deepcopy(M)
          q = divexact(M[j, k], M[k, k])
          E = elementary_matrix(R, n, j, k, -q)
          push!(left, elementary_matrix(S, n, j, k, lift(-q)))
          push!(left2, Emat(S, n, j, k, lift(-q)))
          @assert map_entries(R, left[end]) == E
          for o in 1:n
            M[j, o] = M[j, o] - q * M[k, o]
          end
          @assert E * N == M
        end
      end
      k += 1
      #@show M
    else # no unit there # I could do this in one go by putting a unit in the first position
      _, l = findmin(abs.(v))
      l = l + (k - 1)
      #@show l
      #@show euclid(M[l, k])
      #@show v
      for j in k:n
        if j == l
          continue
        end
        fl, _ = divides(M[j, k], M[l, k])
        if !fl
          #@show M[j, k], M[l, k]
          N = deepcopy(M)
          #@show euclid(M[j, k])
          q, r = divrem(M[j, k], M[l, k])
          #@show euclid(r)
          E = elementary_matrix(R, n, j, l, -q)
          for o in 1:n
            M[j, o] = M[j, o] - q * M[l, o]
          end
          push!(left, elementary_matrix(S, n, j, l, lift(-q)))
          push!(left2, Emat(S, n, j, l, lift(-q)))
          @assert map_entries(R, left[end]) == E
          @assert E * N == M
          break
        end
      end
    end
    @assert det(M) == 1
  end
  #println("M should now be lower triangular")
  #@show M
  @assert det(M) == 1
  # Now M is lower triangular with units on the diagonal
  #@show "here"
  for i in n:-1:2
    for j in (i - 1):-1:1
      # set jth row to jth row - M[k, j]/M[k, k] * jth row
      #@show is_unit(M[i, i])
      #@show M[i, i]
      q = -divexact(M[j, i], M[i, i])
      @assert (-q) * M[i, i] == M[j, i]
      E = elementary_matrix(R, n, j, i, q)
      push!(left, elementary_matrix(S, n, j, i, lift(q)))
      push!(left2, Emat(S, n, j, i, lift(q)))
      @assert map_entries(R, left[end]) == E
      N = deepcopy(M)
      M[j, i] = M[j, i] + q * M[i, i]
      @assert E * N == M
    end
  end
  @assert det(M) == 1
  # Now sort the diagonal
  # We use this neat trick of Rosenberg, p. 60
  for i in 1:(n - 1)
    a = inv(M[i, i])
    ainv = M[i, i]
    # we multiply with (1,...1,a,a^-1,1,...1)
    E1 = elementary_matrix(R, n, i, i + 1, a)
    E2 = elementary_matrix(R, n, i + 1, i, -ainv)
    E3 = E1
    #E4 = identity_matrix(R, n)
    #E4[i, i] = 0
    #E4[i, i + 1] = -1
    #E4[i + 1, i + 1] = 0
    #E4[i + 1, i] = 1
    E5 = elementary_matrix(R, n, i, i + 1, -one(R))
    E6 = elementary_matrix(R, n, i + 1, i, one(R))
    E4 = E6

    #E4S = identity_matrix(S, n)
    #E4S[i, i] = 0
    #E4S[i, i + 1] = -1
    #E4S[i + 1, i + 1] = 0
    #E4S[i + 1, i] = 1
    E1S = elementary_matrix(S, n, i, i + 1, lift(a))
    E1SS = Emat(S, n, i, i + 1, lift(a))
    E2S = elementary_matrix(S, n, i + 1, i, lift(-ainv))
    E2SS = Emat(S, n, i + 1, i, lift(-ainv))
    E3S = E1S
    E3SS = E1SS
    E5S = elementary_matrix(S, n, i, i + 1, -one(S))
    E5SS = Emat(S, n, i, i + 1, -one(S))
    E6S = elementary_matrix(S, n, i + 1, i, one(S))
    E6SS = Emat(S, n, i + 1, i, one(S))
    E4S = E6S
    E4SS = E6SS
    push!(left, E6S)
    push!(left, E5S)
    push!(left, E4S)
    push!(left, E3S)
    push!(left, E2S)
    push!(left, E1S)
    push!(left2, E6SS)
    push!(left2, E5SS)
    push!(left2, E4SS)
    push!(left2, E3SS)
    push!(left2, E2SS)
    push!(left2, E1SS)

    M = (E1 * E2 * E3 * E4 * E5 * E6) * M
    @assert det(M) == 1
  end

  @assert isone(M)

  for i in 1:length(left)
    @assert matrix(left2[i]) == left[i]
  end

  @assert map(R, prod(reverse(left))) * MM == 1

  return prod(matrix.(inv.(left2)))

  return M, left
end

euclid(n::nmod) = gcd(n.data, modulus(parent(n)))
euclid(n::Nemo.fmpz_mod) = gcd(n.data, modulus(parent(n)))

function Base.divrem(n::T, m::T) where T <: Union{nmod,Nemo.fmpz_mod}
  @assert !iszero(m)
  R = parent(n)
  e = euclid(m)
  if isone(e)
    fl, q = divides(n, m)
    @assert fl
    return q, zero(R)
  end

  cp = coprime_base(fmpz[n.data, m.data, modulus(R)])::Vector{fmpz}

  q = Vector{Tuple{fmpz, fmpz}}()
  for i=1:length(cp)
    v = valuation(modulus(R), cp[i])::Int
    if v != 0
      pk = cp[i]^v
      nv = iszero(n.data % pk) ? inf : valuation(n.data % pk, cp[i])
      mv = iszero(m.data % pk) ? inf : valuation(m.data % pk, cp[i])
      if nv < mv
        push!(q, (pk, 0))
      else
        if nv === inf
          push!(q, (pk, 1))
        else
          push!(q, (pk, divexact(n.data % pk, cp[i]^nv)))
        end
      end
    end
  end
  qq = R(crt([x[2] for x = q], [x[1] for x = q])::fmpz)::T
  rr = n-qq*m
  @assert n == qq*m+rr
  @assert rr == 0 || euclid(rr) < e
  return (qq,rr)::Tuple{T, T}
end

