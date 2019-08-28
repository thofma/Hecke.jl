################################################################################
#
#  Triangularization
#
################################################################################

function _pivot(A, start_row, col)
  if !iszero(A[start_row, col])
    return 1;
  end

  for j in start_row + 1:nrows(A)
    if !iszero(A[j, col])
      swap_rows!(A, j, start_row)
      return -1
    end
  end

  return 0
end

function _strong_echelon_form(A::Generic.Mat{NfOrdQuoRingElem}, strategy)
  B = deepcopy(A)

  if nrows(B) < ncols(B)
    B = vcat(B, zero_matrix(base_ring(B), ncols(B) - nrows(B), ncols(B)))
  end

  if strategy == :split
    q, w = z_split(ideal(base_ring(A)))
    R = order(ideal(base_ring(A)))
    ideals = q
    if length(w) != 0
      push!(ideals, prod(w))
    end
    C = _strong_echelon_form_split(B, ideals)
    return C
  elseif strategy == :no_split
    C = _strong_echelon_form_nonsplit(B)
    return C
  else
    error("Invalid strategy")
  end
end

function strong_echelon_form(A::Generic.Mat{NfOrdQuoRingElem}, shape::Symbol = :upperright, strategy::Symbol = :split)
  if shape == :lowerleft
    h = _strong_echelon_form(invert_cols(A), strategy)
    invert_cols!(h)
    invert_rows!(h)
    return h
  elseif shape == :upperright
    h = _strong_echelon_form(A, strategy)
    return h
  else
    error("Not yet implemented")
  end
end

function triangularize!(A::Generic.Mat{NfOrdQuoRingElem})
  n = nrows(A)
  m = ncols(A)
  d = one(base_ring(A))

  t_isdiv = 0.0
  t_xxgcd = 0.0
  t_arith = 0.0

  row = 1
  col = 1
  while row <= nrows(A) && col <= ncols(A)
    #println("doing row $row")
    t = _pivot(A, row, col)
    if t == 0
      col = col + 1
      continue
    end
    d = d*t
    for i in (row + 1):nrows(A)
      if iszero(A[i, col])
        continue
      end

      t_isdiv += @elapsed b, q = isdivisible(A[i, col], A[row, col])

      if b
        for k in col:m
          t_arith += @elapsed A[i, k] = A[i, k] - q*A[row, k]
        end
        @hassert :NfOrdQuoRing 1 A[i, col] == zero(base_ring(A))
      else
        t_xxgcd += @elapsed g,s,t,u,v = xxgcd(A[row, col], A[i, col])
        @hassert :NfOrdQuoRing 1 isone(s*v - t*u)

        for k in col:m
          t_arith += @elapsed t1 = s*A[row, k] + t*A[i, k]
          t_arith += @elapsed t2 = u*A[row, k] + v*A[i, k]
          A[row, k] = t1
          A[i, k] = t2
        end
      end
    end
    row = row + 1;
    col = col + 1;
  end
  #println("  === Time triangularization")
  #println("    isdivisbible: $t_isdiv")
  #println("    xxgcd       : $t_xxgcd")
  #println("    arith       : $t_arith")
  #println("    total time  : $(toc())")
  return d
end

function triangularize(A::Generic.Mat{NfOrdQuoRingElem})
  #println("copying ...")
  B = deepcopy(A)
  #println("done")
  triangularize!(B)
  return B
end

################################################################################
#
#  Strong echelon form
#
################################################################################

# Naive version of inplace strong echelon form
# It is assumed that A has more rows then columns.
function strong_echelon_form_naive!(A::Generic.Mat{NfOrdQuoRingElem})
  #A = deepcopy(B)
  n = nrows(A)
  m = ncols(A)

  @assert n >= m

  #print("triangularizing ... ")
  triangularize!(A)
  #println("done")

  T = zero_matrix(base_ring(A), 1, ncols(A))

  # We do not normalize!
  for j in 1:m
    if !iszero(A[j,j]) != 0
      # This is the reduction
      for i in 1:j-1
        if iszero(A[i, j])
          continue
        else
          q, r = divrem(A[i, j], A[j, j])
          for l in i:m
            A[i, l] = A[i, l] - q*A[j, l]
          end
        end
      end

      a = annihilator(A[j, j])

      for k in 1:m
        T[1, k] = a*A[j, k]
      end
    else
      for k in 1:m
        T[1, k] = A[j, k]
      end
    end

    for i in j+1:m 
      
      if iszero(T[1, i])
        continue
      end

      if iszero(A[i, i])
        for k in i:m
          T[1, k], A[i, k] = A[i, k], T[1, k]
        end
      else
        b, q = isdivisible(T[1, i], A[i, i])
        if b
          for k in i:m
            T[1, k] = T[1, k] - q*A[i, k]
          end
          @hassert :NfOrdQuoRing 1 T[1, i] == zero(base_ring(A))
        else
          g,s,t,u,v = xxgcd(A[i, i], T[1, i])

          for k in i:m
            t1 = s*A[i, k] + t*T[1, k]
            t2 = u*A[i, k] + v*T[1, k]
            A[i, k] = t1
            T[1, k] = t2
          end
        end
      end
    end
  end
  return A
end

################################################################################
#
#  Howell form
#
################################################################################

function howell_form!(A::Generic.Mat{NfOrdQuoRingElem})
  @assert nrows(A) >= ncols(A)

  k = nrows(A)

  strong_echelon_form_naive!(A)

  for i in 1:nrows(A)
    if iszero_row(A, i)
      k = k - 1

      for j in (i + 1):nrows(A)
        if !iszero_row(A, j)
          swap_rows!(A, i, j)
          j = nrows(A)
          k = k + 1
        end
      end
    end
  end
  return k
end

function howell_form(A::Generic.Mat{NfOrdQuoRingElem})
  B = deepcopy(A)

  if nrows(B) < ncols(B)
    B = vcat(B, zero_matrix(base_ring(B), ncols(B) - nrows(B), ncols(B)))
  end

  howell_form!(B)

  return B
end

################################################################################
#
#  Determinant
#
################################################################################

function det(M::Generic.Mat{NfOrdQuoRingElem})
  nrows(M) != ncols(M) && error("Matrix must be square matrix")
  N = deepcopy(M)
  d = triangularize!(N)
  z = one(base_ring(M))
  for i in 1:nrows(N)
    z = z * N[i, i]
  end
  return z*d
  q, r = divrem(z, d)
  @hassert :NfOrdQuoRing 1 iszero(r)
  return divexact(z, d)
end

################################################################################
#
#  Z Split
#
################################################################################

function z_split(I::NfOrdIdl)
  b = basis_matrix(I)
  O = order(I)
  n = degree(O)
  c = coprime_base([b[i, i] for i in 1:n])
  nI = norm(I)
  if isone(nI)
    return NfOrdIdl[I], NfOrdIdl[]
  end
  val = Vector{Int}(undef, length(c))
  for i in 1:length(c)
    val[i] = valuation(nI, c[i])
  end
  if n == 1
    nz = one(FlintZZ)
  else
    nz = prod(b[i, i] for i in 2:n)
  end
  
  A = NfOrdIdl[]
  B = NfOrdIdl[]

  for i in 1:length(c)
    a = ideal(O, c[i]^val[i]) + I
    if iszero(mod(nz, c[i]))
      push!(B, a)
    else
      push!(A, a)
    end
  end
  return A, B
end

function can_map_into_integer_quotient(Q::NfOrdQuoRing)
  B = basis_matrix(ideal(Q))
  for i in 2:ncols(B)
    if !isone(B[i, i])
      return false
    end
  end
  return true
end

function map_into_integer_quotient(Q::NfOrdQuoRing)
  B = basis_matrix(ideal(Q))
  m = B[1, 1]
  R = ResidueRing(FlintZZ, m, cached = false)
  f = (x -> R(x.elem.coordinates[1]))
  g = (y -> Q(y.data)::NfOrdQuoRingElem)
  return R, f, g
end

function can_make_small(Q::Generic.ResRing{fmpz})
  if nbits(modulus(Q)) < Sys.WORD_SIZE - 1
    return true
  else
    return false
  end
end

function make_small(Q::Generic.ResRing{fmpz})
  R = ResidueRing(FlintZZ, Int(modulus(Q)), cached = false)
  f = (x -> R(x.data)::nmod)
  g = (x -> Q(x.data)::Generic.Res{fmpz})
  return R, f, g
end


function _strong_echelon_form_split(M::MatElem{NfOrdQuoRingElem}, ideals)
  Q = base_ring(M)
  R = base_ring(Q)
  modulus = ideal(Q)

  n = nrows(M)
  m = ncols(M)

  M_cur = zero_matrix(Q, n, m)
  
  if length(ideals) == 1
    return _strong_echelon_form_nonsplit(M)
  end

  I = ideals[1]

  RmodI, mRmodI = quo(R, I)
  MmodI = zero_matrix(RmodI, n, m)
  for i in 1:n
    for j in 1:m
      MmodI[i, j] = RmodI(lift(R, M[i, j]))
    end
  end
  echelon_modI = _strong_echelon_form_nonsplit(MmodI)

  for i in 1:n
    for j in 1:m
      M_cur[i, j] = Q(lift(R, echelon_modI[i, j]))
    end
  end

  _assure_weakly_normal_presentation(I)
  gI = gcd(Q(I.gen_one), Q(I.gen_two))

  @assert ideal(R, lift(R, gI)) + modulus == I
#    assert R*R!gi + Modulus(Rd) eq i;

  r = M_cur
  l = gI

  for i in 2:length(ideals)
    I = ideals[i]

    m_cur = zero_matrix(Q, n, m)

    RmodI, mRmodI = quo(R, I)
    MmodI = zero_matrix(RmodI, n, m)

    for i in 1:n
      for j in 1:m
        MmodI[i, j] = RmodI(lift(R, M[i, j]))
      end
    end

    echelon_modI = _strong_echelon_form_nonsplit(MmodI)

    for i in 1:n
      for j in 1:m
        m_cur[i, j] = Q(lift(R, echelon_modI[i, j]))
      end
    end

    
    _assure_weakly_normal_presentation(I)
    gI = gcd(Q(I.gen_one), Q(I.gen_two))

    @assert ideal(R, lift(R, gI)) + modulus == I

    g, a, b, e, f = xxgcd(l, gI)
    gg = g
    ginv = inv(g)
    g = g * ginv
    a = a * ginv
    b = b * ginv
    e = e * gg
    f = f * gg
    @assert g == a * l + b * gI
    @assert 0 == e * l + f * gI
    @assert 1 == a * f - b * e
    #@show inv(g)
    a = a * l
    b = b * gI
    #@assert isone(g)
    r = r * b + m_cur * a
    l = l * gI
  end
  return r
end


#    if l cmpeq 1 then
#      r := m;
#      l := gi;
#      L := i;
#    else
#      f, a, b := Idempotents(L, i);
#      if f then
#        a := Rd!a;
#        b := Rd!b;
#      else
#        g, a,b := Xgcd(l, gi);
#        a *:= l;
#        b *:= gi;
#        assert g eq 1;
#      end if;  
#      assert 1 eq a+b;
#      r := r*b+m*a;
#      l *:= gi;
#      L *:= i;

function _strong_echelon_form_nonsplit(M)
  Q = base_ring(M)
  I = ideal(Q)

  n = nrows(M)
  m = ncols(M)

  if can_map_into_integer_quotient(Q)
    RmodIZ, f, g = map_into_integer_quotient(Q)
    M_cur = zero_matrix(Q, n, m)
    if can_make_small(RmodIZ)
      RmodIZsmall, ff, gg = make_small(RmodIZ)
      M_temp = zero_matrix(RmodIZsmall, n, m)
      for i in 1:n
        for j in 1:m
          M_temp[i, j] = ff(f(M[i, j]))
        end
      end
      strong_echelon_form!(M_temp)
      for i in 1:n
        for j in 1:m
          M_cur[i, j] = g(gg(M_temp[i, j]))
        end
      end
    else
      forflint = zero_matrix(FlintZZ, n, m)
      for i in 1:n
        for j in 1:m
          forflint[i, j] = f(M[i, j]).data
        end
      end
      ccall((:fmpz_mat_strong_echelon_form_mod, :libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz}), forflint, RmodIZ.modulus)
      for i in 1:n
        for j in 1:m
          M_cur[i, j] = Q(forflint[i, j])
        end
      end
      #error("dasds")
    end
    return M_cur
  else
    N = deepcopy(M)
    strong_echelon_form_naive!(N)
    return N
  end
end

function test_pseudohnf()
  Qx, x = FlintQQ["x"]
  for i in 2:15
    K, a = NumberField(x^i - 10, "a")
    O = maximal_order(K)
    lp = NfOrdFracIdl[]
    for p in [2, 3, 5, 7, 11, 13]
      pp = prime_decomposition(O, p)
      for P in pp
        push!(lp, frac_ideal(O, P[1]))
      end
    end

    pm = PseudoMatrix(matrix(K, 5, 5, [ rand(-2^10:2^10) for i in 1:25]), rand(lp, 5))

    @time d = numerator(det(pm))

    if iszero(norm(d))
      continue
    end

    q, w = z_split(d)
    R = order(d)
    ideals = q

    if length(w) != 0
      push!(ideals, prod(w))
    end

    @show length(ideals)
    
    gc()
    @time pseudo_hnf_mod(pm, d, strategy = :split)
    gc()
    @time pseudo_hnf_mod(pm, d, strategy = :no_split)
    gc()
    @time pseudo_hnf_kb(pm)
    gc()

    hnf_new = pseudo_hnf_mod(pm, d)
    hnf_old = pseudo_hnf_kb(pm)

    @assert det(hnf_new) == det(hnf_old)

    @assert Hecke._spans_subset_of_pseudohnf(hnf_new, hnf_old, :upperright)
  end
  println("PASS")
end
