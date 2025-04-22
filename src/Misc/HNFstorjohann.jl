#=
HNF algorithm due to Arne Storjohann
"A Fast + Practical + Deterministic Algorithm for Triangularizing Integer Matrices"
=#

# This function only changes CC, zero_cols and N but not T.
function conditioning_with_transform!(T::MatElem{S}, N::MatElem{S}, CC::Array{S}, zero_cols::BitArray, row::Int, col1::Int) where S <: Nemo.RingElement
  @assert col1 < ncols(T)
  @assert T[row, col1] > 0
  R = base_ring(T)
  row1 = row + 1
  # We don't need every field of CC
  for i = (row + 2):nrows(T)
    CC[i] = zero!(CC[i])
    zero_cols[i] = true
  end
  N[1, 1] = deepcopy(T[row, col1])
  N[2, 1] = deepcopy(T[row1, col1])
  t = R()
  t1 = R()
  t2 = R()
  col2 = 0
  s = 0
  for c = (col1 + 1):ncols(T)
    for i = row1:nrows(T)
      t1 = mul!(t1, N[1, 1], T[i, c])
      t2 = mul!(t2, T[row, c], T[i, col1])
      t = t1 - t2
      if !iszero(t)
        col2 = c
        N[1, 2] = deepcopy(T[row, col2])
        N[2, 2] = deepcopy(T[row1, col2])
        # Make sure the rows row and row1 are linearly independent
        if i != row1
          N[2, 1] = add!(N[2, 1], T[i, col1])
          N[2, 2] = add!(N[2, 2], T[i, col2])
          s = i
        end
        break
      end
    end
    if col2 != 0
      break
    end
  end
  @assert col2 != 0
  if row1 == nrows(T)
    return col2
  end
  for l = row + 2:nrows(T)
    g = gcd(N[2, 1], T[l, col1])
    if iszero(g)
      continue
    end
    q1, r1 = divrem(divexact(N[2, 1], g), N[1, 1])
    if r1 < 0
      add!(r1, N[1, 1])
      q1 = q1 - 1
    end
    q2, r2 = divrem(divexact(T[l, col1], g), N[1, 1])
    if r2 < 0
      add!(r2, N[1, 1])
      q2 = q2 - 1
    end
    t1 = mul!(t1, N[1, 1], T[l, col2])
    t2 = mul!(t2, N[1, 2], T[l, col1])
    n = t1 - t2
    if n != 0
      t1 = mul!(t1, N[1, 1], N[2, 2])
      t2 = mul!(t2, N[1, 2], N[2, 1])
      nn = t2 - t1
      @assert nn != 0
      # If nn/n in Z and positive:
      if sign(n) == sign(nn) && rem(nn, n) == 0
        r2 = -r2
      end
    end
    t1 = zero!(t1)
    t2 = deepcopy(r1)
    while gcd(t2, N[1, 1]) != 1
      t2 = add!(t2, r2)
      t1 += 1
    end
    if !iszero(t1)
      if r2 < 0
        t1 = -t1
      end
      CC[l] = deepcopy(t1)
      zero_cols[l] = false
      t = mul!(t, T[l, col1], t1)
      N[2, 1] = add!(N[2, 1], t)
      t = mul!(t, T[l, col2], t1)
      N[2, 2] = add!(N[2, 2], t)
    end
  end
  if s > row1
    CC[s] = CC[s] + R(1)
    zero_cols[s] = false
  end
  return col2
end

# This function only changes N and QC, but not T.
function column_reduction_with_transform!(T::MatElem{S}, N::MatElem{S}, QC::MatElem{S}, row::Int, col1::Int, col2::Int) where S <: Nemo.RingElement
  @assert T[ row, col1] > 0
  @assert nrows(T) == nrows(QC)
  R = base_ring(T)
  row1 = row + 1
  t = R()
  t1 = R()
  t2 = R()
  g, a, b = gcdx(N[1, 1], N[2, 1])
  QC[row, row] = a
  QC[row, row1] = b
  QC[row1, row] = -divexact(N[2, 1], g)
  QC[row1, row1] = divexact(N[1, 1], g)
  t = deepcopy(N[1, 2])
  t1 = mul!(t1, N[1, 2], a)
  t2 = mul!(t2, N[2, 2], b)
  N[1, 2] = add!(N[1, 2], t1, t2)
  t1 = mul!(t1, QC[row1, row], t)
  t2 = mul!(t2, QC[row1, row1], N[2, 2])
  N[2, 2] = add!(N[2, 2], t1, t2)
  if N[2, 2] < 0
    QC[row1, row] = -QC[row1, row]
    QC[row1, row1] = -QC[row1, row1]
    N[2, 2] = -N[2, 2]
  end
  N[1, 1] = g
  # Make 0 below T[row, col1] and reduce below T[row1, col2]
  for i = (row + 2):nrows(T)
    if iszero(T[i, col1])
      QC[i, row] = zero!(QC[i, row])
      QC[i, row1] = zero!(QC[i, row1])
    else
      g, a, b = gcdx(N[1, 1], T[i, col1])
      g1 = divexact(N[1, 1], g)
      g2 = -divexact(T[i, col1], g)
      N[1, 1] = g
      t = deepcopy(N[1, 2])
      t1 = mul!(t1, a, N[1, 2])
      t2 = mul!(t2, b, T[i, col2])
      N[1, 2] = add!(N[1, 2], t1, t2)
      t1 = mul!(t1, g1, T[i, col2])
      t2 = mul!(t2, g2, t)
      t = add!(t, t1, t2) # this would be T[i, col2], but we don't change T here
      for c = row:row1
        QC[i, c] = mul!(QC[i, c], g2, QC[row, c])
        QC[row, c] = mul!(QC[row, c], a, QC[row, c])
      end
    end
    if t < 0 || t >= N[2, 2]
      q = -fdiv(t, N[2, 2])
      for c = row:row1
        t1 = mul!(t1, q, QC[row1, c])
        QC[i, c] = add!(QC[i, c], t1)
      end
    end
  end
  # Reduce above T[row, col1] and above T[row1, col2]
  for i = 1:row
    t = deepcopy(T[i, col2])
    if i != row && (T[i, col1] < 0 || T[i, col1] >= N[1, 1])
      q = -fdiv(T[i, col1], N[1, 1])
      t1 = mul!(t1, q, N[1, 2])
      t = add!(t, t1) # this would be T[i, col2]
      for c = row:row1
        QC[i, c] = mul!(QC[i, c], q, QC[row, c])
      end
    else
      if i != row
        QC[i, row] = zero!(QC[i, row])
        QC[i, row1] = zero!(QC[i, row1])
      end
    end
    if t < 0 || t >= N[2, 2]
      q = -fdiv(t, N[2, 2])
      for c = row:row1
        t1 = mul!(t1, q, QC[row1, c])
        QC[i, c] = add!(QC[i, c], t1)
      end
    end
  end
  return nothing
end

function hnf_storjohann_with_transform(A::MatElem{S}) where S <: Nemo.RingElement
  #timeRed = 0
  #timeProdC = 0
  #timeBuildQC = 0
  #timeProdQC = 0
  #timeU = 0
  R = base_ring(A)
  T = similar(A, nrows(A) + 2, ncols(A) + 2)
  n = nrows(T)
  m = ncols(T)
  T[1, 1] = R(1)
  T[n, m] = R(1)
  n1 = n - 1
  m1 = m - 1
  for i = 2:n1
    for j = 2:m1
      T[i, j] = deepcopy(A[i - 1, j - 1])
    end
  end
  #=
      1 0 0
  T = 0 A 0
      0 0 1
  =#
  Q = identity_matrix(R, n)
  C = identity_matrix(T, n)
  QC = identity_matrix(T, n)
  #=
  We use QC at the same time for Q_k and the product Q_k * CC.
    Q_k should be
  1 0 ... * * ... 0
  0 1 ... * * ... 0
  . . . . * * . . .
  0 0 ... * * ... 1
  Only the columns row and row + 1 (with the *'s) are saved in QC.
  The columns before row will not be reset since they are never needed again.
  =#
  N = similar(T, 2, 2)
  col1 = 1
  col2 = 0
  row = 1
  CC = Vector{S}(n)
  for i = 1:n
    CC[i] = R()
  end
  #=
  CC should be
  1 0 ..... 0
  0 1 ..... 0
  . . . . . .
  0 0 1 * * *
  . . . . . .
  0 0 0 0 0 1
  Only the "row + 1 row" (the one with the *'s) is saved here.
  =#
  zero_cols = BitArray(n) # zero_cols[i] == true iff CC[i] == 0
  non_zero_entries = Vector{Vector{Int}}(n)
  # If i is in non_zero_entries[j] then C[i, j] != 0 (but we don't
  # save j in non_zero_entries[j] although there is always a 1 on
  # the diagonal).
  for i = 1:n
    non_zero_entries[i] = Vector{Int}()
  end
  temp = Vector{S}(n)
  for i = 1:n
    temp[i] = R()
  end
  t = R()
  while col2 < m
    row1 = row + 1
    row2 = row + 2
    #tic()
    col2 = conditioning_with_transform!(T, N, CC, zero_cols, row, col1)
    column_reduction_with_transform!(T, N, QC, row, col1, col2)
    col1 = col2
    #timeRed += toq();
    # C = CC*C
    #tic()
    for i = row2:n
      if zero_cols[i]
        continue
      end
      for j = row2:i # C is upper triangular
        if iszero(C[i, j])
          continue
        end
        t = mul!(t, CC[i], C[i, j])
        C[row1, j] = add!(C[row1, j], t)
        push!(non_zero_entries[j], row1)
      end
    end
    #timeProdC += toq();
    # "QC = Q_k*CC"
    #tic()
    for j = row2:n
      if zero_cols[j]
        continue
      end
      for i = 1:n
        QC[i, j] = mul!(QC[i, j], QC[i, row1], CC[j])
        if i == j
          QC[i, j] += 1
        end
      end
    end
    #timeBuildQC += toq();
    zero_cols[row] = false
    zero_cols[row1] = false
    # Q = QC*Q
    # We only need to change the columns 1 to row1 since we already know,
    # that the columns row2 to n will eventually be an "identity matrix".
    # In particular, we don't need to compute Q*inv(CC).
    #tic()
    for j = 1:row1
      for i = row:n
        temp[i] = zero!(temp[i])
      end
      for l = row:n
        if zero_cols[l]
          temp[l] = add!(temp[l], Q[l, j])
          continue
        end
        for i = 1:row - 1
          t = mul!(t, QC[i, l], Q[l, j])
          Q[i, j] = add!(Q[i, j], t)
        end
        for i = row:n
          t = mul!(t, QC[i, l], Q[l, j])
          temp[i] = add!(temp[i], t)
        end
      end
      for i = row:n
        Q[i, j] = deepcopy(temp[i])
      end
    end
    # T = QC*T
    for j = row:m
      for i = row:n
        temp[i] = zero!(temp[i])
      end
      for l = row:n
        if zero_cols[l]
          temp[l] = add!(temp[l], T[l, j])
          continue
        end
        for i = 1:row - 1
          t = mul!(t, QC[i, l], T[l, j])
          T[i, j] = add!(T[i, j], t)
        end
        for i = row:n
          t = mul!(t, QC[i, l], T[l, j])
          temp[i] = add!(temp[i], t)
        end
      end
      for i = row:n
        T[i, j] = deepcopy(temp[i])
      end
    end
    #timeProdQC += toq();
    row += 1
  end
  #tic()
  U = deepcopy(Q)
  for j = 1:n
    if length(non_zero_entries[j]) == 0
      continue
    end
    for i = 1:n
      for l in non_zero_entries[j]
        t = mul!(t, Q[i, l], C[l, j])
        U[i, j] = add!(U[i, j], t)
      end
    end
  end
  #timeU += toq();
  #println("Time reduction: $timeRed")
  #println("Time products with CC: $timeProdC")
  #println("Time to compute QC: $timeBuildQC")
  #println("Time products with QC: $timeProdQC")
  #println("Time to compute U: $timeU")
  return sub(T, 2:n1, 2:m1), sub(Q, 2:n1, 2:n1), sub(C, 2:n1, 2:n1), sub(U, 2:n1, 2:n1)
end

function conditioning!(T::MatElem{S}, row::Int, col1::Int) where S <: Nemo.RingElement
  @assert col1 < ncols(T)
  @assert T[row, col1] > 0
  R = base_ring(T)
  row1 = row + 1
  t = R()
  t1 = R()
  t2 = R()
  col2 = 0
  for c = (col1 + 1):ncols(T)
    for i = row1:nrows(T)
      t1 = mul!(t1, T[row, col1], T[i, c])
      t2 = mul!(t2, T[row, c], T[i, col1])
      t = t1 - t2
      if !iszero(t)
        col2 = c
        # Make sure the rows row and row1 are linearly independent
        if i != row1
          for j = col1:ncols(T)
            T[row1, j] = add!(T[row1, j], T[i, j])
          end
        end
        break
      end
    end
    if col2 != 0
      break
    end
  end
  @assert col2 != 0
  if row1 == nrows(T)
    return col2
  end
  for l = row + 2:nrows(T)
    g = gcd(T[row1, col1], T[l, col1])
    if iszero(g)
      continue
    end
    q1, r1 = divrem(divexact(T[row1, col1], g), T[row, col1])
    if r1 < 0
      add!(r1, T[row, col1])
      q1 = q1 - 1
    end
    q2, r2 = divrem(divexact(T[l, col1], g), T[row, col1])
    if r2 < 0
      add!(r2, T[row, col1])
      q2 = q2 - 1
    end
    t1 = mul!(t1, T[row, col1], T[l, col2])
    t2 = mul!(t2, T[row, col2], T[l, col1])
    n = t1 - t2
    if n != 0
      t1 = mul!(t1, T[row, col1], T[row1, col2])
      t2 = mul!(t2, T[row, col2], T[row1, col1])
      nn = t2 - t1
      @assert nn != 0
      # If nn/n in Z and positive:
      if sign(n) == sign(nn) && rem(nn, n) == 0
        r2 = -r2
      end
    end
    t1 = zero!(t1)
    t2 = deepcopy(r1)
    while gcd(t2, T[row, col1]) != 1
      t2 = add!(t2, r2)
      t1 += 1
    end
    if !iszero(t1)
      if r2 < 0
        t1 = -t1
      end
      for j = col1:(ncols(T) - 1)
        t = mul!(t, T[l, j], t1)
        T[row1, j] = add!(T[row1, j], t)
      end
    end
  end
  return col2
end

function column_reduction!(T::MatElem{S}, row::Int, col1::Int, col2::Int) where S <: Nemo.RingElement
  @assert T[ row, col1] > 0
  R = base_ring(T)
  row1 = row + 1
  col11 = col1 + 1
  n = ncols(T) - 1
  t = R()
  t1 = R()
  t2 = R()
  # Make 0 below T[row, col1]
  for i = row1:nrows(T)
    if i == row1 || !iszero(T[i, col1])
      g, a, b = gcdx(T[row, col1], T[i, col1])
      c = divexact(T[row, col1], g)
      d = -divexact(T[i, col1], g)
      if i == row1
        t1 = mul!(t1, d, T[row, col2])
        t2 = mul!(t2, c, T[row1, col2])
        t = add!(t, t1, t2)
        if t < 0
          c = -c
          d = -d
        end
      end
      T[row, col1] = deepcopy(g)
      T[i, col1] = zero!(T[i, col1])
      for j = col11:n
        t = deepcopy(T[row, j])
        t1 = mul!(t1, T[row, j], a)
        t2 = mul!(t2, T[i, j], b)
        T[row, j] = add!(T[row, j], t1, t2)
        t1 = mul!(t1, T[i, j], c)
        t2 = mul!(t2, t, d)
        T[i, j] = add!(T[i, j], t1, t2)
      end
    end
  end
  # Reduce below T[row1, col2]
  for i = (row + 2):nrows(T)
    if T[i, col2] < 0 || T[i, col2] >= T[row1, col2]
      q = -fdiv(T[i, col2], T[row1, col2])
      for j = col11:n
        t = mul!(t, q, T[row1, j])
        T[i, j] = add!(T[i, j], t)
      end
    end
  end
  # Reduce above T[row, col1]
  for i = 1:(row - 1)
    if T[i, col1] < 0 || T[i, col1] >= T[row, col1]
      q = -fdiv(T[i, col1], T[row, col1])
      for j = col1:n
        t = mul!(t, q, T[row, j])
        T[i, j] = add!(T[i, j], t)
      end
    end
  end
  # Reduce above T[row1, col2]
  for i = 1:row
    if T[i, col2] < 0 || T[i, col2] >= T[row1, col2]
      q = -fdiv(T[i, col2], T[row1, col2])
      for j = col11:n
        t = mul!(t, q, T[row1, j])
        T[i, j] = add!(T[i, j], t)
      end
    end
  end
  return nothing
end

function hnf_storjohann(A::MatElem{S}) where S <: Nemo.RingElement
  R = base_ring(A)
  T = similar(A, nrows(A) + 2, ncols(A) + 2)
  n = nrows(T)
  m = ncols(T)
  T[1, 1] = R(1)
  T[n, m] = R(1)
  n1 = n - 1
  m1 = m - 1
  for i = 2:n1
    for j = 2:m1
      T[i, j] = deepcopy(A[i - 1, j - 1])
    end
  end
  #=
      1 0 0
  T = 0 A 0
      0 0 1
  =#
  col1 = 1
  col2 = 0
  row = 1
  while col2 < m
    col2 = conditioning!(T, row, col1)
    column_reduction!(T, row, col1, col2)
    col1 = col2
    row += 1
  end
  return sub(T, 2:n1, 2:m1)
end
