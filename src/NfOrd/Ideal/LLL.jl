function _lll_gram(A::NfOrdIdl)
  K = nf(order(A))
  @assert istotally_real(K)
  g = trace_matrix(A)
  @assert det(g) != 0
  @assert isposdef(g)
  l, t = lll_gram_with_transform(g)
  return FakeFmpqMat(l, fmpz(1)), t
end

function lll_basis(A::NfOrdIdl, v::fmpz_mat = zero_matrix(FlintZZ, 1, 1); prec::Int = 100)
  L, T = lll(A, v, prec=prec)
  S = FakeFmpqMat(T)*basis_mat(A)*basis_mat(order(A))
  K = nf(order(A))
  q = nf_elem[elem_from_mat_row(K, num(S), i, den(S)) for i=1:degree(K)]
  return q
end

function lll(A::NfOrdIdl, v::fmpz_mat = zero_matrix(FlintZZ, 1, 1); prec::Int = 100)

  K = nf(order(A))
  if iszero(v) && istotally_real(K)
    #in this case the gram-matrix of the minkowski lattice is the trace-matrix
    #which is exact.
    return _lll_gram(A)
  end  

  c = minkowski_mat(nf(order(A)), prec) ## careful: current iteration
                                        ## c is NOT a copy, so don't change.
  l, t1 = lll_with_transform(basis_mat(A))
  b = FakeFmpqMat(l)*basis_mat(order(A))

  n = degree(order(A))

  rt_c = roots_ctx(K)
  if !isdefined(rt_c, :cache_z1)
    rt_c.cache_z1 = zero_matrix(FlintZZ, n, n)
    rt_c.cache_z2 = zero_matrix(FlintZZ, n, n)
  end
  
  d = rt_c.cache_z1
  g = rt_c.cache_z2

  sv = fmpz(0)
  if !iszero(v)
    @v_do :ClassGroup 2 println("using inf val", v)
    c = deepcopy(c)
    mult_by_2pow_diag!(c, v)
    sv = max(fmpz(0), sum(v[1,i] for i=1:cols(l)))
  end


  round_scale!(d, c, prec)
  ccall((:fmpz_mat_mul, :libflint), Void, (Ptr{fmpz_mat}, Ptr{fmpz_mat},  Ptr{fmpz_mat}), &g, &(b.num), &d)
  den = b.den

  ccall((:fmpz_mat_gram, :libflint), Void, (Ptr{fmpz_mat}, Ptr{fmpz_mat}), &d, &g)
  shift!(d, -prec)
  prec = div(prec, 2)
  shift!(d, -prec)  #TODO: remove?

  for i=1:n
    fmpz_mat_entry_add_ui!(d, i, i, UInt(rows(d)))
  end

  ctx=Nemo.lll_ctx(0.99, 0.51, :gram)

  ccall((:fmpz_mat_one, :libflint), Void, (Ptr{fmpz_mat}, ), &g)
  ccall((:fmpz_lll, :libflint), Void, (Ptr{fmpz_mat}, Ptr{fmpz_mat}, Ptr{Nemo.lll_ctx}), &d, &g, &ctx)

  l, t = d, g
  ## test if entries in l are small enough, if not: increase precision
  ## or signal that prec was too low
  @v_do :ClassGroup 3 print_with_color(:green, "lll basis length profile\n");
  @v_do :ClassGroup 3 for i=1:rows(l)
    print(div(l[i,i], fmpz(2)^prec), " : ")
  end
  @v_do :ClassGroup 3 println("")
  if nbits(max(t)) >  div(prec, 2)
    @v_do :ClassGroup 2 print_with_color(:red, "lll trafo too large\n");
    throw(LowPrecisionLLL())
  end
  ## lattice has lattice disc = order_disc * norm^2
  ## lll needs to yield a basis sth
  ## l[1,1] = |b_i|^2 <= 2^((n-1)/2) disc^(1/n)  
  ## and prod(l[i,i]) <= 2^(n(n-1)/2) disc
  n = rows(l)
  disc = abs(discriminant(order(A)))*norm(A)^2 * den^(2*n) * fmpz(2)^(2*sv)
  d = root(disc, n)+1
  d *= fmpz(2)^(div(n+1,2)) * fmpz(2)^prec
  pr = fmpz(1)
  if l[1,1] > d 
    @v_do :ClassGroup 2 print_with_color(:red, "LLL basis too large\n");
    @v_do :ClassGroup 3 println("bound is ", d, " value at ", 1, " is ", l[1,1]); 
    throw(LowPrecisionLLL())
  end
  for i=1:n
    pr = pr*l[i,i]
  end  
  if pr > fmpz(2)^(div(n*(n-1), 2)) * disc * fmpz(2)^(n*prec)
    @v_do :ClassGroup 2 print_with_color(:red, "LLL basis too large\n");
    @v_do :ClassGroup 2 println("prod too large: ", pr, " > 2^(n(n-1)/2) disc = ", fmpz(2)^(div(n*(n-1), 2)) * disc * fmpz(2)^(n*prec));
    throw(LowPrecisionLLL())
  end

  return FakeFmpqMat(deepcopy(l), fmpz(2)^prec), t*t1
end

function short_elem(A::NfOrdFracIdl,
                v::fmpz_mat=zero_matrix(FlintZZ, 1,1); prec::Int = 100)
  return divexact(short_elem(A.num, v, prec = prec), A.den)
end

function short_elem(A::NfOrdIdl,
                v::fmpz_mat = zero_matrix(FlintZZ, 1,1); prec::Int = 100)
  K = nf(order(A))
  temp = FakeFmpqMat(basis_mat(A))*basis_mat(order(A))
  b = temp.num
  b_den = temp.den
  l, t = lll(A, v, prec = prec)
  w = view(t, 1,1, 1, cols(t))
  c = w*b
  q = elem_from_mat_row(K, c, 1, b_den)
  return q
end

function reduce_ideal(A::NfOrdIdl)
  B = inv(A)
  b = short_elem(B)
  C = b*A
  simplify(C)
  @assert C.den == 1
  return C.num
end  

function reduce_ideal(A::NfOrdFracIdl)
  B = inv(A)
  b = short_elem(B.num)
  C = divexact(b, B.den)*A
  simplify(C)
  @assert C.den == 1
  return C.num
end  

function reduce_ideal2(A::NfOrdIdl)
  B = inv(A)
  b = short_elem(B)
  C = b*A
  simplify(C)
  @assert C.den == 1
  return C.num, b
end  

