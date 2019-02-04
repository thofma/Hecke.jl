function _lll_gram(A::NfOrdIdl)
  K = nf(order(A))
  @assert istotally_real(K)
  g = trace_matrix(A)
  @assert det(g) != 0
  @assert isposdef(g)
  l, t = lll_gram_with_transform(g)
  return FakeFmpqMat(l, fmpz(1)), t::fmpz_mat
end

function _lll_quad(A::NfOrdIdl)
  K = nf(order(A))
  @assert degree(K) ==2 && discriminant(order(A)) < 0
  b = basis(A)
  a1 = 2*numerator(norm(b[1]))
  a2 = 2*numerator(norm(b[2]))
  a12 = numerator(trace(b[1] * conjugate_quad(K(b[2]))))
  g = matrix(FlintZZ, 2, 2, [a1, a12, a12, a2])
  @assert isposdef(g)
  l, t = lll_gram_with_transform(g)
  return FakeFmpqMat(l, fmpz(1)), t::fmpz_mat
end

function lll_basis(A::NfOrdIdl, v::fmpz_mat = zero_matrix(FlintZZ, 1, 1); prec::Int = 100)
  L, T = lll(A, v, prec=prec)
  S = FakeFmpqMat(T)*basis_mat(A)*basis_mat(order(A))
  K = nf(order(A))
  q = nf_elem[elem_from_mat_row(K, numerator(S), i, denominator(S)) for i=1:degree(K)]
  return q
end

function cmpindex(A::fmpz_mat, i::Int, j::Int, b::fmpz)
  a = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), A, i-1, j-1)
  return ccall((:fmpz_cmp, :libflint), Int32, (Ptr{fmpz}, Ref{fmpz}), a, b)
end

function prod_diag(A::fmpz_mat)
  a = fmpz()
  for i=1:nrows(A)
    b = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), A, i-1, i-1)
    ccall((:fmpz_mul, :libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ptr{fmpz}), a, a, b)
  end
  return a
end

function lll(A::NfOrdIdl, v::fmpz_mat = zero_matrix(FlintZZ, 1, 1); prec::Int = 100)


  K = nf(order(A))
  if iszero(v) && istotally_real(K)
    #in this case the gram-matrix of the minkowski lattice is the trace-matrix
    #which is exact.
    return _lll_gram(A)
  end

  if iszero(v) && degree(K) == 2 && discriminant(order(A)) < 0
    #in this case the gram-matrix of the minkowski lattice is related to the
    #trace-matrix which is exact.
    #could be extended to CM-fields
    return _lll_quad(A)
  end

  n = degree(order(A))
  prec = max(prec, 4*n)

  l, t1 = lll_with_transform(basis_mat(A, Val{false}))

  if iszero(v)
    d = minkowski_gram_mat_scaled(order(A), prec)
    ccall((:fmpz_mat_mul, :libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz_mat}), d, d, l')
    ccall((:fmpz_mat_mul, :libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz_mat}), d, l, d)
    g = zero_matrix(FlintZZ, n, n)
    den = fmpz(1)
    sv = fmpz(0)
  else
    c = minkowski_mat(nf(order(A)), prec) ## careful: current iteration
                                          ## c is NOT a copy, so don't change.
    b = FakeFmpqMat(l)*basis_mat(order(A), Val{false})


    rt_c = roots_ctx(K)
    if !isdefined(rt_c, :cache_z1)
      rt_c.cache_z1 = zero_matrix(FlintZZ, n, n)
      rt_c.cache_z2 = zero_matrix(FlintZZ, n, n)
    end

    d::fmpz_mat = rt_c.cache_z1
    g::fmpz_mat = rt_c.cache_z2

    round_scale!(g, c, prec)

    sv = fmpz(0)
    if !iszero(v)
      @v_do :ClassGroup 2 println("using inf val", v)
      c = deepcopy(c)
      mult_by_2pow_diag!(c, v)
      sv = max(fmpz(0), sum(v[1,i] for i=1:ncols(l)))
    end


    round_scale!(d, c, prec)
    ccall((:fmpz_mat_mul, :libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat},  Ref{fmpz_mat}), g, (b.num), d)
    den = b.den

    ccall((:fmpz_mat_gram, :libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}), d, g)
    shift!(d, -prec)
  end

  prec = div(prec, 2)
  shift!(d, -prec)  #TODO: remove?

  for i=1:n
    fmpz_mat_entry_add_ui!(d, i, i, UInt(nrows(d)))
  end

  ctx=Nemo.lll_ctx(0.99, 0.51, :gram)

  ccall((:fmpz_mat_one, :libflint), Nothing, (Ref{fmpz_mat}, ), g)
  ccall((:fmpz_lll, :libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{Nemo.lll_ctx}), d, g, ctx)

  l, t = d, g
  ## test if entries in l are small enough, if not: increase precision
  ## or signal that prec was too low
  @v_do :ClassGroup 2 printstyled("lll basis length profile\n", color=:green);
  @v_do :ClassGroup 2 for i=1:nrows(l)
    print(Float64(div(l[i,i], fmpz(2)^prec*den*den)*1.0), " : ")
  end
  @v_do :ClassGroup 2 println("")
  if nbits(maximum(abs, t)) >  div(prec, 2)
    @v_do :ClassGroup 2 printstyled("lll trafo too large\n", color=:red);
    throw(LowPrecisionLLL())
  end
  ## lattice has lattice disc = order_disc * norm^2
  ## lll needs to yield a basis sth
  ## l[1,1] = |b_i|^2 <= 2^((n-1)/2) disc^(1/n)  
  ## and prod(l[i,i]) <= 2^(n(n-1)/2) disc
  n = nrows(l)
  disc = abs(discriminant(order(A)))*norm(A)^2 * den^(2*n) * fmpz(2)^(2*sv)
  di = root(disc, n)+1
  di *= fmpz(2)^(div(n+1,2)) * fmpz(2)^prec

  if cmpindex(l, 1, 1, di) > 0 
    @v_do :ClassGroup 2 printstyled("LLL basis too large\n", color = :red);
    @v_do :ClassGroup 3 println("bound is ", di, " value at ", 1, " is ", l[1,1]); 
    throw(LowPrecisionLLL())
  end
  pr = prod_diag(l)
  if pr > fmpz(2)^(div(n*(n-1), 2)) * disc * fmpz(2)^(n*prec)
    @v_do :ClassGroup 2 printstyled("LLL basis too large\n", color = :red);
    @v_do :ClassGroup 2 println("prod too large: ", pr, " > 2^(n(n-1)/2) disc = ", fmpz(2)^(div(n*(n-1), 2)) * disc * fmpz(2)^(n*prec));
    throw(LowPrecisionLLL())
  end

  return FakeFmpqMat(deepcopy(l), fmpz(2)^prec), t*t1
end

function short_elem(A::NfOrdFracIdl,
                v::fmpz_mat=zero_matrix(FlintZZ, 1,1); prec::Int = 100)
  return divexact(short_elem(A.num, v, prec = prec), A.den)
end
function _short_elem(A::NfOrdFracIdl,
                v::fmpz_mat=zero_matrix(FlintZZ, 1, 1))
  return divexact(_short_elem(A.num, v), A.den)
end

function short_elem(A::NfOrdIdl,
                v::fmpz_mat = zero_matrix(FlintZZ, 1,1); prec::Int = 100)
  K = nf(order(A))
  temp = FakeFmpqMat(basis_mat(A))*basis_mat(order(A))
  b = temp.num
  b_den = temp.den
  local t
  while true
    if prec > 2^18
      error("Something wrong in short_elem")
    end
    try
      l, t = lll(A, v, prec = prec)
      break
    catch e
      if !(e isa LowPrecisionLLL || e isa InexactError)
        rethrow(e)
      end
    end
    prec = 2 * prec
  end

  w = view(t, 1,1, 1, ncols(t))
  c = w*b
  q = elem_from_mat_row(K, c, 1, b_den)
  return q
end

function _short_elem(A::NfOrdIdl,
                v::fmpz_mat = zero_matrix(FlintZZ, 1, 1))
  p = 64
  while true
    if p > 40000
      error("Something wrong in reduce_ideal")
    end
    try
      b = short_elem(A, v, prec = p)
      return b
    catch e
      if e isa LowPrecisionLLL || e isa InexactError
        p = 2*p
      else
        rethrow(e)
      end
    end
  end
end

function reduce_ideal(A::NfOrdIdl)
  B = inv(A)
  success = false
  b = _short_elem(B)
  C = b*A
  simplify(C)
  @assert C.den == 1
  return C.num
end

function reduce_ideal(A::NfOrdFracIdl)
  B = inv(A)
  b = _short_elem(B.num)
  C = divexact(b, B.den)*A
  simplify(C)
  @assert C.den == 1
  return C.num
end

function reduce_ideal2(A::NfOrdIdl)
  B = inv(A)
  b = _short_elem(B)
  C = b*A
  simplify(C)
  @assert C.den == 1
  return C.num, b
end

