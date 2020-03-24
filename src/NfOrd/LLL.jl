add_verbose_scope(:LLL)
add_assert_scope(:LLL)

################################################################################
#
#  Special functions for real fields and quadratic fields
#
################################################################################

function _lll_gram(A::NfOrdIdl)
  K = nf(order(A))
  @assert istotally_real(K)
  g = trace_matrix(A)
  @hassert :LLL 1 !iszero(det(g))
  @hassert :LLL 1 isposdef(g)
  l, t = lll_gram_with_transform(g)
  return FakeFmpqMat(l, fmpz(1)), t::fmpz_mat
end

function _lll_quad(A::NfOrdIdl)
  K = nf(order(A))
  @assert degree(K) == 2 && discriminant(order(A)) < 0
  b = basis(A)
  a1 = 2*numerator(norm(b[1]))
  a2 = 2*numerator(norm(b[2]))
  a12 = numerator(trace(b[1] * conjugate_quad(K(b[2]))))
  g = matrix(FlintZZ, 2, 2, [a1, a12, a12, a2])
  @hassert :LLL 1 isposdef(g)
  l, t = lll_gram_with_transform(g)
  return FakeFmpqMat(l, fmpz(1)), t::fmpz_mat
end

function _lll_CM(A::NfOrdIdl, f::NfToNfMor)
  OK = order(A)
  @vprint :LLL 3 "Reduction\n"
  M = _minkowski_matrix_CM(OK, f)
  @vtime :LLL 3 BM, T = lll_with_transform(basis_matrix(A, copy = false), lll_ctx(0.71, 0.51))
  g = BM*M*transpose(BM)
  @hassert :LLL 1 isposdef(g)
  @vtime :LLL 3 l, t = lll_gram_with_transform(g)
  return FakeFmpqMat(l, fmpz(1)), t*T::fmpz_mat
end

################################################################################
#
#  lll for ideals
#
################################################################################

function lll(A::NfOrdIdl, v::fmpz_mat = zero_matrix(FlintZZ, 1, 1); prec::Int = 100)

  K = nf(order(A))

  if iszero(v) 
    if istotally_real(K)
      #in this case the gram-matrix of the minkowski lattice is the trace-matrix
      #which is exact.
      return _lll_gram(A)
    elseif degree(K) == 2 && discriminant(order(A)) < 0
       #in this case the gram-matrix of the minkowski lattice is related to the
      #trace-matrix which is exact.
      return _lll_quad(A)
    elseif isautomorphisms_known(K)
      fl, f_conj = iscm_field(K)
      if fl
        return _lll_CM(A, f_conj)
      end
    end
  end

  n = degree(order(A))
  prec = max(prec, 4*n)

  l, t1 = lll_with_transform(basis_matrix(A, copy = false))

  if iszero(v)
    d = minkowski_gram_mat_scaled(order(A), prec)
    ccall((:fmpz_mat_mul, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz_mat}), d, d, l')
    ccall((:fmpz_mat_mul, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz_mat}), d, l, d)
    g = zero_matrix(FlintZZ, n, n)
    den = fmpz(1)
    sv = fmpz(0)
  else
    c = minkowski_matrix(nf(order(A)), prec) ## careful: current iteration
                                          ## c is NOT a copy, so don't change.
    b = l*basis_matrix(order(A), copy = false)


    rt_c = roots_ctx(K)
    if !isdefined(rt_c, :cache_z1)
      rt_c.cache_z1 = zero_matrix(FlintZZ, n, n)
      rt_c.cache_z2 = zero_matrix(FlintZZ, n, n)
    end

    d::fmpz_mat = rt_c.cache_z1
    g::fmpz_mat = rt_c.cache_z2

    round_scale!(g, c, prec)

    @v_do :ClassGroup 2 println("using inf val", v)
    c = deepcopy(c)
    mult_by_2pow_diag!(c, v)
    sv = max(fmpz(0), sum(v[1,i] for i=1:ncols(l)))


    round_scale!(d, c, prec)
    ccall((:fmpz_mat_mul, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat},  Ref{fmpz_mat}), g, (b.num), d)
    den = b.den

    ccall((:fmpz_mat_gram, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}), d, g)
    shift!(d, -prec)
  end

  prec = div(prec, 2)
  shift!(d, -prec)  #TODO: remove?

  for i=1:n
    fmpz_mat_entry_add_ui!(d, i, i, UInt(nrows(d)))
  end

  ctx = Nemo.lll_ctx(0.99, 0.51, :gram)

  ccall((:fmpz_mat_one, libflint), Nothing, (Ref{fmpz_mat}, ), g)
  ccall((:fmpz_lll, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{Nemo.lll_ctx}), d, g, ctx)

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

  if compare_index(l, 1, 1, di) > 0 
    @v_do :ClassGroup 2 printstyled("LLL basis too large\n", color = :red);
    @v_do :ClassGroup 3 println("bound is ", di, " value at ", 1, " is ", l[1,1]); 
    throw(LowPrecisionLLL())
  end
  pr = prod_diagonal(l)
  if pr > fmpz(2)^(div(n*(n-1), 2)) * disc * fmpz(2)^(n*prec)
    @v_do :ClassGroup 2 printstyled("LLL basis too large\n", color = :red);
    @v_do :ClassGroup 2 println("prod too large: ", pr, " > 2^(n(n-1)/2) disc = ", fmpz(2)^(div(n*(n-1), 2)) * disc * fmpz(2)^(n*prec));
    throw(LowPrecisionLLL())
  end

  return FakeFmpqMat(deepcopy(l), fmpz(2)^prec), t*t1
end


###############################################################################
#
#  LLL computation for orders
#
###############################################################################

@doc Markdown.doc"""
    lll(M::NfOrd) -> NfOrd
The same order, but with the basis now being LLL reduced wrt. the Minkowski metric.
"""
function lll(M::NfOrd; prec::Int = 100)
  
  if isdefined(M, :lllO)
    return M.lllO::NfOrd
  end
  K = nf(M)

  if istotally_real(K)
    On =  _lll_gram(M)
    M.lllO = On
    return On::NfOrd
  end
  
  if degree(K) == 2
    On = _lll_quad(M)
    M.lllO = On
    return On::NfOrd
  end
  
  if isautomorphisms_known(K)
    fl, f_conj = iscm_field(K)
    if fl
      On = _lll_CM(M, f_conj)
      M.lllO = On
      return On
    end
  end
  
  return _lll(M, prec)
end
# don't know what this is doing
#for totally real field, the T_2-Gram matrix is the trace matrix, hence exact.

function _lll_gram(M::NfOrd)
  K = nf(M)
  @assert istotally_real(K)
  g = trace_matrix(M)

  w = lll_gram_with_transform(g)[2]
  On = NfOrd(K, w*basis_matrix(M, copy = false))
  On.ismaximal = M.ismaximal
  if isdefined(M, :index)
    On.index = M.index
  end
  if isdefined(M, :disc)
    On.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On.gen_index = M.gen_index
  end
  return On
end

function _minkowski_matrix_CM(M::NfOrd, f::NfToNfMor)
  if isdefined(M,  :minkowski_gram_CMfields)
    return M.minkowski_gram_CMfields
  end
  K = nf(M)
  b = basis(M, K)
  n = degree(M)
  @vprint :LLL 1 "Computing the gram matrix\n"
  g = zero_matrix(FlintZZ, n, n)
  conjs = nf_elem[f(x) for x in b]
  for i = 1:n
    g[i, i] = numerator(trace(b[i] * conjs[i]))
    for j = i+1:n
      el = numerator(trace(b[i] * conjs[j]))
      g[i, j] = el
      g[j, i] = el
    end
  end
  M.minkowski_gram_CMfields = g
  return g
end

function _lll_CM(M::NfOrd, f::NfToNfMor)
  K = nf(M)
  g = _minkowski_matrix_CM(M, f)
  @vprint :LLL 1 "Now LLL\n"
  @hassert :LLL 1 isposdef(g)
  w = lll_gram_with_transform(g)[2]
  On = NfOrd(K, w*basis_matrix(M, copy = false))
  On.ismaximal = M.ismaximal
  if isdefined(M, :index)
    On.index = M.index
  end
  if isdefined(M, :disc)
    On.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On.gen_index = M.gen_index
  end
  return On
end


function _lll_quad(M::NfOrd)
  K = nf(M)
  b = basis(M)
  a1 = 2*numerator(norm(b[1]))
  a2 = 2*numerator(norm(b[2]))
  a12 = numerator(trace(b[1] * conjugate_quad(K(b[2]))))
  g = matrix(FlintZZ, 2, 2, fmpz[a1, a12, a12, a2])
  @hassert :ClassGroup 1 isposdef(g)
  w = lll_gram_with_transform(g)[2]
  On = NfOrd(K, w*basis_matrix(M, copy = false))
  On.ismaximal = M.ismaximal
  if isdefined(M, :index)
    On.index = M.index
  end
  if isdefined(M, :disc)
    On.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On.gen_index = M.gen_index
  end
  return On
end

function _lll(M::NfOrd, prec::Int)

  K = nf(M)
  n = degree(K)
  M1 = _ordering_by_T2(M)
  prec = max(prec, 10*n)
  prec = max(prec, 100 + 25*div(degree(M), 3) + Int(round(log(abs(discriminant(M))))))
  
  if n > 10
    prec, M1 = lll_precomputation(M1, prec)
  end
  M1, prec = _lll_with_parameters(M1, (0.75, 0.51), prec)
  M1 = _lll_with_parameters(M1, (0.99, 0.51), prec)[1]
  M.lllO = M1
  return M1
end

function _ordering_by_T2(M::NfOrd)
  
  K = nf(M)
  B = basis(M, K)
  ints = fmpz[lower_bound(t2(x), fmpz) for x in B]
  p = sortperm(ints)
  On = NfOrd(B[p])
  On.ismaximal = M.ismaximal
  if isdefined(M, :index)
    On.index = M.index
  end
  if isdefined(M, :disc)
    On.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On.gen_index = M.gen_index
  end
  return On
end

function lll_precomputation(M::NfOrd, prec::Int)

  n = degree(M)
  K = nf(M)
  natt = div(n, 2)
  g = identity_matrix(FlintZZ, n)
  new_prec = prec
  block = 1
  while block < 3
    @vprint :LLL 3 "Simplifying block $(block)\n"
    if block == 1
      rg = collect(1:natt)
    else
      rg = collect((natt+1):n)
    end
    new_prec, g1 = _lll_sublattice(M, rg, prec = prec)
    _copy_matrix_into_matrix(g, first(rg), first(rg), g1)
    if new_prec == prec
      block += 1
    else
      prec = new_prec
    end
  end
  @vprint :LLL 3 "Precision: $(new_prec)\n"
  On = NfOrd(K, g*basis_matrix(M, copy = false))
  On.ismaximal = M.ismaximal
  if isdefined(M, :index)
    On.index = M.index
  end
  if isdefined(M, :disc)
    On.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On.gen_index = M.gen_index
  end
  #In pratice, we have changed the main diagonal blocks of the gram matrix. 
  #Now, we do the other blocks
  g = identity_matrix(FlintZZ, n)
  new_prec = prec
  block = 1
  natt = div(n, 4)
  first_part = 1:natt
  second_part = (natt+1):(2*natt)
  third_part = (2*natt+1):3*natt
  fourth_part = (3*natt+1):n
  while block < 3
    @vprint :LLL 3 "Simplifying block $(block)\n"
    if block == 1
      b1 = first_part
      b2 = third_part
    else
      b1 = second_part
      b2 = fourth_part
    end
    rg = vcat(b1, b2)
    new_prec, g1 = _lll_sublattice(On, rg, prec = prec)
    _copy_matrix_into_matrix(g, first(b1), first(b1), view(g1, 1:length(b1), 1:length(b1)))
    _copy_matrix_into_matrix(g, first(b1), first(b2), view(g1, 1:length(b1), length(b1)+1:length(rg)))
    _copy_matrix_into_matrix(g, first(b2), first(b2), view(g1, length(b1)+1:length(rg), length(b1)+1:length(rg)))
    _copy_matrix_into_matrix(g, first(b2), first(b1), view(g1, length(b1)+1:length(rg), 1:length(b1)))
    if new_prec == prec
      block += 1
    else
      prec = new_prec
    end
  end
  @vprint :LLL 3 "Precision: $(new_prec)\n"
  On1 = NfOrd(K, g*basis_matrix(On, copy = false))
  On1.ismaximal = M.ismaximal
  if isdefined(M, :index)
    On1.index = M.index
  end
  if isdefined(M, :disc)
    On1.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On1.gen_index = M.gen_index
  end
  g = identity_matrix(FlintZZ, n)
  block = 1
  while block < 3
    @vprint :LLL 3 "Simplifying block $(block)\n"
    if block == 1
      b1 = first_part
      b2 = fourth_part
    else
      b1 = second_part
      b2 = third_part
    end
    rg = vcat(b1, b2)
    new_prec, g1 = _lll_sublattice(On1, rg, prec = prec)
    _copy_matrix_into_matrix(g, first(b1), first(b1), view(g1, 1:length(b1), 1:length(b1)))
    _copy_matrix_into_matrix(g, first(b1), first(b2), view(g1, 1:length(b1), length(b1)+1:length(rg)))
    _copy_matrix_into_matrix(g, first(b2), first(b2), view(g1, length(b1)+1:length(rg), length(b1)+1:length(rg)))
    _copy_matrix_into_matrix(g, first(b2), first(b1), view(g1, length(b1)+1:length(rg), 1:length(b1)))
    if new_prec == prec
      block += 1
    else
      prec = new_prec
    end
  end
  On2 = NfOrd(K, g*basis_matrix(On1, copy = false))
  On2.ismaximal = M.ismaximal
  if isdefined(M, :index)
    On2.index = M.index
  end
  if isdefined(M, :disc)
    On2.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On2.gen_index = M.gen_index
  end
  @vprint :LLL 3 "Precomputation finished with precision $(prec)\n"
  return prec, On2
end



function _lll_sublattice(M::NfOrd, u::Vector{Int}; prec = 100)
  K = nf(M)
  n = degree(M)
  l = length(u)
  prec = max(prec, 10*n)
  local g::fmpz_mat
  local d::fmpz_mat
  ctx = Nemo.lll_ctx(0.99, 0.51, :gram)
  att = 0 
  #TODO: If one can compute the exact discriminant of the lattice, we could check correctness. 
  # At the moment it is just heuristic.
  while true
    att += 1
    @vprint :LLL 3 "Attempt number : $(att)\n"  
    while true
      try
        d = minkowski_gram_mat_scaled(M, prec)
        break
      catch e
        prec = prec*2
      end
    end
    @vprint :Simplify 3 "Minkowski matrix computed\n"
    g = identity_matrix(FlintZZ, l)
    d1 = sub(d, u, u)
    prec = div(prec, 2)
    shift!(d1, -prec)  #TODO: remove?

    for i=1:l
      fmpz_mat_entry_add_ui!(d1, i, i, UInt(l))
    end
    @vtime :LLL 3 ccall((:fmpz_lll, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{Nemo.lll_ctx}), d1, g, ctx)

    if nbits(maximum(abs, g)) <= div(prec, 2)
      prec *= 2
      break
    end
    @vprint :LLL 3 "Still in the loop\n"
    prec *= 4
  end
  return prec, g
end


function _lll_with_parameters(M::NfOrd, parameters::Tuple{Float64, Float64}, prec)

  K = nf(M)
  n = degree(M)
  prec = max(prec, 10*n)
  disc = abs(discriminant(M))
  local g::fmpz_mat
  local d::fmpz_mat
  ctx = Nemo.lll_ctx(parameters[1], parameters[2], :gram)
  att = 0 
  while true
    att += 1
    if att > 3 
      @vprint :LLL "Having a hard time computing a LLL basis"
    end
    @vprint :LLL 3 "Attempt number : $(att)\n"
    while true
      try
        d = minkowski_gram_mat_scaled(M, prec)
        break
      catch e
        prec = prec*2
      end
    end
    @vprint :LLL 3 "Minkowski matrix computed\n"
    diag_d = prod_diagonal(d)
    g = identity_matrix(FlintZZ, n)
    
    prec = div(prec, 2)
    shift!(d, -prec)  #TODO: remove?

    for i=1:n
      fmpz_mat_entry_add_ui!(d, i, i, UInt(nrows(d)))
    end
    @vtime :LLL 3 ccall((:fmpz_lll, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{Nemo.lll_ctx}), d, g, ctx)
    
    if nbits(maximum(abs, g)) <= div(prec, 2)
      fl = true
      disc = abs(discriminant(M))
      di = root(disc, n)+1
      di *= fmpz(2)^(div(n+1,2)+prec)
      if compare_index(d, 1, 1, di) > 0
        fl = false
      else
        pr = prod_diagonal(d)
        if pr > fmpz(2)^(div(n*(n-1), 2)+(n*prec)) * disc 
          fl = false
        end
      end
      if fl
        break
      end
    end
    On = NfOrd(K, g*basis_matrix(M, copy = false))
    On.ismaximal = M.ismaximal
    if isdefined(M, :index)
      On.index = M.index
    end
    if isdefined(M, :disc)
      On.disc = M.disc
    end
    if isdefined(M, :gen_index)
      On.gen_index = M.gen_index
    end
    prec *= 2
    local d1::fmpz_mat
    while true
      try
        d1 = minkowski_gram_mat_scaled(On, prec)
        break
      catch e
        prec = prec+10
      end
    end
    if prod_diagonal(d1) < diag_d
      @vprint :LLL 3 "I use the transformation\n"
      M = On
    else
      prec *= 2
    end
    @vprint :LLL 3 "Still in the loop\n"
  end
  
  On = NfOrd(K, g*basis_matrix(M, copy = false))
  On.ismaximal = M.ismaximal
  if isdefined(M, :index)
    On.index = M.index
  end
  if isdefined(M, :disc)
    On.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On.gen_index = M.gen_index
  end
  @vprint :LLL 3 "LLL finished with parameters $(parameters)\n"
  return On, prec
end

################################################################################
#
#  Applications
#
################################################################################

@doc Markdown.doc"""
    lll_basis(M::NfOrd) -> Array{nf_elem, 1}
A basis for $M$ that is reduced using the LLL algorithm for the Minkowski metric.
"""
function lll_basis(M::NfOrd)
  M1 = lll(M)
  return basis(M1, nf(M1))
end

@doc Markdown.doc"""
    lll_basis(I::NfOrdIdl) -> Array{nf_elem, 1}
A basis for $I$ that is reduced using the LLL algorithm for the Minkowski metric.
"""
function lll_basis(A::NfOrdIdl, v::fmpz_mat = zero_matrix(FlintZZ, 1, 1); prec::Int = 100)
  L, T = lll(A, v, prec=prec)
  S = FakeFmpqMat(T)*basis_matrix(A)*basis_matrix(order(A))
  K = nf(order(A))
  q = nf_elem[elem_from_mat_row(K, numerator(S), i, denominator(S)) for i=1:degree(K)]
  return q
end

function short_elem(A::NfOrdFracIdl,
                v::fmpz_mat=zero_matrix(FlintZZ, 1,1); prec::Int = 100)
  return divexact(short_elem(A.num, v, prec = prec), A.den)
end


function short_elem(A::NfOrdIdl,
                v::fmpz_mat = zero_matrix(FlintZZ, 1,1); prec::Int = 100)
  K = nf(order(A))
  temp = basis_matrix(A, copy = false)*basis_matrix(order(A), copy = false)
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

  w = view(t, 1:1, 1:ncols(t))
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
  return C.num, b
end

function reduce_ideal(A::NfOrdFracIdl)
  B = inv(A)
  b = short_elem(B.num)
  C = divexact(b, B.den)*A
  simplify(C)
  @assert C.den == 1
  return C.num, divexact(b, B.den)
end


################################################################################
#
#  Short basis of product of ideals
#
################################################################################

function lll_basis_product(I::NfOrdIdl, J::NfOrdIdl)

  @time A = lll(I)[2]*basis_matrix(I, copy = false)
  @time IJ = I*J
  @time C = basis_matrix(IJ, copy = false)
  @time T = (C * FakeFmpqMat(pseudo_inv(A))).num
  @time T1 = lll(T)
  new_basis_IJ = T1*A
  IJ = NfOrdIdl(order(I), new_basis_IJ)
  @time res =  lll_basis(IJ)
  return res
end

