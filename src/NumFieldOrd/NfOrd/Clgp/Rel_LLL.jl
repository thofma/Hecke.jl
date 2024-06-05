function NormCtx(O::AbsNumFieldOrder, nb::Int, normal::Bool = false)
  if normal
    return NormCtx_split(O, nb)
  else
    if degree(O) > 20
      return NormCtx_gen(O, nb)
    else
      return NormCtx_simple(O, nb)
    end
  end
end

function norm(m::ZZMatrix, NC::NormCtx_split, div::ZZRingElem = ZZRingElem(1))
  l = Vector{ZZRingElem}()
  for i = 1:length(NC.lp)
    ccall((:fmpz_mat_get_nmod_mat, libflint), Cvoid, (Ref{fpMatrix}, Ref{ZZMatrix}), NC.mp[i], m)
    mul!(NC.np[i], NC.mp[i], NC.lC[i])
    n = NC.np[i]
    p = n[1,1]
    for j=2:ncols(m)
      p *= n[1,j]
    end
    push!(l, lift(inv(NC.lR[i](div))*p))
  end
  no = crt_signed(l, NC.e)
  if nbits(no) > NC.nb - 10
    return nothing
  else
    O = NC.O
    k = nf(O)
#    @assert no *div == norm(O(ZZRingElem[m[1, i] for i = 1:degree(k)]).elem_in_nf)
    return no
  end
end

function norm(a::ZZMatrix, NC::NormCtx_gen, div::ZZRingElem = ZZRingElem(1))
  O = NC.O
  k = nf(O)
  l = Vector{ZZRingElem}()
  for i=1:length(NC.lp)
    ccall((:fmpz_mat_get_nmod_mat, libflint), Cvoid, (Ref{fpMatrix}, Ref{ZZMatrix}), NC.mp[i], a)
    mul!(NC.np[i], NC.mp[i], NC.basis[i])
    gp = NC.gp[i]
    for j=1:degree(k)
      ccall((:nmod_poly_set_coeff_ui, libflint), Nothing,
      (Ref{fpPolyRingElem}, Int, UInt), gp, j - 1, NC.np[i][1,j].data)
    end
    push!(l, lift(resultant(NC.fp[i], gp)//div))
  end

  no = crt_signed(l, NC.e)
  if nbits(no) > NC.nb-10
    return nothing
  else
#    global last_bad = (a, NC, div)
#    @assert no *div == norm(O(ZZRingElem[a[1, i] for i = 1:degree(k)]).elem_in_nf)
    return no
  end
end

function norm(a::ZZMatrix, NC::NormCtx_simple, div::ZZRingElem = ZZRingElem(1))
  O = NC.O
  k = nf(O)
  no = numerator(norm_div(O(ZZRingElem[a[1, i] for i = 1:degree(k)]).elem_in_nf, div, NC.nb))
  if nbits(no) > NC.nb-10
    return nothing
  else
#    @assert no *div == norm(O(ZZRingElem[a[1, i] for i = 1:degree(k)]).elem_in_nf)
    return no
  end
end

function class_group_small_lll_elements_relation_start(clg::ClassGrpCtx{T},
                O::AbsSimpleNumFieldOrder; prec::Int = 200, val::Int = 0,
                limit::Int = 0) where {T}
  return class_group_small_lll_elements_relation_start(clg, ideal(O, parent(basis_matrix(FakeFmpqMat, O).num)(1)), prec = prec)
end

function class_group_small_lll_elements_relation_start(clg::ClassGrpCtx{T},
                A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}; prec::Int = 200, val::Int = 0,
                limit::Int = 0) where {T}
  O = order(A)
  n = degree(O)
  L, Tr = lll(A, prec = prec)
  I = SmallLLLRelationsCtx(zero_matrix(FlintZZ, 1, 1))
  S = Tr*basis_matrix(A, copy = false)
  bd = abs(discriminant(O))*norm(A)^2
  bd = root(bd, n, check = false)
  bd *= L.den
  f = Int[i for i = 1:n if compare_index(L.num, i, i, bd) < 0]
  m = div(n, 4)
  if m < 2
    m = n
  end
  while length(f) < m
    f = Int[i for i = 1:n if compare_index(L.num, i, i, bd) < 0]
    bd *= 2
  end
  I.b = Vector{ZZMatrix}(undef, length(f))
  for j = 1:length(f)
    I.b[j] = view(S, f[j]:f[j], 1:ncols(S))
  end
  #println([Float64(numerator(L)[i,i]//denominator(L)*1.0) for i=1:degree(K)])
  #now select a subset that can yield "small" relations, where
  #small means of effective norm <= sqrt(disc)
  I.A = A
  I.elt = zero_matrix(FlintZZ, 1, n)
  return I
end

function class_group_small_lll_elements_relation_next(I::SmallLLLRelationsCtx)
  #the 1st n relations are the basis elements
  if I.cnt < length(I.b)
    I.cnt += 1
    I.elt = I.b[I.cnt]
    return deepcopy(I.b[I.cnt])
  end
  #the next 2*n*(n-1)/2 relations are the ones of weight 2
  #1st b[i] + b[j], all combinations, then b[i]-b[j]
  #it may (or may not) be helpful
  if I.cnt <= length(I.b)^2
    n = length(I.b)
    c = I.cnt - n # we already did n relations in the 1st if
    if c > n*(n-1)/2
      c -= div(n*(n-1), 2)
      s = -1
    else
      s = 1
    end
    i = 1
    while c+i-1 >= n
      c -= (n-i)
      i += 1
    end
    I.cnt += 1
    I.elt = I.b[i] + s*I.b[c+i]
    return I.elt
  end

  if I.cnt > (2*I.bd+1)^div(length(I.b), 2)
    I.bd += 1
  end

  I.cnt += 1
  while true
    # Before: rand!(I.elt, I.b, -I.bd:I.bd, min(length(I.b), 5))
    # TODO: make this non-allocating
    I.elt = rand(-I.bd:I.bd) * rand(I.b)
    for i in 2:min(length(I.b), 5)
      I.elt = I.elt + rand(-I.bd:I.bd) * rand(I.b)
    end
    if !iszero(I.elt)
      return deepcopy(I.elt)
    end
  end
end

