function NormCtx(O::NfAbsOrd, nb::Int, normal::Bool = false)
  if normal
    return NormCtx_split(O, nb)
  else
    return NormCtx_gen(O, nb)
  end
end

function norm(m::fmpz_mat, NC::NormCtx_split, div::fmpz = fmpz(1))
  l = Array{fmpz, 1}()
  for i = 1:length(NC.lp)
    ccall((:fmpz_mat_get_nmod_mat, libflint), Cvoid, (Ref{gfp_mat}, Ref{fmpz_mat}), NC.mp[i], m)
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
    return no
  end
end

#not used.
function norms(a::fmpz_mat, NC::NormCtx_split, div::fmpz = fmpz(1))
  no = Array{fmpz, 1}()
  nr = Array{gfp_mat, 1}()
  for i=1:length(NC.lp)
    n = matrix(NC.lR[i], a)*NC.lC[i]
    m = zero_matrix(NC.lR[i], nrows(a), 1)
    for k=1:nrows(n)
      for j=2:ncols(n)
        n[k, 1] *= n[k, j]
      end
      m[k, 1] = n[k, 1]*inv(NC.lR[i](div))
    end
    push!(nr, m)
  end
  mm = induce_crt(nr, NC.e, true)
end

function norm(a::fmpz_mat, NC::NormCtx_gen, div::fmpz = fmpz(1))
  O = NC.O
  k = nf(O)
  no = numerator(norm_div(O(fmpz[a[1, i] for i = 1:degree(k)]).elem_in_nf, div, NC.nb))
  if nbits(no) > NC.nb-10
    return nothing
  else
    return no
  end
end

function class_group_small_lll_elements_relation_start(clg::ClassGrpCtx{T},
                O::NfOrd; prec::Int = 200, val::Int = 0,
                limit::Int = 0) where {T}
  return class_group_small_lll_elements_relation_start(clg, ideal(O, parent(basis_matrix(O).num)(1)), prec = prec)
end

function class_group_small_lll_elements_relation_start(clg::ClassGrpCtx{T},
                A::NfOrdIdl; prec::Int = 200, val::Int = 0,
                limit::Int = 0) where {T}
  global _start = A
  O = order(A)
  n = degree(O)
  L, Tr = lll(A, prec = prec)
  I = SmallLLLRelationsCtx(zero_matrix(FlintZZ, 1, 1))
  S = Tr*basis_matrix(A, copy = false)
  bd = abs(discriminant(O))*norm(A)^2
  bd = root(bd, n)
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
  I.b = Vector{fmpz_mat}(undef, length(f))
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

