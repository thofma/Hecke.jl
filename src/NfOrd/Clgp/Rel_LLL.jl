mutable struct SmallLLLRelationsCtx
  A::NfOrdIdl
  b::Array{nf_elem, 1}
  bd::Int
  cnt::Int
  elt::nf_elem
  function SmallLLLRelationsCtx()
    n = new()
    n.bd = 1
    n.cnt = 0
    return n
  end
end

function class_group_small_lll_elements_relation_start{T}(clg::ClassGrpCtx{T},
                O::NfOrd; prec::Int = 200, val::Int = 0,
                limit::Int = 0)
  return class_group_small_lll_elements_relation_start(clg, hecke.ideal(O, parent(basis_mat(O).num)(1)), prec = prec)
end

function class_group_small_lll_elements_relation_start{T}(clg::ClassGrpCtx{T},
                A::NfOrdIdl; prec::Int = 200, val::Int = 0,
                limit::Int = 0)
  global _start
  K = nf(order(A))
  @v_do :ClassGroup_time 2 rt = time_ns()

  local I, S, bd, nL

  while true
    try
      L, Tr = lll(A, prec = prec)
      @v_do :ClassGroup_time 2 _start += time_ns()-rt
      I = SmallLLLRelationsCtx()
      S::FakeFmpqMat = FakeFmpqMat(Tr)*basis_mat(A)*basis_mat(order(A))
      bd::fmpz = abs(discriminant(order(A)))*norm(A)^2
      bd = root(bd, degree(K))::fmpz
      bd *= denominator(L)::fmpz
      nL::fmpz_mat = numerator(L)
      f = find(i-> nL[i,i] < bd, 1:degree(K))
      m = div(degree(K), 4)
      if m < 2
        m = degree(K)
      end
      while length(f) < m 
        f = find(i-> nL[i,i] < bd, 1:degree(K))
        bd *= 2
      end
      I.b = nf_elem[elem_from_mat_row(K, numerator(S), i, denominator(S)) for i=f]
      #println([Float64(numerator(L)[i,i]//denominator(L)*1.0) for i=1:degree(K)])
      #now select a subset that can yield "small" relations, where
      #small means of effective norm <= sqrt(disc)
      I.A = A
      I.elt = K()
      return I
    catch e
      if isa(e, LowPrecisionLLL)
        print_with_color(:red, "prec too low in LLL,")
        prec = Int(ceil(1.2*prec))
#        println(" increasing to ", prec)
        if prec > 1000
          error("2:too much prec")
        end
      else
        rethrow(e)
      end
    end
  end
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
    rand!(I.elt, I.b, -I.bd:I.bd, min(length(I.b), 5))
    if !iszero(I.elt)
      return deepcopy(I.elt)
    end
  end
end

