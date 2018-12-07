mutable struct SmallLLLRelationsCtx{T}
  A::NfOrdIdl
  b::Array{T, 1}
  bd::Int
  cnt::Int
  elt::T
  function SmallLLLRelationsCtx(a::T) where {T}
    n = new{T}()
    n.bd = 1
    n.cnt = 0
    return n
  end
end

mutable struct NormCtx_split <: NormCtx
  O::NfAbsOrd{AnticNumberField, nf_elem}
  lp::Array{Int, 1}  #the primes
  lR::Array{GaloisField, 1} #the local (finite field) splitting field
  nb::Int #bound on the number of bits the norm is allowed to have
  lC::Array{gfp_mat, 1} # for each p in lp, the conjugates of the basis of O
  mp::Array{gfp_mat, 1} # for each p in lp, the conjugates of the basis of O
  np::Array{gfp_mat, 1} # for each p in lp, the conjugates of the basis of O
  e::crt_env
  function NormCtx_split(O::NfAbsOrd, nb::Int)
    p = p_start
    NC = new()
    NC.O = O
    NC.nb = nb
    NC.lp = Array{Int, 1}()
    NC.lR = Array{GaloisField, 1}()
    NC.lC = Array{gfp_mat, 1}()
    NC.mp = Array{gfp_mat, 1}()
    NC.np = Array{gfp_mat, 1}()
    B = basis(O)
    n = degree(O)
    while (true)
      p = next_prime(p)
      lP = prime_decomposition(O, p)
      if length(lP) < degree(O)
        continue
      end
      push!(NC.lp, p)
      R = GF(p, cached = false)
      push!(NC.lR, R)
      push!(NC.mp, zero_matrix(R, 1, degree(O)))
      push!(NC.np, zero_matrix(R, 1, degree(O)))
      M = Array{Nemo.elem_type(R), 1}()
      for P = lP
        F, mF = ResidueFieldSmall(O, P[1])
        for x = B
          xp = mF(x)
          push!(M, R(coeff(xp, 0)))
        end
      end
      push!(NC.lC, matrix(R, n, n, M)')
      nb -= nbits(p)
      if nb <= 0
        NC.e = crt_env(fmpz[p for p = NC.lp])
        return NC
      end
    end
  end
end

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
    ccall((:fmpz_mat_get_nmod_mat, :libflint), Cvoid, (Ref{gfp_mat}, Ref{fmpz_mat}), NC.mp[i], m)
    mul!(NC.np[i], NC.mp[i], NC.lC[i])
    n = NC.np[i]
    p = n[1,1]
    for j=2:cols(m)
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
    m = zero_matrix(NC.lR[i], rows(a), 1)
    for k=1:rows(n)
      for j=2:cols(n)
        n[k, 1] *= n[k, j]
      end
      m[k, 1] = n[k, 1]*inv(NC.lR[i](div))
    end
    push!(nr, m)
  end
  mm = induce_crt(nr, NC.e, true)
end

mutable struct NormCtx_gen <: NormCtx
  nb::Int
  O::NfAbsOrd
  function NormCtx_gen(O::NfAbsOrd, nb::Int)
    NC = new()
    NC.nb = nb
    NC.O = O
    return NC
  end
end

function norm(a::fmpz_mat, NC::NormCtx_gen, div::fmpz = fmpz(1))
  O = NC.O
  k = nf(O)
  no = numerator(norm_div(k(O(fmpz[a[1, i] for i = 1:degree(k)])), div, NC.nb))
  if nbits(no) > NC.nb-10
    return nothing
  else
    return no
  end
end

function class_group_small_lll_elements_relation_start(clg::ClassGrpCtx{T},
                O::NfOrd; prec::Int = 200, val::Int = 0,
                limit::Int = 0) where {T}
  return class_group_small_lll_elements_relation_start(clg, hecke.ideal(O, parent(basis_mat(O).num)(1)), prec = prec)
end

function class_group_small_lll_elements_relation_start(clg::ClassGrpCtx{T},
                A::NfOrdIdl; prec::Int = 200, val::Int = 0,
                limit::Int = 0) where {T}
  global _start
  O = order(A)
  K = nf(O)
  local rt::UInt
  @v_do :ClassGroup_time 2 rt = time_ns()

  local I, S, bd

  while true
    try
    L::FakeFmpqMat, Tr::fmpz_mat = lll(A, prec = prec)
    @v_do :ClassGroup_time 2 _start += time_ns()-rt
    I = SmallLLLRelationsCtx(zero_matrix(FlintZZ, 1, 1))
    S::FakeFmpqMat = FakeFmpqMat(Tr)*basis_mat(A, Val{false})
    bd::fmpz = abs(discriminant(order(A)))*norm(A)^2
    bd = root(bd, degree(K))::fmpz
    bd *= L.den
    f = findall(i-> cmpindex(L.num, i, i, bd) < 0, 1:degree(K))
    m = div(degree(K), 4)
    if m < 2
      m = degree(K)
    end
    while length(f) < m 
      f = findall(i-> cmpindex(L.num, i, i, bd) < 0, 1:degree(K))
        bd *= 2
      end
      I.b = fmpz_mat[]
      @assert S.den == 1
      for i=f
        push!(I.b, view(S.num, i:i, 1:cols(S.num)))
      end
      #println([Float64(numerator(L)[i,i]//denominator(L)*1.0) for i=1:degree(K)])
      #now select a subset that can yield "small" relations, where
      #small means of effective norm <= sqrt(disc)
      I.A = A
      I.elt = zero_matrix(FlintZZ, 1, degree(O))
      return I
    catch e
      if isa(e, LowPrecisionLLL) || isa(e, InexactError)
        printstyled("prec too low in LLL\n", color = :red)
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

