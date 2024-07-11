################################################################################
#
#  Triangularization
#
################################################################################

function _strong_echelon_form(A::MatElem{AbsSimpleNumFieldOrderQuoRingElem}, strategy)
  B = deepcopy(A)

  if nrows(B) < ncols(B)
    B = vcat(B, zero_matrix(base_ring(B), ncols(B) - nrows(B), ncols(B)))
  end

  if strategy == :split
    q, w = z_split1(ideal(base_ring(A)))
    R = order(ideal(base_ring(A)))
    ideals = vcat(q, w)
    #if length(w) != 0
    #  push!(ideals, prod(w))
    #end
    C = _strong_echelon_form_split(B, ideals)
    return C
  elseif strategy == :no_split
    C = _strong_echelon_form_nonsplit(B)
    return C
  else
    error("Invalid strategy")
  end
end

function strong_echelon_form(A::MatElem{AbsSimpleNumFieldOrderQuoRingElem}, shape::Symbol = :upperright, strategy::Symbol = :split)
  if shape == :lowerleft
    h = _strong_echelon_form(reverse_cols(A), strategy)
    reverse_cols!(h)
    reverse_rows!(h)
    return h
  elseif shape == :upperright
    h = _strong_echelon_form(A, strategy)
    return h
  else
    error("Not yet implemented")
  end
end

################################################################################
#
#  Inverse
#
################################################################################

function inv(A::MatElem{T}) where {T <: Union{AbsSimpleNumFieldOrderQuoRingElem, LocalFieldValuationRingResidueRingElem}}
  !is_square(A) && error("Matrix not invertible")
  H, U = howell_form_with_transformation(A)
  !is_one(H) && error("Matrix not invertible")
  return U
end

################################################################################
#
#  Determinant
#
################################################################################

function det(M::Generic.Mat{AbsSimpleNumFieldOrderQuoRingElem})
  nrows(M) != ncols(M) && error("Matrix must be square matrix")
  N = deepcopy(M)
  d = AbstractAlgebra.triangularize!(N)
  z = one(base_ring(M))
  for i in 1:nrows(N)
    z = z * N[i, i]
  end
  return z*d
  q, r = divrem(z, d)
  @hassert :AbsOrdQuoRing 1 iszero(r)
  return divexact(z, d)
end

################################################################################
#
#  Z Split
#
################################################################################

function z_split1(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  lf = factor_easy(I)
  if isempty(lf)
    return AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[I], AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
  end
  A = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
  B = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
  for (I, v) in lf
    a = I^v
    if norm(a) != minimum(a)
      push!(B, a)
    else
      push!(A, a)
    end
  end
  return A, B
end



function z_split(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  b = basis_matrix(I, copy = false)
  O = order(I)
  n = degree(O)
  c = coprime_base([b[i, i] for i in 1:n])
  nI = norm(I)
  if isone(nI)
    return AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[I], AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
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

  A = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
  B = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]

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

function can_map_into_integer_quotient(Q::AbsSimpleNumFieldOrderQuoRing)
  B = basis_matrix(ideal(Q), copy = false)
  for i in 2:ncols(B)
    if !isone(B[i, i])
      return false
    end
  end
  return true
end

function map_into_integer_quotient(Q::AbsSimpleNumFieldOrderQuoRing)
  B = basis_matrix(ideal(Q), copy = false)
  m = B[1, 1]
  R = residue_ring(FlintZZ, m, cached = false)[1]
  local f
  let R = R, Q = Q
    function f(x::AbsSimpleNumFieldOrderQuoRingElem)
      mod!(x.elem, Q)
      return R(coordinates(x.elem, copy = false)[1])
    end
  end
  g = (y -> Q(y.data)::AbsSimpleNumFieldOrderQuoRingElem)
  return R, f, g
end

function can_make_small(Q::EuclideanRingResidueRing{ZZRingElem})
  if nbits(modulus(Q)) < Sys.WORD_SIZE - 1
    return true
  else
    return false
  end
end

function can_make_small(Q::Nemo.ZZModRing)
  if nbits(modulus(Q)) < Sys.WORD_SIZE - 1
    return true
  else
    return false
  end
end

function make_small(Q::EuclideanRingResidueRing{ZZRingElem})
  R = residue_ring(FlintZZ, Int(modulus(Q)), cached = false)[1]
  f = (x -> R(x.data)::zzModRingElem)
  g = (x -> Q(x.data)::EuclideanRingResidueRingElem{ZZRingElem})
  return R, f, g
end

function make_small(Q::Nemo.ZZModRing)
  R = residue_ring(FlintZZ, Int(modulus(Q)), cached = false)[1]
  f = (x -> R(data(x))::zzModRingElem)
  g = (x -> Q(x.data)::Nemo.ZZModRingElem)
  return R, f, g
end


function _strong_echelon_form_split(M::MatElem{AbsSimpleNumFieldOrderQuoRingElem}, ideals1)
  Q = base_ring(M)
  R = base_ring(Q)
  modulus = ideal(Q)
  ideals = sort(ideals1, by = x -> minimum(x, copy = false))

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
  _strong_echelon_form_nonsplit!(MmodI)
  for i in 1:min(n, m)
    for j in i:m
      M_cur[i, j] = Q(lift(MmodI[i, j]))
    end
  end

  _assure_weakly_normal_presentation(I)
  gI = gcd(Q(I.gen_one), Q(I.gen_two))

  @hassert :PseudoHnf 1 ideal(R, lift(R, gI)) + modulus == I

  r = M_cur
  l = gI

  m_cur = zero_matrix(Q, n, m)

  for i in 2:length(ideals)
    I = ideals[i]

    RmodI, mRmodI = quo(R, I)
    MmodI = zero_matrix(RmodI, n, m)

    for i in 1:n
      for j in 1:m
        MmodI[i, j] = RmodI(lift(M[i, j]))
      end
    end

    echelon_modI = _strong_echelon_form_nonsplit(MmodI)

    for i in 1:min(n, m)
      for j in i:m
        m_cur[i, j] = Q(lift(R, echelon_modI[i, j]))
      end
    end


    _assure_weakly_normal_presentation(I)
    gI = gcd(Q(I.gen_one), Q(I.gen_two))

    @hassert :PseudoHnf 1 ideal(R, lift(R, gI)) + modulus == I

    g, a, b, e, f = gcdxx(l, gI)
    #gg = g
    ginv = inv(g)
    #mul!(e, e, gg)
    #mul!(f, f, gg)
    #mul!(g, g, ginv)
    mul!(a, a, ginv)
    mul!(b, b, ginv)
    #g = g * ginv
    #a = a * ginv
    #b = b * ginv
    #e = e * gg
    #f = f * gg
    #@hassert :PseudoHnf 1 g == a * l + b * gI
    #@hassert :PseudoHnf 1 0 == e * l + f * gI
    #@hassert :PseudoHnf 1 1 == a * f - b * e
    mul!(a, a, l)
    mul!(b, b, gI)
    #a = a * l
    #b = b * gI
    mul_special!(r, b)
    mul_special!(m_cur, a)
    add_special!(r, m_cur)
    #r = r * b + m_cur * a
    mul!(l, l, gI)
    #l = l * gI
  end
  return r
end

function mul!(a::MatElem{AbsSimpleNumFieldOrderQuoRingElem}, b::MatElem{AbsSimpleNumFieldOrderQuoRingElem}, c::AbsSimpleNumFieldOrderQuoRingElem)
  for i = 1:nrows(b)
    for j = 1:ncols(b)
      mul!(a[i, j], b[i, j], c)
    end
  end
  return a
end

function mul_special!(a::MatElem{AbsSimpleNumFieldOrderQuoRingElem}, b::AbsSimpleNumFieldOrderQuoRingElem)
  for i = 1:min(nrows(a), ncols(a))
    for j = i:ncols(a)
      mul!(a[i, j], a[i, j], b)
    end
  end
  return a
end

function add_special!(a::MatElem{AbsSimpleNumFieldOrderQuoRingElem}, b::MatElem{AbsSimpleNumFieldOrderQuoRingElem})
  for i = 1:min(nrows(b), ncols(b))
    for j = i:ncols(b)
      add!(a[i, j], a[i, j], b[i, j])
    end
  end
  return a
end

function add!(a::MatElem{AbsSimpleNumFieldOrderQuoRingElem}, b::MatElem{AbsSimpleNumFieldOrderQuoRingElem}, c::MatElem{AbsSimpleNumFieldOrderQuoRingElem})
  for i = 1:nrows(b)
    for j = 1:ncols(b)
      add!(a[i, j], b[i, j], c[i, j])
    end
  end
  return a
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

function _strong_echelon_form_nonsplit!(M)
  Q = base_ring(M)

  n = nrows(M)
  m = ncols(M)

  if can_map_into_integer_quotient(Q)
    RmodIZ, f, g = map_into_integer_quotient(Q)
    if can_make_small(RmodIZ)
      RmodIZsmall, ff, gg = make_small(RmodIZ)
      M_temp = zero_matrix(RmodIZsmall, n, m)
      for i in 1:n
        for j in 1:m
          M_temp[i, j] = ff(f(M[i, j]))
        end
      end
      strong_echelon_form!(M_temp)
      for i in 1:min(n, m)
        for j = 1:i-1
          zero!(M[i, j])
        end
        for j in i:m
          M[i, j] = g(gg(M_temp[i, j]))
        end
      end
      for i = min(n, m)+1:n
        for j = 1:m
          zero!(M[i, j])
        end
      end
    else
      forflint = zero_matrix(FlintZZ, n, m)
      for i in 1:n
        for j in 1:m
          forflint[i, j] = f(M[i, j]).data
        end
      end
      ccall((:fmpz_mat_strong_echelon_form_mod, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZRingElem}), forflint, modulus(RmodIZ))
      for i in 1:min(n, m)
        for j = 1:i-1
          zero!(M[i, j])
        end
        for j in i:m
          M[i, j] = Q(forflint[i, j])
        end
      end
      for i = min(n, m)+1:n
        for j = 1:m
          zero!(M[i, j])
        end
      end
    end
    return M
  else
    AbstractAlgebra.strong_echelon_form_naive!(M)
    return M
  end

end


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
      for i in 1:min(n, m)
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
      ccall((:fmpz_mat_strong_echelon_form_mod, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZRingElem}), forflint, modulus(RmodIZ))
      for i in 1:min(n, m)
        for j in 1:m
          M_cur[i, j] = Q(forflint[i, j])
        end
      end
    end
    return M_cur
  else
    N = deepcopy(M)
    AbstractAlgebra.strong_echelon_form_naive!(N)
    return N
  end
end

function test_pseudohnf()
  Qx, x = FlintQQ["x"]
  for i in 2:15
    K, a = number_field(x^i - 10, "a")
    O = maximal_order(K)
    lp = AbsSimpleNumFieldOrderFractionalIdeal[]
    for p in [2, 3, 5, 7, 11, 13]
      pp = prime_decomposition(O, p)
      for P in pp
        push!(lp, fractional_ideal(O, P[1]))
      end
    end

    pm = pseudo_matrix(matrix(K, 5, 5, [ rand(-2^10:2^10) for i in 1:25]), rand(lp, 5))

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
