################################################################################
# maps and disc_log and such
################################################################################

function power_class(A::NfMaxOrdIdl, e::fmpz)
  if e == 0
    O = order(A)
    return Hecke.ideal(O, parent(basis_mat(O).num)(1))
  end

  if e < 0
    A = inv(A)
    e = -e
    A = Hecke.reduce_ideal(A)
  end

  if e == 1
    return A
  elseif e == 2
    return A*A
  end

  f = div(e, 2)
  B = power_class(A, f)^2
  if isodd(e)
    B *= A
  end
  if norm(B) > root(abs(discriminant(order(A))), 2)
    B = Hecke.reduce_ideal(B)
  end
  return B
end

function power_product_class(A::Array{Hecke.NfMaxOrdIdl, 1}, e::Array{fmpz, 1})
  i = 1
  while i <= length(e) && e[i] == 0
    i += 1
  end
  if i > length(e)
    return power_class(A[1], 0)
  end
  B = power_class(A[i], e[i])
  i += 1
  while i <= length(e)
    if e[i] != 0
      B *= power_class(A[i], e[i])
      if norm(B) > root(abs(discriminant(order(B))), 2)
        B = Hecke.reduce_ideal(B)
      end
    end
    i += 1
  end
  return B
end

function class_group_disc_exp(a::Hecke.FinGenGrpAbElem, c::Hecke.ClassGrpCtx)
  if length(c.dl_data) == 3
    Ti = inv(c.dl_data[2])
    c.dl_data = (c.dl_data[1], c.dl_data[2], c.dl_data[3], Ti)
  else
    Ti = c.dl_data[4]
  end
  e = a.coeff * sub(Ti, rows(Ti)-cols(a.coeff)+1:rows(Ti), 1:cols(Ti))
  return power_product_class(c.FB.ideals[length(c.FB.ideals)-rows(Ti)+1:end], [mod(e[1, i], c.h) for i=1:cols(e)])
end

function class_group_disc_log(r::SRow{fmpz}, c::Hecke.ClassGrpCtx)
  if c.h==1
    return fmpz[1]
  end
  if length(c.dl_data) == 3
    s, T, C = c.dl_data
  else
    s, T, C, Ti = c.dl_data
  end
#  println("start with $r")
  while length(r.pos)>0 && r.pos[1] < s
    r = Hecke.add_scaled_row(c.M.basis[r.pos[1]], r, -r.values[1])
    Hecke.mod!(r, c.h)
  end

#  println("reduced to $r")
  rr = MatrixSpace(FlintZZ, 1, rows(T))()
  for i = 1:rows(T)
    rr[1,i] = 0
  end
  for (p,v) = r
    rr[1, p-s+1] = v
  end
  return C(sub(rr*T, 1:1, rows(T)-length(C.snf)+1:rows(T)))
end

function class_group_disc_log(I::Hecke.NfMaxOrdIdl, c::Hecke.ClassGrpCtx)
  #easy case: I factors over the FB...
  n = norm(I)
  if issmooth(c.FB.fb_int, n)
    fl, r = _factor!(c.FB, I)
    if fl 
      return class_group_disc_log(r, c)
    end
  end
  # ok, we have to work
  I = Hecke.reduce_ideal(I) # not unneccessarily hard on us...
#  println("reduce to $I")
  n = norm(I)
  if issmooth(c.FB.fb_int, n)
    fl, r = _factor!(c.FB, I)
    if fl 
      return class_group_disc_log(r, c)
    end
  end
  #really annoying, but at least we have a small(ish) ideal now

#  println("have to work")
  E = Hecke.class_group_small_lll_elements_relation_start(c, I)
  iI = inv(I)
  J = Hecke.NfMaxOrdIdl[]
  while true
    a = Hecke.class_group_small_lll_elements_relation_next(E)
#    println("trying $a")
    Ia = simplify(a*iI)
    @assert Ia.den == 1
    n = norm(Ia.num)
    if issmooth(c.FB.fb_int, n)
      fl, r = _factor!(c.FB, Ia.num)
      if fl 
        return -class_group_disc_log(r, c)
      end
    end
    if E.cnt > 100
      push!(J, rand(c.FB.ideals))
      j = Hecke.random_get(J)*I
      E = Hecke.class_group_small_lll_elements_relation_start(c, j) 
      iI = inv(j)
    end
  end
end

type MapClassGrp{T} <: Map{T, Hecke.NfMaxOrdIdlSet}
  header::Hecke.MapHeader

  function MapClassGrp()
    return new()
  end
end

function show(io::IO, mC::MapClassGrp)
  println(io, "ClassGroup map of $(codomain(mC))")
end

function class_group(c::Hecke.ClassGrpCtx; redo::Bool = false)
  if !redo
    if isdefined(c, :cl_map)
      mC = c.cl_map
      C = domain(mC)
      return C, mC
    end
  end  
  C = class_group_grp(c, redo = redo)
  r = MapClassGrp{typeof(C)}()
  r.header = Hecke.MapHeader(C, parent(c.FB.ideals[1]), x->class_group_disc_exp(x, c), x->class_group_disc_log(x, c))

  c.cl_map = r
  return C, r
end

function class_group_grp(c::Hecke.ClassGrpCtx; redo::Bool = false)

  if !redo && isdefined(c, :dl_data)
    return c.dl_data[3]
  end

  h, p = Hecke.class_group_get_pivot_info(c)
  @assert h>0

  if h==1 # group is trivial...
    C = DiagonalGroup([1])
    #mC = x -> 1*O, inv x-> [1]
    c.dl_data = (1, MatrixSpace(FlintZZ, 1, 1)(), C)
    return C
  end

  s = minimum(p)
  #essential bit starts at s..

  n = length(c.FB.ideals)
  es = sub(c.M.basis, s:n, s:n)
  hnf!(es)
  es_dense = fmpz_mat(es)
  S, T = snf_with_transform(es_dense, l=false, r=true)

  p = find(x->S[x,x]>1, 1:cols(S))

  C = DiagonalGroup([S[x,x] for x= p])
  c.dl_data = (s, T, C)
  return C
end

