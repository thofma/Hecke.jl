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

#finds x in K s.th. xI is c.FB-smooth. returns x and the factorisation 
function class_group_ideal_relation(I::Hecke.NfMaxOrdIdl, c::Hecke.ClassGrpCtx)
  #easy case: I factors over the FB...
  O = order(I)
  K = nf(O)
  n = norm(I)
  if issmooth(c.FB.fb_int, n)
    fl, r = _factor!(c.FB, I)
    if fl 
      return K(1), r
    end
  end
  # ok, we have to work
  I, b = Hecke.reduce_ideal2(I) # not unneccessarily hard on us...
#  println("reduce to $I")
  n = norm(I)
  if issmooth(c.FB.fb_int, n)
    fl, r = _factor!(c.FB, I)
    if fl 
      return b, r
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
        scale_row!(r, fmpz(-1))
        return b//a, r
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


function class_group_disc_log(I::Hecke.NfMaxOrdIdl, c::Hecke.ClassGrpCtx)
  return class_group_disc_log(class_group_ideal_relation(I, c)[2], c)
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


#the kannan_bachem needs to be cached somewhere.

#we're missing the S-Unit group

function principal_gen_fac_elem(A::NfMaxOrdIdl)
  O = order(A)
  c = Hecke._get_ClassGrpCtx_of_order(O)

  H, T = Hecke.hnf_kannan_bachem(vcat(c.M.bas_gens,  c.M.rel_gens), Val{true})

  x, r = Hecke.class_group_ideal_relation(A, c)

  R, d = Hecke.solve_ut(H, r)
  if d != 1
    error("ideal not principal")
  end
  rs = zeros(fmpz, c.M.bas_gens.r + c.M.rel_gens.r)
  for (p,v) = R
    rs[p] = v
  end

  for i in length(T):-1:1
    Hecke.apply_right!(rs, T[i])
  end

  e = Hecke.FacElem(vcat(c.R_gen, c.R_rel), rs)*x

  #reduce e modulo units.
  e = reduce([e], Hecke._get_UnitGrpCtx_of_order(O))[1]

  return e
end

#for all ideals A in I, this functions find a generator for
#  A^order(A) 
#in factored form
#if the ideals are pairwise coprime primes, this will give a basis
#for the S-unit group (modulo units)
#if not: it's up to you...
function sunits_mod_units(I::Array{NfMaxOrdIdl, 1})
  O = order(I[1])
  c = Hecke._get_ClassGrpCtx_of_order(O)

  H, T = Hecke.hnf_kannan_bachem(vcat(c.M.bas_gens,  c.M.rel_gens), Val{true})

  U = Array{Hecke.FacElem{Hecke.nf_elem, Nemo.AnticNumberField}, 1}()
  for A = I
    x, r = Hecke.class_group_ideal_relation(A, c)
    R, d = Hecke.solve_ut(H, r)
    rs = zeros(fmpz, c.M.bas_gens.r + c.M.rel_gens.r)
    for (p,v) = R
      rs[p] = v
    end

    for i in length(T):-1:1
      Hecke.apply_right!(rs, T[i])
    end

    e = Hecke.FacElem(vcat(c.R_gen, c.R_rel), rs)*x^-d

    push!(U, e)
  end
  U = reduce(U, Hecke._get_UnitGrpCtx_of_order(O))
  return U
end

#the normalise bit ensures that the "log" vector lies in the same vector space
#well, the same hyper-plane, as the units
function conjugates_arb_log_normalise(x::Hecke.FacElem{Hecke.nf_elem, AnticNumberField}, p::Int = 10)
  K = base_ring(x)
  r,s = signature(K)
  c = conjugates_arb_log(x, p)
  R = parent(c[1])
  n = (log(root(R(abs(norm(x))), degree(K))))
  for i=1:r
    c[i] -= n
  end
  for i=r+1:r+s
    c[i] -= n
    c[i] -= n
  end
  return c
end
 
function _conj_arb_log_matrix_normalise_cutoff{T}(u::Array{T, 1}, prec::Int = 32)
  z = conjugates_arb_log_normalise(u[1], prec)
  A = ArbMatSpace(parent(z[1]), length(u), length(z)-1)()
  for i=1:length(z)-1
    A[1,i] = z[i]
  end

  for j=2:length(u)
    z = conjugates_arb_log_normalise(u[j], prec)
    for i=1:length(z)-1
      A[j,i] = z[i]
    end
  end
  return A
end

function reduce_mod_units{T}(a::Array{T, 1}, U::Hecke.UnitGrpCtx)
  #for T of type FacElem, U cannot be found from the order as the order
  #is not known
  r = length(U.units)
  if r == 0
    return a
  end

  prec = U.tors_prec

  b = deepcopy(a)
  while true
    prec, A = Hecke._conj_log_mat_cutoff_inv(U, prec)
    B = _conj_arb_log_matrix_normalise_cutoff(a, prec)
    C = B*A

    redo = false

    for i=1:rows(C)
      for j=1:cols(C)
        fl, v = unique_integer(ceil(C[i,j]))
        if !fl
          prec *= 2
          redo = true
          break
        end
        b[i] *= U.units[j]^-v
      end
      if redo
        break
      end
    end
    return b
  end  
end

