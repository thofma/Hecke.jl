module PolymakeOscar

using Polymake, Hecke, Markdown

Hecke.nrows(A::Polymake.pm_MatrixAllocated) = Int(size(A)[1])
Hecke.ncols(A::Polymake.pm_MatrixAllocated) = Int(size(A)[2])

@doc Markdown.doc"""
    solve_ineq(A::fmpz_mat, b::fmpz_mat)

Solves $Ax<=b$, assumes finite set of solutions.
"""
function solve_ineq(A::fmpz_mat, b::fmpz_mat)
  bA = Array{BigInt, 2}(hcat(-b, A))
  p = @pm Polytope.Polytope( :INEQUALITIES => bA)
  inner = p.INTERIOR_LATTICE_POINTS
  out = p.BOUNDARY_LATTICE_POINTS

  res = zero_matrix(FlintZZ, nrows(inner) + nrows(out), ncols(A))
  for i=1:nrows(out)
    @assert out[i,1] == 1
    for j=1:ncols(A)
      res[i,j] = out[i, j+1]
    end
  end
  for i=1:nrows(inner)
    @assert inner[i,1] == 1
    for j=1:ncols(A)
      res[i+nrows(out), j] = inner[i, j+1]
    end
  end
  return res
end

@doc Markdown.doc"""
    solve_non_negative(A::fmpz_mat, b::fmpz_mat)

Finds all solutions to $Ax = b$, $x>=0$. Assumes a finite set of solutions.
"""
function solve_non_negative(A::fmpz_mat, b::fmpz_mat)
  bA = Array{BigInt, 2}(hcat(-b, A))
  zI = Array{BigInt, 2}(hcat(zero_matrix(FlintZZ, ncols(A), 1), MatrixSpace(FlintZZ, ncols(A), ncols(A))(1)))
  p = @pm Polytope.Polytope(:EQUATIONS => deepcopy(bA), :INEQUALITIES => deepcopy(zI))
  inner = p.INTERIOR_LATTICE_POINTS
  out = p.BOUNDARY_LATTICE_POINTS

  res = zero_matrix(FlintZZ, nrows(inner) + nrows(out), ncols(A))
  for i=1:nrows(out)
    @assert out[i,1] == 1
    for j=1:ncols(A)
      res[i,j] = out[i, j+1]
    end
  end
  for i=1:nrows(inner)
    @assert inner[i,1] == 1
    for j=1:ncols(A)
      res[i+nrows(out), j] = inner[i, j+1]
    end
  end
  return res
end

@doc Markdown.doc"""
    solve_mixed(A::fmpz_mat, b::fmpz_mat, C::fmpz_mat)

Solves $Ax = b$ under $Cx >= 0$, assumes a finite solution set.
"""
function solve_mixed(A::fmpz_mat, b::fmpz_mat, C::fmpz_mat)  # Ax == b && Cx >= 0
  bA = Array{BigInt, 2}(hcat(-b, A))
  z = findall(i->!iszero_row(bA, i), 1:nrows(bA))
  zbA = Array{BigInt, 2}(bA[z, :])
  z = findall(i->!iszero_row(C, i), 1:nrows(C))
  zI = Array{BigInt, 2}(hcat(zero_matrix(FlintZZ, nrows(C), 1), C))[z, :]
  if length(zbA) == 0
    p = @pm Polytope.Polytope(:INEQUALITIES => zI)
  else
    if nrows(zI) == 0
      p = @pm Polytope.Polytope(:EQUATIONS => zbA)
    else
      p = @pm Polytope.Polytope(:EQUATIONS => zbA, :INEQUALITIES => zI)
    end
  end
  inner = p.INTERIOR_LATTICE_POINTS
  out = p.BOUNDARY_LATTICE_POINTS

  res = zero_matrix(FlintZZ, nrows(inner) + nrows(out), ncols(A))
  for i=1:nrows(out)
    @assert out[i,1] == 1
    for j=1:ncols(A)
      res[i,j] = out[i, j+1]
    end
  end
  for i=1:nrows(inner)
    @assert inner[i,1] == 1
    for j=1:ncols(A)
      res[i+nrows(out), j] = inner[i, j+1]
    end
  end
  return res
end

@doc Markdown.doc"""
    solve_mixed(A::fmpz_mat, b::fmpz_mat, C::fmpz_mat, d::fmpz_mat)

Solves $Ax = b$ under $Cx >= d$, assumes a finite solution set.
"""
function solve_mixed(A::fmpz_mat, b::fmpz_mat, C::fmpz_mat, d::fmpz_mat)
  n = ncols(A)
  A = cat(A, identity_matrix(FlintZZ, ncols(d)), dims=(1,2))
  b = vcat(b, identity_matrix(FlintZZ, ncols(d)))
  C = [C -d; zero_matrix(FlintZZ, ncols(d), ncols(C)) identity_matrix(FlintZZ, ncols(d))]
  s = solve_mixed(A, b, C)
  return s[:, 1:n]
end

function Hecke.valuation(a::FacElem{fmpz, FlintIntegerRing}, p::fmpz)
  return sum(k*valuation(b, p) for (b, k) = a.fac)
end

function norm_equation2_fac_elem(R::NfAbsOrd, k::fmpz; abs::Bool = false)
  @assert Hecke.ismaximal(R)
  lp = factor(k*R)
  s, ms = Hecke.sunit_mod_units_group_fac_elem(collect(keys(lp)))
  C = vcat([matrix(FlintZZ, 1, ngens(s), [valuation(ms(s[i]), p) for i=1:ngens(s)]) for p = keys(lp)])
  
  lp = factor(k)
  A = vcat([matrix(FlintZZ, 1, ngens(s), [valuation(Hecke.factored_norm(ms(s[i])), p) for i=1:ngens(s)]) for p = keys(lp.fac)])
  b = matrix(FlintZZ, length(lp.fac), 1, [valuation(k, p) for p = keys(lp.fac)])

  so = solve_mixed(A, b, C)
  sol = [ms(s(sub(so, i:i, 1:ncols(so)))) for i=1:nrows(so)]

  if !abs
    u, mu = unit_group_fac_elem(R)
    i = findfirst(x -> norm(mu(x)) == -1, gens(u))
    ns = [norm(x) for x = sol]
    if i === nothing
      return [sol[i] for i in 1:length(sol) if ns[i] == k]
    end
    U = mu(u[i])
    return [ ns[i] == k ? sol[i] : sol[i] * U for i = 1:length(sol)]
  end
  return sol
end


function norm_equation_fac_elem(R::NfAbsOrd, k::fmpz; abs::Bool = false)
  @assert Hecke.ismaximal(R)
  lp = factor(k)
  S = []
  for (p, k) = lp.fac
    P = prime_decomposition(R, p)
    s = solve_non_negative(matrix(FlintZZ, 1, length(P), [degree(x[1]) for x = P]), matrix(FlintZZ, 1, 1, [k]))
    push!(S, (P, [view(s, i:i, 1:ncols(s)) for i=1:nrows(s)]))
  end
  sol = []
  for x in Base.Iterators.ProductIterator(Tuple(t[2] for t = S))
    I = ideal(R, 1)
    for i = 1:length(S)
      I *= prod(S[i][1][j][1]^Int(x[i][j]) for j=1:length(S[i][1]))
    end
    fl, g = Hecke.isprincipal_fac_elem(I)
    if fl
      push!(sol, g)
    end
  end
  if !abs
    u, mu = unit_group_fac_elem(R)
    i = findfirst(x -> norm(mu(x)) == -1, gens(u))
    ns = [norm(x) for x = sol]
    if i === nothing
      return [sol[i] for i in 1:length(sol) if ns[i] == k]
    end
    U = mu(u[i])
    return [ ns[i] == k ? sol[i] : sol[i] * U for i = 1:length(sol)]
  end
  return sol
end

norm_equation_fac_elem(R::NfAbsOrd, k::Integer; abs::Bool = false) = 
                            norm_equation_fac_elem(R, fmpz(k), abs = abs)

function norm_equation(R::NfAbsOrd, k::fmpz; abs::Bool = false)
  s = norm_equation_fac_elem(R, k, abs = abs)
  return [R(evaluate(x)) for x = s]
end

norm_equation(R::NfAbsOrd, k::Integer; abs::Bool = false) = norm_equation(R, fmpz(k), abs = abs)

function norm_equation_fac_elem(R::Hecke.NfRelOrd{nf_elem,Hecke.NfOrdFracIdl}, a::NfAbsOrdElem{AnticNumberField,nf_elem})

  @assert Hecke.ismaximal(R)
  Ka, mKa, mkK = absolute_field(nf(R))
  Ra = maximal_order(Ka)
  class_group(Ra)
  k = nf(parent(a))
  class_group(parent(a))

  lp = factor(Ra(mkK(k(a)))*Ra)
  la = factor(a*parent(a))
  S, mS = Hecke.sunit_mod_units_group_fac_elem(collect(keys(lp)))
  s, ms = Hecke.sunit_mod_units_group_fac_elem(collect(keys(la)))
  No = hom(S, s, elem_type(s)[preimage(ms, norm(mkK, mS(g))) for g = gens(S)])
  q, mq = quo(S, kernel(No)[1])
  q, mms = snf(q)
  mq = mq*inv(mms)

  C = vcat([matrix(FlintZZ, 1, ngens(q), [valuation(mS(preimage(mq, q[i])), p) for i=1:ngens(q)]) for p = keys(lp)])
  
  A = vcat([matrix(FlintZZ, 1, ngens(q), [valuation(norm(mkK, mS(preimage(mq, g))), p) for g in gens(q)]) for p = keys(la)])
  b = matrix(FlintZZ, length(la), 1, [valuation(a, p) for p = keys(la)])

  so = solve_mixed(A, b, C)
  u, mu = Hecke.unit_group_fac_elem(parent(a))
  U, mU = Hecke.unit_group_fac_elem(Ra)
  No = hom(U, u, elem_type(u)[preimage(mu, norm(mkK, mU(g))) for g = gens(U)])
  sol = []
  for i = 1:nrows(so)
    aa = mS(preimage(mq, q(sub(so, i:i, 1:ncols(so)))))
    b = norm(mkK, aa)
    c = b*inv(FacElem(k(a)))
    d = preimage(mu, c)
    fl, p = haspreimage(No, d)
    if fl
      push!(sol, FacElem(Dict(mKa(x) => v for (x, v) = (aa*inv(mU(p))).fac)))
    end
  end

  return sol
end

function Hecke.isirreducible(a::NfAbsOrdElem{AnticNumberField,nf_elem})
  if iszero(a)
    return false
  end
  O = parent(a)
  S = collect(keys(factor(a*O)))
  if length(S) == 0
    return false
  end
  s, ms = Hecke.sunit_mod_units_group_fac_elem(S)
  V = matrix([fmpz[valuation(ms(x), y) for y = S] for x = gens(s)])
  b = matrix([fmpz[valuation(a, y) for y = S]])
  sol = solve(V, b)

  #want to write sol = x+y where
  # Cx, Cy > 0
  # if this is possible, then a is not irreducible as a
  # is then ms(Ax) * ms(Ay) and neither is trivial.

  I = identity_matrix(FlintZZ, length(S))
  A = hcat(I, I)
  #so A*(x|y) = x+y = sol is the  1. condition
  C = cat(V, V, dims=(1,2))
  # C(x|y) >=0 iff Cx >=0 and Cy >=0
  #Cx <> 0 iff (1,..1)*Cx >= 1
  one = matrix(FlintZZ, 1, length(S), [1 for p = S])
  zer = matrix(FlintZZ, 1, length(S), [0 for p = S])
  C = vcat(C, hcat(one, zer), hcat(zer, one))
  d = matrix(FlintZZ, 2*length(S)+2, 1, [0 for i = 1:2*length(S) + 2])
  d[end-1, 1] = 1
  d[end, 1] = 1

  pt = solve_mixed(A, sol, C, d)
  return nrows(pt) == 0
end

function irreducibles(S::Array{NfAbsOrdIdl{AnticNumberField,nf_elem},1})
  if length(S) == 0
    return []
  end
  @assert all(isprime, S)
  #TODO: try to get a better bound - in general if S is too large
  #      it cannot work 
  
  O = order(S[1])
  @assert all(x-> order(x) == O, S)

  s, ms = Hecke.sunit_mod_units_group_fac_elem(S)
  if length(S) == 1
    return O(evaluate(ms(s[1])))
  end
  c, mc = class_group(O)

  V = matrix([[valuation(ms(x), y) for y = S] for x = gens(s)])
  o = matrix([[order(preimage(mc, p))-1 for p = S]]) #TODO: this info is in V!
  if length(S) > sum(o)
    @show "fast"
    return []
  end
  #potential elements x
  # have valuation Vx
  # if the support is supposed to be S, then Vx >= 1
  # Vx < o (or else I can remove primes from the support)
  # have to be irreducible...
  so = solve_mixed(zero_matrix(FlintZZ, 1, length(S)), zero_matrix(FlintZZ, 1, 1), vcat(V, -V), vcat(matrix(FlintZZ, length(S), 1, [1 for p = S]), -o))

  res = []
  for i = 1:nrows(so)
    x = O(evaluate(ms(s(so[i, :]))))
    if isirreducible(x)
      push!(res, x)
    end
  end
  return res
end

function factorisations(a::NfAbsOrdElem{AnticNumberField,nf_elem})
  O = parent(a)
  S = collect(keys(factor(a*O)))
  if length(S) == 0
    return []
  end
  irr = reduce(vcat, irreducibles(collect(x)) for x = Hecke.subsets(Set(S)))
  A = matrix([fmpz[valuation(x, y) for y = S] for x = irr])
  b = matrix([fmpz[valuation(a, y) for y = S]])
  sol = solve_non_negative(A, b)
  res = Fac{NfAbsOrdElem{AnticNumberField,nf_elem}}[]
  for j=1:nrows(sol)
    x = Dict{typeof(a), Int}()
    y = a
    for i=1:length(irr)
      if sol[j,i] != 0
        x[irr[i]] = sol[j,i]
        y = divexact(y, irr[i]^sol[j,i])
      end
    end
    push!(res, Fac(y, x))
  end
  return res
end

function Base.lastindex(a::fmpz_mat, i::Int)
  i==1 && return nrows(a)
  i==2 && return ncols(a)
  error("illegal dimension")
end

end
