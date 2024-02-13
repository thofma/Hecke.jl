module PolymakeOscar

using Polymake, Hecke

Hecke.number_of_rows(A::Polymake.MatrixAllocated) = Int(size(A)[1])
Hecke.number_of_columns(A::Polymake.MatrixAllocated) = Int(size(A)[2])

function _polytope(; A::ZZMatrix=zero_matrix(FlintZZ, 1, 1), b::ZZMatrix=zero_matrix(FlintZZ, ncols(A), 1), C::ZZMatrix=zero_matrix(FlintZZ, 1, 1))
  if !iszero(A)
    bA = Matrix{BigInt}(hcat(-b, A))
    z = findall(i->!is_zero_row(bA, i), 1:nrows(bA))
    zbA = Matrix{BigInt}(bA[z, :])
  else
    zbA = Matrix{BigInt}(undef, 0, 0)
  end
  if !iszero(C)
    z = findall(i->!is_zero_row(C, i), 1:nrows(C))
    zI = Matrix{BigInt}(hcat(zero_matrix(FlintZZ, nrows(C), 1), C))[z, :]
  else
    zI = Matrix{BigInt}(undef, 0, 0)
  end
  if length(zbA) == 0
    p =  polytope.Polytope(INEQUALITIES = zI)
  else
    if nrows(zI) == 0
      p = polytope.Polytope(EQUATIONS = zbA)
    else
      p = polytope.Polytope(EQUATIONS = zbA, INEQUALITIES = zI)
    end
  end
  return p
end



@doc raw"""
    solve_ineq(A::ZZMatrix, b::ZZMatrix)

Solves $Ax<=b$, assumes finite set of solutions.
"""
function solve_ineq(A::ZZMatrix, b::ZZMatrix)
  p = _polytope(C = hcat(b, -A))
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

@doc raw"""
    solve_non_negative(A::ZZMatrix, b::ZZMatrix)

Finds all solutions to $Ax = b$, $x>=0$. Assumes a finite set of solutions.
"""
function solve_non_negative(A::ZZMatrix, b::ZZMatrix)
  p = _polytope(A = A, b = b, C = identity_matrix(FlintZZ, ncols(A)))
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

@doc raw"""
    solve_mixed(A::ZZMatrix, b::ZZMatrix, C::ZZMatrix)

Solves $Ax = b$ under $Cx >= 0$, assumes a finite solution set.
"""
function solve_mixed(A::ZZMatrix, b::ZZMatrix, C::ZZMatrix)  # Ax == b && Cx >= 0
  p = _polytope(A = A, b = b, C = C)
  inner = p.INTERIOR_LATTICE_POINTS
  out = p.BOUNDARY_LATTICE_POINTS

  res = zero_matrix(FlintZZ, nrows(inner) + nrows(out), ncols(A))
  for i=1:nrows(out)
    if out[i,1] != 1
      println("unbounded polytope!!")
      global last_in = (A, b, C)
    end
    @assert out[i,1] == 1
    for j=1:ncols(A)
      res[i,j] = out[i, j+1]
    end
  end
  for i=1:nrows(inner)
    if inner[i,1] != 1
      println("unbounded polytope!!")
      global last_in = (A, b, C)
    end
    @assert inner[i,1] == 1
    for j=1:ncols(A)
      res[i+nrows(out), j] = inner[i, j+1]
    end
  end
  return res
end

@doc raw"""
    solve_mixed(A::ZZMatrix, b::ZZMatrix, C::ZZMatrix, d::ZZMatrix)

Solves $Ax = b$ under $Cx >= d$, assumes a finite solution set.
"""
function solve_mixed(A::ZZMatrix, b::ZZMatrix, C::ZZMatrix, d::ZZMatrix)
  n = ncols(A)
  A = cat(A, identity_matrix(FlintZZ, ncols(d)), dims=(1,2))
  b = vcat(b, identity_matrix(FlintZZ, ncols(d)))
  C = [C -d; zero_matrix(FlintZZ, ncols(d), ncols(C)) identity_matrix(FlintZZ, ncols(d))]
  s = solve_mixed(A, b, C)
  return s[:, 1:n]
end

function Hecke.valuation(a::FacElem{ZZRingElem, ZZRing}, p::ZZRingElem)
  return sum(k*valuation(b, p) for (b, k) = a.fac)
end

function norm_equation2_fac_elem(R::AbsNumFieldOrder, k::ZZRingElem; abs::Bool = false)
  @assert Hecke.is_maximal(R)
  lp = factor(k*R)
  s, ms = Hecke.sunit_mod_units_group_fac_elem(collect(keys(lp)))
  C = reduce(vcat, [matrix(FlintZZ, 1, ngens(s), [valuation(ms(s[i]), p) for i=1:ngens(s)]) for p = keys(lp)])

  lp = factor(k)
  A = reduce(vcat, [matrix(FlintZZ, 1, ngens(s), [valuation(Hecke.factored_norm(ms(s[i])), p) for i=1:ngens(s)]) for p = keys(lp.fac)])
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


function norm_equation_fac_elem(R::AbsNumFieldOrder, k::ZZRingElem; abs::Bool = false)
  @assert Hecke.is_maximal(R)
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
    fl, g = is_principal_fac_elem(I)
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

norm_equation_fac_elem(R::AbsNumFieldOrder, k::Integer; abs::Bool = false) =
                            norm_equation_fac_elem(R, ZZRingElem(k), abs = abs)

function norm_equation(R::AbsNumFieldOrder, k::ZZRingElem; abs::Bool = false)
  s = norm_equation_fac_elem(R, k, abs = abs)
  return [R(evaluate(x)) for x = s]
end

norm_equation(R::AbsNumFieldOrder, k::Integer; abs::Bool = false) = norm_equation(R, ZZRingElem(k), abs = abs)

function norm_equation_fac_elem(R::Hecke.RelNumFieldOrder{AbsSimpleNumFieldElem,Hecke.AbsSimpleNumFieldOrderFractionalIdeal}, a::AbsSimpleNumFieldOrderElem)

  @assert Hecke.is_maximal(R)
  Ka, mKa, mkK = collapse_top_layer(nf(R))
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

  C = reduce(vcat, [matrix(FlintZZ, 1, ngens(q), [valuation(mS(preimage(mq, q[i])), p) for i=1:ngens(q)]) for p = keys(lp)])

  A = reduce(vcat, [matrix(FlintZZ, 1, ngens(q), [valuation(norm(mkK, mS(preimage(mq, g))), p) for g in gens(q)]) for p = keys(la)])
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
    fl, p = has_preimage_with_preimage(No, d)
    if fl
      push!(sol, FacElem(Dict(mKa(x) => v for (x, v) = (aa*inv(mU(p))).fac)))
    end
  end

  return sol
end

function Hecke.is_irreducible(a::AbsSimpleNumFieldOrderElem)
  if iszero(a)
    return false
  end
  O = parent(a)
  S = collect(keys(factor(a*O)))
  if length(S) == 0
    return false
  end
  s, ms = Hecke.sunit_mod_units_group_fac_elem(S)
  V = matrix([ZZRingElem[valuation(ms(x), y) for y = S] for x = gens(s)])
  b = matrix([ZZRingElem[valuation(a, y) for y = S]])
  sol = solve(V, b; side = :right)

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
  global last_irr = a
  pt = solve_mixed(A, sol, C, d)
  return nrows(pt) == 0
end

@doc raw"""
    irreducibles(S::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem}}) -> Vector{AbsNumFieldOrderElem}

Computes all irreducibles whose support is contained in $S$.
"""
function irreducibles(S::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem}})
  if length(S) == 0
    return []
  end
  @assert all(is_prime, S)
  #TODO: try to get a better bound - in general if S is too large
  #      it cannot work

  O = order(S[1])
  @assert all(x-> order(x) == O, S)

  s, ms = Hecke.sunit_mod_units_group_fac_elem(S)
  if length(S) == 1
    return [O(evaluate(ms(s[1])))]
  end
  c, mc = class_group(O)

  V = matrix([[valuation(ms(x), y) for y = S] for x = gens(s)])

  p = _polytope(C = V)
  z = p.HILBERT_BASIS_GENERATORS
  @assert nrows(z[2]) == 0 #no idea....
  res = [O(evaluate(ms(s(map(ZZRingElem, Array(z[1][i, 2:end])))))) for i=1:nrows(z[1]) if z[1][i,1] == 0]
  return res
end

@doc raw"""
    factorisations(a::AbsSimpleNumFieldOrderElem) -> Vector{Fac{OrdElem}}

Computes all factorisations of $a$ into irreducibles.
"""
function factorisations(a::AbsSimpleNumFieldOrderElem)
  O = parent(a)
  S = collect(keys(factor(a*O)))
  if length(S) == 0
    return []
  end
  irr = irreducibles(S)
  A = matrix([ZZRingElem[valuation(x, y) for y = S] for x = irr])
  b = matrix([ZZRingElem[valuation(a, y) for y = S]])
  sol = solve_non_negative(A, b)
  res = Fac{AbsSimpleNumFieldOrderElem}[]
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

function Base.lastindex(a::ZZMatrix, i::Int)
  i==1 && return nrows(a)
  i==2 && return ncols(a)
  error("illegal dimension")
end

export irreducibles, factorisations

end

using Main.PolymakeOscar
