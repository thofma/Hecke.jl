module PolymakeOscar

using Polymake, Hecke

Hecke.nrows(A::Polymake.pm_MatrixAllocated) = Int(size(A)[1])
Hecke.ncols(A::Polymake.pm_MatrixAllocated) = Int(size(A)[2])

#solves Ax <= b
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

function solve_mixed(A::fmpz_mat, b::fmpz_mat, C::fmpz_mat)  # Ax == b && Cx >= 0
  bA = Array{BigInt, 2}(hcat(-b, A))
  z = findall(i->!iszero_row(C, i), 1:nrows(C))
  zI = Array{BigInt, 2}(hcat(zero_matrix(FlintZZ, nrows(C), 1), C))[z, :]
  p = @pm Polytope.Polytope(:EQUATIONS => bA, :INEQUALITIES => zI)
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



end
