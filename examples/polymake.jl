module PolymakeOscar

using Polymake, Hecke

Hecke.rows(A::Polymake.pm_MatrixAllocated) = Int(size(A)[1])
Hecke.cols(A::Polymake.pm_MatrixAllocated) = Int(size(A)[2])

#solves Ax <= b
function solve_ineq(A::fmpz_mat, b::fmpz_mat)
  bA = Array{BigInt, 2}(hcat(-b, A))
  p = Polymake.perlobj( "Polytope<Rational>", Dict("INEQUALITIES" => bA))
  inner = Polymake.give(p, "INTERIOR_LATTICE_POINTS")
  out = Polymake.give(p, "BOUNDARY_LATTICE_POINTS")

  res = zero_matrix(FlintZZ, rows(inner) + rows(out), cols(A))
  for i=1:rows(out)
    @assert out[i,1] == 1
    for j=1:cols(A)
      res[i,j] = out[i, j+1]
    end
  end
  for i=1:rows(inner)
    @assert inner[i,1] == 1
    for j=1:cols(A)
      res[i+rows(out), j] = inner[i, j+1]
    end
  end
  return res
end

function solve_non_negative(A::fmpz_mat, b::fmpz_mat)
  bA = Array{BigInt, 2}(hcat(-b, A))
  zI = Array{BigInt, 2}(hcat(zero_matrix(FlintZZ, cols(A), 1), MatrixSpace(FlintZZ, cols(A), cols(A))(1)))
  p = Polymake.perlobj( "Polytope<Rational>", Dict("EQUATIONS" => bA, 
                                                   "INEQUALITIES" => zI))
  inner = Polymake.give(p, "INTERIOR_LATTICE_POINTS")
  out = Polymake.give(p, "BOUNDARY_LATTICE_POINTS")

  res = zero_matrix(FlintZZ, rows(inner) + rows(out), cols(A))
  for i=1:rows(out)
    @assert out[i,1] == 1
    for j=1:cols(A)
      res[i,j] = out[i, j+1]
    end
  end
  for i=1:rows(inner)
    @assert inner[i,1] == 1
    for j=1:cols(A)
      res[i+rows(out), j] = inner[i, j+1]
    end
  end
  return res
end

function norm_equation_fac_elem(R::NfAbsOrd, k::fmpz; abs::Bool = false)
  @assert Hecke.ismaximal(R)
  lp = factor(k)
  S = []
  for (p, k) = lp.fac
    P = prime_decomposition(R, p)
    s = solve_non_negative(matrix(FlintZZ, 1, length(P), [degree(x[1]) for x = P]), matrix(FlintZZ, 1, 1, [k]))
    push!(S, (P, [view(s, i:i, 1:cols(s)) for i=1:rows(s)]))
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

end
