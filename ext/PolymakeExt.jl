module PolymakeExt

using Hecke, Polymake

import Hecke:
  solve_mixed,
  number_of_columns,
  number_of_rows

# Needs polymake (obviously)

# Returns all vectors v such that Av == b and Cv >= 0.

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
    p =  Polymake.polytope.Polytope(INEQUALITIES = zI)
  else
    if nrows(zI) == 0
      p = Polymake.polytope.Polytope(EQUATIONS = zbA)
    else
      p = Polymake.polytope.Polytope(EQUATIONS = zbA, INEQUALITIES = zI)
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
function Hecke.solve_mixed(A::ZZMatrix, b::ZZMatrix, C::ZZMatrix)  # Ax == b && Cx >= 0
  p = _polytope(A = A, b = b, C = C)
  inner = p.INTERIOR_LATTICE_POINTS
  out = p.BOUNDARY_LATTICE_POINTS

  res = zero_matrix(FlintZZ, (nrows(inner) + nrows(out))::Int, ncols(A)::Int)
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

end
