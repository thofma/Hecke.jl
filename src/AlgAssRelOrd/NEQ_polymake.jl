# Stolen from examples/polymake.jl
# Needs polymake (obviously)

# Returns all vectors v such that Av == b and Cv >= 0.
function solve_mixed(A::fmpz_mat, b::fmpz_mat, C::fmpz_mat)
  bA = Array{BigInt, 2}(hcat(-b, A))
  z = findall(i->!iszero_row(C, i), 1:nrows(C))
  zI = Array{BigInt, 2}(hcat(zero_matrix(FlintZZ, nrows(C), 1), C))[z, :]
  p = polytope.Polytope(EQUATIONS = bA, INEQUALITIES = zI)

  res = Vector{fmpz_mat}(undef, p.N_LATTICE_POINTS)
  if p.N_LATTICE_POINTS == 0
    return res
  end

  inner_points = p.INTERIOR_LATTICE_POINTS
  boundary_points = p.BOUNDARY_LATTICE_POINTS

  for i = 1:Int(size(boundary_points)[1]) # "==" nrows(boundary_points)
    @assert boundary_points[i, 1] == 1
    c = zero_matrix(FlintZZ, 1, ncols(A))
    for j = 1:ncols(A)
      c[1, j] = boundary_points[i, j + 1]
    end
    res[i] = c
  end

  for i = 1:Int(size(inner_points)[1])
    @assert inner_points[i, 1] == 1
    c = zero_matrix(FlintZZ, 1, ncols(A))
    for j = 1:ncols(A)
      c[1, j] = inner_points[i, j + 1]
    end
    res[i + Int(size(boundary_points)[1])] = c
  end
  return res
end

