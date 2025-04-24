################################################################################
#
#          RieSrf/PeriodMatrix.jl : Computing the period matrix
#
# (C) 2023 Jeroen Hanselman
#
################################################################################

function big_period_matrix(RS::RiemannSurface)

  g = genus(RS)
  diff_base = basis_of_differentials(RS)
  paths, _ = fundamental_group_of_punctured_P1(RS::RiemannSurface)
  num_paths = length(paths)
  
  disc_points = discriminant_points(RS)
  small_C = AcbField(100)
  disc_points_low_precision = [small_C(P) for P in disc_points]
  
  
  for path in paths
    gauss_legendre_path_parameters(disc_points_low_precision, path, RS.extra_error)
  end
  
end
