@testset "Database" begin
  DB = Hecke.lattice_database()
  L = lattice(DB, 1)
  @assert L isa ZZLat

  DB = Hecke.quadratic_lattice_database()
  L = lattice(DB, 1)
  @assert L isa QuadLat

  DB = Hecke.hermitian_lattice_database()
  L = lattice(DB, 1)
  @assert L isa HermLat
end
