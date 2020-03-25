################################################################################
#
#  Lattice database
#
################################################################################

export number_of_lattices, lattice_name, lattice,
       lattice_automorphism_group_order, lattice_database

struct LatticeDB
  path::String
  max_rank::Int
  db::Vector{Vector{NamedTuple{(:name, :rank, :deg, :amb, :basis_mat, :min, :aut, :kissing),
                               Tuple{String, Int, Int, Vector{Rational{BigInt}}, Vector{Rational{BigInt}}, BigInt, BigInt, BigInt}}}}

  function LatticeDB(path::String)
    db = Meta.eval(Meta.parse(Base.read(path, String)))
    max_rank = length(db)
    return new(path, max_rank, db)
  end
end

# TODO: Write a parser for the data

function show(io::IO, L::LatticeDB)
  print(io, "Nebe-Sloan database of lattices (rank limit = ", L.max_rank, ")")
end

const default_lattice_db = Ref(joinpath(pkgdir, "data/lattices"))

################################################################################
#
#  For creating a lattice database
#
################################################################################

function lattice_database()
  if !isfile(joinpath(pkgdir, "data/lattices"))
    download_lattice_data()
  end
  return LatticeDB(default_lattice_db[])
end

function lattice_database(path::String)
  return LatticeDB(path)
end

################################################################################
#
#  Conversion from linear indicies
#
################################################################################

function from_linear_index(L::LatticeDB, i::Int)
  k = 1
  while i > length(L.db[k])
    i = i - length(L.db[k])
    k += 1
  end
  return (k, i)
end

################################################################################
#
#  Out of bounds error functions
#
################################################################################

@inline function _check_rank_range(L, r)
  r < 0 || r > L.max_rank &&
        throw(error("Rank ($(r)) must be between 1 and $(L.max_rank)"))
end

@inline function _check_range(L, r, i)
  r < 0 || r > L.max_rank &&
          throw(error("Rank ($(r)) must be between 1 and $(L.max_rank)"))
  j = number_of_lattices(L, r)
  i < 0 || i > j && throw(error("Index ($(i)) must be between 1 and $(j)"))
end

@inline function _check_range(L, i)
  j = number_of_lattices(L)
  i < 0 || i > j && throw(error("Index ($(i)) must be between 1 and $(j)"))
end

################################################################################
#
#  Access functions
#
################################################################################

function number_of_lattices(L::LatticeDB, r::Int)
  _check_rank_range(L, r)
  return length(L.db[r])
end

function number_of_lattices(L::LatticeDB)
  return sum(length.(L.db))
end

function lattice_name(L::LatticeDB, r::Int, i::Int)
  _check_range(L, r, i)
  return L.db[r][i].name
end

function lattice_name(L::LatticeDB, i::Int)
  _check_range(L, i)
  return lattice_name(L, from_linear_index(L, i)...)
end

function lattice_automorphism_group_order(L::LatticeDB, r::Int, i::Int)
  _check_range(L, r, i)
  return L.db[r][i].aut
end

function lattice_automorphism_group_order(L::LatticeDB, i::Int)
  _check_range(L, i)
  return lattice_automorphism_group_order(L, from_linear_index(L, i)...)
end

function lattice(L::LatticeDB, r::Int, i::Int)
  _check_range(L, r, i)
  d = L.db[r][i].deg
  A = matrix(FlintQQ, d, d, L.db[r][i].amb)
  B = matrix(FlintQQ, r, d, L.db[r][i].basis_mat)
  return Zlattice(B, gram = A)
end

function lattice(L::LatticeDB, i::Int)
  _check_range(L, i)
  return lattice(L, from_linear_index(L, i)...)
end

################################################################################
#
#  Quadratic lattices DB
#
################################################################################

const default_quad_lattice_db = Ref(joinpath(pkgdir, "data/quadratic_lattices"))

struct QuadLatDB
  path::String
  db::Vector{Tuple{Vector{BigInt}, Vector{Vector{Rational{BigInt}}}, Vector{Vector{Rational{BigInt}}}, Int}}

  function QuadLatDB(path::String)
    db = Meta.eval(Meta.parse(Base.read(path, String)))
    return new(path, db)
  end
end

function lattice(L::QuadLatDB, i::Int)
  data = L.db[i]
  f = Globals.Qx(data[1])
  K, a = NumberField(f, "a", cached = false)
  diag = map(K, data[2])
  gens = map(K, data[3])
  D = diagonal_matrix(diag)
  n = nrows(D)
  @assert iszero(mod(length(gens), n))
  k = div(length(gens), n)
  gens_split = collect(Iterators.partition(gens, k))
  return quadratic_lattice(K, generators = gens_split, gram_ambient_space = D)
end

function quadratic_lattice_database()
  if !isfile(joinpath(pkgdir, "data/quadratic_lattices"))
    download_lattice_data()
  end
  return QuadLatDB(default_quad_lattice_db[])
end

