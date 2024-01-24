################################################################################
#
#  Lattice database
#
################################################################################

struct LatDB
  path::String
  max_rank::Int
  db::Vector{Vector{NamedTuple{(:name, :rank, :deg, :amb, :basis_mat, :min, :aut, :kissing),
                               Tuple{String, Int, Int, Vector{Rational{BigInt}}, Vector{Rational{BigInt}}, BigInt, BigInt, BigInt}}}}

  function LatDB(path::String)
    db = Meta.eval(Meta.parse(Base.read(path, String)))
    max_rank = length(db)
    return new(path, max_rank, db)
  end
end

# TODO: Write a parser for the data

function Base.show(io::IO, ::MIME"text/plain", L::LatDB)
  println(io, "Definite integer lattices of rank <= ", L.max_rank)
  println(io, "Author: Gabriele Nebe and Neil Sloane")
  println(io, "Source: http://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/index.html")
  print(io, "Number of lattices: ", number_of_lattices(L))
end

function Base.show(io::IO, L::LatDB)
  if get(io, :supercompact, false)
    print(io, "Integer lattices database")
  else
    print(io, "Nebe-Sloan database of lattices (rank limit = ", L.max_rank, ")")
  end
end

const default_lattice_db = Ref(joinpath(artifact"ZLatDB", "ZLatDB", "data"))

################################################################################
#
#  For creating a lattice database
#
################################################################################

function lattice_database()
  return LatDB(default_lattice_db[])
end

function lattice_database(path::String)
  return LatDB(path)
end

################################################################################
#
#  Conversion from linear indices
#
################################################################################

function from_linear_index(L::LatDB, i::Int)
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
        error("Rank ($(r)) must be between 1 and $(L.max_rank)")
end

@inline function _check_range(L, r, i)
  r < 0 || r > L.max_rank &&
          error("Rank ($(r)) must be between 1 and $(L.max_rank)")
  j = number_of_lattices(L, r)
  i < 0 || i > j && error("Index ($(i)) must be between 1 and $(j)")
end

@inline function _check_range(L, i)
  j = number_of_lattices(L)
  i < 0 || i > j && error("Index ($(i)) must be between 1 and $(j)")
end

################################################################################
#
#  Access functions
#
################################################################################

function number_of_lattices(L::LatDB, r::Int)
  _check_rank_range(L, r)
  return length(L.db[r])
end

function number_of_lattices(L::LatDB)
  return sum(length.(L.db))
end

function lattice_name(L::LatDB, r::Int, i::Int)
  _check_range(L, r, i)
  return L.db[r][i].name
end

function lattice_name(L::LatDB, i::Int)
  _check_range(L, i)
  return lattice_name(L, from_linear_index(L, i)...)
end

function lattice_automorphism_group_order(L::LatDB, r::Int, i::Int)
  _check_range(L, r, i)
  return L.db[r][i].aut
end

function lattice_automorphism_group_order(L::LatDB, i::Int)
  _check_range(L, i)
  return lattice_automorphism_group_order(L, from_linear_index(L, i)...)
end

function lattice(L::LatDB, r::Int, i::Int)
  _check_range(L, r, i)
  d = L.db[r][i].deg
  A = matrix(FlintQQ, d, d, L.db[r][i].amb)
  B = matrix(FlintQQ, r, d, L.db[r][i].basis_mat)
  return integer_lattice(B, gram = A)
end

function lattice(L::LatDB, i::Int)
  _check_range(L, i)
  return lattice(L, from_linear_index(L, i)...)
end

################################################################################
#
#  Quadratic lattices DB
#
################################################################################

const default_quad_lattice_db = Ref(joinpath(artifact"QuadLatDB", "QuadLatDB", "data"))

struct QuadLatDB
  path::String
  #db::Vector{Tuple{Vector{BigInt}, Vector{Vector{Rational{BigInt}}}, Vector{Vector{Rational{BigInt}}}, Int}}
  metadata
  head::Int
  length::Int

  function QuadLatDB(path::String)
    metadata = Dict()
    f = open(path)
    head = 0
    while true
      line = readline(f)
      if line[1] == '#'
        head += 1
        if !(':' in line)
          continue
        end
        i = 2
        while line[i] != ':'
          i += 1
        end
        key = strip(line[2:i-1])
        val = strip(line[i+1:end])
        metadata[key] = val
      else
        break
      end
    end
    seekstart(f)
    length = countlines(f)
    close(f)
    return new(path, metadata, head, length - head)
  end
end

function quadratic_lattice_database()
  return QuadLatDB(default_quad_lattice_db[])
end

function quadratic_lattice_database(path::String)
  return QuadLatDB(path)
end

Base.length(D::QuadLatDB) = D.length

class_number(D::QuadLatDB, i::Int) = _lattice_data(D, i)[4]

function Base.show(io::IO, ::MIME"text/plain", D::QuadLatDB)
  s = get(D.metadata, "Description", "Quadratic lattices database")
  print(io, s, "\n")
  if haskey(D.metadata, "Author")
    print(io, "Author: $(D.metadata["Author"])\n")
  end
  if haskey(D.metadata, "Source")
    print(io, "Source: $(D.metadata["Source"])\n")
  end
  if haskey(D.metadata, "Version")
    print(io, "Version: $(VersionNumber(D.metadata["Version"]))\n")
  end

  print(io, "Number of lattices: ", D.length)
end

function Base.show(io::IO, D::QuadLatDB)
  if get(io, :supercompact, false)
    print(io, "Quadratic lattices database")
  else
    s = get(D.metadata, "Description", "Quadratic lattices database")
    print(io, s)
  end
end

function versioninfo(D::QuadLatDB)
  return VersionNumber(D.metadata["Version"])
end

function _lattice_data(D::QuadLatDB, i::Int)
  it = Iterators.drop(eachline(D.path), D.head + i - 1)
  line = IOBuffer(first(it))
  return _parse_quad(line, versioninfo(D))
end

function lattice(D::QuadLatDB, i::Int)
  return _get_lattice(_lattice_data(D, i))
end

function _get_lattice(data)
  f = Globals.Qx(data[1])
  K, a = number_field(f, "a", cached = false)
  diag = map(K, data[2])
  gens = map(K, data[3])
  D = diagonal_matrix(diag)
  n = nrows(D)
  @assert iszero(mod(length(gens), n))
  gens_split = collect(Iterators.partition(gens, n))
  gens_split = Vector{elem_type(K)}[collect(g) for g in gens_split]
  return quadratic_lattice(K, gens_split, gram = D)
end

################################################################################
#
#  Hermitian lattices DB
#
################################################################################

const default_herm_lattice_db = Ref(joinpath(artifact"HermLatDB", "HermLatDB", "data"))

struct HermLatDB
  path::String
  #db::Vector{Tuple{Vector{BigInt}, Vector{Vector{Rational{BigInt}}}, Vector{Vector{Rational{BigInt}}}, Int}}
  metadata
  head::Int
  length::Int

  function HermLatDB(path::String)
    metadata = Dict()
    f = open(path)
    head = 0
    while true
      line = readline(f)
      if line[1] == '#'
        head += 1
        if !(':' in line)
          continue
        end
        i = 2
        while line[i] != ':'
          i += 1
        end
        key = strip(line[2:i-1])
        val = strip(line[i+1:end])
        metadata[key] = val
      else
        break
      end
    end
    seekstart(f)
    length = countlines(f)
    close(f)
    return new(path, metadata, head, length - head)
  end
end

function hermitian_lattice_database()
  return HermLatDB(default_herm_lattice_db[])
end

function hermitian_lattice_database(path::String)
  return HermLatDB(path)
end

Base.length(D::HermLatDB) = D.length

class_number(D::HermLatDB, i::Int) = _lattice_data(D, i)[5]

function Base.show(io::IO, ::MIME"text/plain", D::HermLatDB)
  s = get(D.metadata, "Description", "Hermitian lattices database")
  print(io, s, "\n")
  if haskey(D.metadata, "Author")
    print(io, "Author: $(D.metadata["Author"])\n")
  end
  if haskey(D.metadata, "Source")
    print(io, "Source: $(D.metadata["Source"])\n")
  end
  if haskey(D.metadata, "Version")
    print(io, "Version: $(VersionNumber(D.metadata["Version"]))\n")
  end

  print(io, "Number of lattices: ", D.length)
end

function Base.show(io::IO, D::HermLatDB)
  if get(io, :supercompact, false)
    print(io, "Hermitian lattices database")
  else
    s = get(D.metadata, "Description", "Hermitian lattices database")
    print(io, s)
  end
end

function versioninfo(D::HermLatDB)
  return VersionNumber(D.metadata["Version"])
end

function _lattice_data(D::HermLatDB, i::Int)
  it = Iterators.drop(eachline(D.path), D.head + i - 1)
  line = IOBuffer(first(it))
  return _parse_herm(line, versioninfo(D))
end

function lattice(D::HermLatDB, i::Int)
  return _get_hermitian_lattice(_lattice_data(D, i))
end

function _get_hermitian_lattice(data)
  f = Globals.Qx(data[1])
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t", cached = false)
  E, b = number_field(Kt(map(K, data[2])), "b", cached = false)
  diag = map(E, map(K, data[3]))
  k = degree(K)
  #gens = [ E(map(K, collect(Iterators.partition(v, k))))  map(E, data[4])
  D = diagonal_matrix(diag)
  n = nrows(D)
  @assert iszero(mod(length(data[4]), n))
  gens_split = collect(Iterators.partition(data[4], n))
  gens = Vector{elem_type(E)}[]
  for v in gens_split
    push!(gens, map(E, [map(K, collect(Vector.(Iterators.partition(w, k)))) for w in v]))
  end
  return hermitian_lattice(E, gens, gram = D)
end

################################################################################
#
#  Parse
#
################################################################################

base_type(::Type{QQFieldElem}) = ZZRingElem

base_type(::Type{Rational{T}}) where {T} = T

function parse_int(io, delim = UInt8[UInt8(',')])
  n = IOBuffer()
  b = Base.read(io, UInt8)
  while !(b in delim)
    Base.write(n, b)
    if eof(io)
      break
    end
    b = Base.read(io, UInt8)
  end

  return b, parse(Int, String(take!(n)))
end

function parse_rational(::Type{T}, io, delim = [UInt8(',')]) where {T}
  n = IOBuffer()
  d = IOBuffer()
  read_den = false
  b = Base.read(io, UInt8)
  while !(b in delim)
    if b == UInt8('/')
      read_den = true
      skip(io, 1)
      @goto read
    end

    if !read_den
      Base.write(n, b)
    else
      Base.write(d, b)
    end

    @label read
    if eof(io)
      break
    end
    b = Base.read(io, UInt8)
  end

  nu = String(take!(n))

  if length(nu) < 18
    num = base_type(T)(parse(Int, nu))
  else
    num = parse(base_type(T), nu)
  end

  if !read_den
    return b, T(num)
  else
    de = String(take!(d))
    if length(de) < 18
      den = base_type(T)(parse(Int, de))
    else
      den = parse(base_type(T), de)
    end
    return b, num//den
  end
end

function parse_array(::Type{T}, io, ldelim = '[', rdelim = ']') where {T}
  res = Vector{T}()
  b = Base.read(io, UInt8)
  @assert b == UInt8(ldelim)
  mark(io)
  b = Base.read(io, UInt8)
  if b == UInt8(rdelim)
    return b, res
  else
    reset(io)
    unmark(io)
    while true
      b, z = parse_rational(T, io, map(UInt8, [',', rdelim]))
      push!(res, z)
      if b != UInt8(',')
        @assert b == UInt8(rdelim)
        break
      end
    end
    return b, res
  end
end

function parse_array(::Type{Vector{T}}, io, ldelim = '[', rdelim = ']') where {T}
  res = Vector{Vector{T}}()
  b = Base.read(io, UInt8)
  @assert b == UInt8(ldelim)
  mark(io)
  b = Base.read(io, UInt8)
  if b == rdelim
    return res
  else
    reset(io)
    unmark(io)
    while true
      b, z = parse_array(T, io)
      push!(res, z)
      b = Base.read(io, UInt8)
      if b == UInt8(rdelim)
        break
      end
      if b != UInt8(',')
        @assert b == UInt8(rdelim)
        break
      end
    end
    return res
  end
end

#db::Vector{Tuple{Vector{BigInt}, Vector{Vector{Rational{BigInt}}}, Vector{Vector{Rational{BigInt}}}, Int}}
function _parse_quad(io, version)
  @assert version == v"0.0.1"
  b, def_poly = parse_array(QQFieldElem, io)
  @assert b == UInt8(']')
  b = Base.read(io, UInt8)
  @assert b == UInt8(',')
  diagonal = parse_array(Vector{QQFieldElem}, io)
  b = Base.read(io, UInt8)
  @assert b == UInt8(',')
  gens = parse_array(Vector{QQFieldElem}, io)
  b = Base.read(io, UInt8)
  @assert b == UInt8(',')
  b, cl = parse_int(io)
  return def_poly, diagonal, gens, cl
end

function _parse_herm(io, version)
  @assert version == v"0.0.1"
  b, def_poly = parse_array(QQFieldElem, io)
  @assert b == UInt8(']')
  b = Base.read(io, UInt8)
  @assert b == UInt8(',')
  ext_poly = parse_array(Vector{QQFieldElem}, io)
  b = Base.read(io, UInt8)
  @assert b == UInt8(',')
  diagonal = parse_array(Vector{QQFieldElem}, io)
  b = Base.read(io, UInt8)
  @assert b == UInt8(',')
  gens = parse_array(Vector{QQFieldElem}, io)
  b = Base.read(io, UInt8)
  @assert b == UInt8(',')
  b, cl = parse_int(io)
  return def_poly, ext_poly, diagonal, gens, cl
end

