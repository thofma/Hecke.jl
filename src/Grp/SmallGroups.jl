################################################################################
#
#  Small groups
#
################################################################################

using Pkg.Artifacts

#CF: as of now, nothing works here and the exports cause errors in Oscar

mutable struct SmallGroupDB
  path::String
  max_order::Int
  db::Vector{Vector{NamedTuple{(:id, :name, :gens, :rels, :nontrivrels,
                                :orderdis, :ordersubdis, :is_abelian, :is_cyclic,
                                :issolvable, :is_nilpotent, :autorder,
                                :aut_gens, :nchars, :dims, :schur, :galrep,
                                :fields, :mod),
                              Tuple{Tuple{Int, Int}, String, Vector{Perm{Int}},
                                    Vector{Vector{Int}}, Vector{Vector{Int}},
                                    Vector{Tuple{Int,Int}},
                                    Vector{Tuple{Int,Int}},
                                    Bool, Bool, Bool, Bool, ZZRingElem,
                                    Vector{Vector{Vector{Int}}}, Int,
                                    Vector{Int},Vector{Int}, Vector{Int},
                                    Vector{Vector{QQFieldElem}},
                                    Vector{Vector{Vector{Vector{QQFieldElem}}}}}}}}

end

function SmallGroupDB(path::String)
  db = Vector{NamedTuple{(:id, :name, :gens, :rels, :nontrivrels, :orderdis,
                          :ordersubdis, :is_abelian, :is_cyclic, :issolvable,
                          :is_nilpotent, :autorder, :aut_gens, :nchars, :dims,
                          :schur, :galrep, :fields, :mod),
                         Tuple{Tuple{Int, Int}, String, Vector{Perm{Int}},
                               Vector{Vector{Int}}, Vector{Vector{Int}},
                               Vector{Tuple{Int,Int}},
                               Vector{Tuple{Int,Int}}, Bool, Bool, Bool,
                               Bool, ZZRingElem, Vector{Vector{Vector{Int}}}, Int,
                               Vector{Int},Vector{Int}, Vector{Int},
                               Vector{Vector{QQFieldElem}},
                               Vector{Vector{Vector{Vector{QQFieldElem}}}}}}}[]
  z = eltype(eltype(db))[]
  open(path) do io
    while !eof(io)
    e = _parse_row(io)
    if isempty(z) || e.id[1] == z[1].id[1]
      push!(z, e)
    else
      push!(db, z)
      z = eltype(eltype(db))[]
      push!(z, e)
    end
  end
  push!(db, z)
  end
  max_order = length(db)
  return SmallGroupDB(path, max_order, db)
end

function SmallGroupDBLegacy(path::String)

  f = function(z)
    if z isa BigInt
      return ZZRingElem(z)
    elseif z isa Rational{BigInt}
      return QQFieldElem()
    elseif z isa Vector{Vector{Rational{BigInt}}}
      return Vector{QQFieldElem}[ QQFieldElem.(v) for v in z]
    elseif z isa Vector{Vector{Vector{Vector{Rational{BigInt}}}}}
      zz = Vector{Vector{Vector{Vector{QQFieldElem}}}}(undef, length(z))
      for i in 1:length(z)
        zz[i] = Vector{Vector{Vector{QQFieldElem}}}(undef, length(z[i]))
        for j in 1:length(z[i])
          zz[i][j] = Vector{Vector{QQFieldElem}}(undef, length(z[i][j]))
          for k in 1:length(z[i][j])
            zz[i][j][k] = QQFieldElem.(z[i][j][k])
          end
        end
      end
      return zz
    else
      return z
    end
  end

  dbnew = Vector{NamedTuple{(:id, :name, :gens, :rels, :nontrivrels, :orderdis,
                          :ordersubdis, :is_abelian, :is_cyclic, :issolvable,
                          :is_nilpotent, :autorder, :aut_gens, :nchars, :dims,
                          :schur, :galrep, :fields, :mod),
                         Tuple{Tuple{Int, Int}, String, Vector{Perm{Int}},
                               Vector{Vector{Int}}, Vector{Vector{Int}},
                               Vector{Tuple{Int,Int}},
                               Vector{Tuple{Int,Int}}, Bool, Bool, Bool,
                               Bool, ZZRingElem, Vector{Vector{Vector{Int}}}, Int,
                               Vector{Int},Vector{Int}, Vector{Int},
                               Vector{Vector{QQFieldElem}},
                               Vector{Vector{Vector{Vector{QQFieldElem}}}}}}}[]

  db = Hecke.eval(Meta.parse(Base.read(path, String)))
  for i in 1:length(db)
    push!(dbnew, eltype(dbnew)(undef, length(db[i])))
    for j in 1:length(db[i])
      v = db[i][j]
      vv = map(f, v)
      dbnew[i][j] = (id = (i, j), vv...)
    end
  end

  max_order = length(dbnew)
  return SmallGroupDB(path, max_order, dbnew)
end

function show(io::IO, L::SmallGroupDB)
  print(io, "Database of small groups (order limit = ", L.max_order, ")")
end

const legacy_default_small_group_db = [joinpath(pkgdir, "data/small_groups_extended"), joinpath(pkgdir, "data/small_groups_default")]

function small_group_database()
  st = artifact"SmallGroupDB"
  return SmallGroupDB(joinpath(st, "SmallGroupDB", "data"))
end

const _DefaultSmallGroupDB = Ref{Any}(nothing)

function DefaultSmallGroupDB()
  _DB = _DefaultSmallGroupDB[]
  if _DefaultSmallGroupDB[] === nothing
    DB = small_group_database()
    _DefaultSmallGroupDB[] = DB
    return DB::SmallGroupDB
  else
    return _DB::SmallGroupDB
  end
end

is_from_db(G::MultTableGroup) = G.isfromdb

function small_group(i, j; DB = DefaultSmallGroupDB())
  data = DB.db[i][j]
  #i < 1 || i > 63 && error("Group order ($i) must be between 1 and $small_groups_limit")
  #j < 1 || j > number_of_small_groups(i) && error("Index ($j) must be between 1 and $(number_of_small_groups(i))")
  P = SymmetricGroup(i)
  Gens = [one(P)]
  for p in data.gens
    push!(Gens, P(p))
  end
  G, PtoG, GtoP = generic_group(closure(Gens, *, one(P)), *)

  # The small groups have generators, for which we know
  # generators for the relations.
  # This is used in the homomorphism computation.
  # To make this work, the generators must much exactly
  # with the generators in the database.
  G.gens = Vector{Int}(undef, length(data.gens))
  for k in 1:length(data.gens)
    p = data.gens[k]
    G.gens[k] = PtoG[P(p)][]
  end

  G.issolvable = data.issolvable
  G.is_nilpotent = data.is_nilpotent
  G.isfromdb = true
  G.small_group_id = (i, j)
  return G
end

################################################################################
#
#  Better parsing
#
################################################################################

function _parse_row(io::IO)
  b = Base.read(io, UInt8)
  # id
  b, id = _parse(Tuple{Int, Int}, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, name = _parse(String, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, gens = _parse(Vector{Perm{Int}}, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, rels = _parse(Vector{Vector{Int}}, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, nontrivrels = _parse(Vector{Vector{Int}}, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, orderdis = _parse(Vector{Tuple{Int, Int}}, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, ordersubdis = _parse(Vector{Tuple{Int, Int}}, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, is_abelian = _parse(Bool, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, is_cyclic = _parse(Bool, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, issolvable = _parse(Bool, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, is_nilpotent = _parse(Bool, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, autorder = _parse(ZZRingElem, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, aut_gens = _parse(Vector{Vector{Vector{Int}}}, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, nchars = _parse(Int, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, dims = _parse(Vector{Int}, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, schur = _parse(Vector{Int}, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, galrep = _parse(Vector{Int}, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, fields = _parse(Vector{Vector{QQFieldElem}}, io, b)
  @assert b == UInt(',')
  b = Base.read(io, UInt8)
  b, mod = _parse(Vector{Vector{Vector{Vector{QQFieldElem}}}}, io, b)
  return (id = id, name = name, gens = gens, rels = rels, nontrivrels = nontrivrels, orderdis = orderdis,
          ordersubdis = ordersubdis, is_abelian = is_abelian, is_cyclic = is_cyclic, issolvable = issolvable,
          is_nilpotent = is_nilpotent, autorder = autorder, aut_gens = aut_gens, nchars = nchars, dims = dims,
          schur = schur, galrep = galrep, fields = fields, mod = mod)
end
