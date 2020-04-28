################################################################################
#
#  Small groups
#
################################################################################

#export number_of_small_groups, small_groups_limit
export small_group
#CF: as of now, nothing works here and the exports cause errors in Oscar

mutable struct SmallGroupDB
  path::String
  max_order::Int
  db::Vector{Vector{NamedTuple{(:name, :gens, :rels, :nontrivrels, :orderdis,
                                :ordersubdis, :isabelian, :iscyclic,
                                :issolvable, :isnilpotent, :autorder, :aut_gens,
                                :nchars, :dims, :schur, :galrep, :fields, :mod),
                               Tuple{String,Array{Perm{Int64},1},
                                     Vector{Vector{Int64}},
                                     Vector{Vector{Int64}},
                                     Vector{Tuple{Int64,Int64}},
                                     Vector{Tuple{Int64,Int64}},
                                     Bool,Bool,Bool,Bool,BigInt,
                                     Vector{Vector{Vector{Int64}}},Int64,
                                     Vector{Int64},Vector{Int64}, Vector{Int},
                                     Vector{Vector{Rational{BigInt}}},
                                     Vector{Vector{Vector{Vector{Rational{BigInt}}}}}}}}}

  function SmallGroupDB(path::String)
    db = Hecke.eval(Meta.parse(Base.read(path, String)))
    max_order = length(db)
    return new(path, max_order, db)
  end
end

# TODO: Write a parser for the data

function show(io::IO, L::SmallGroupDB)
  print(io, "Database of small groups (order limit = ", L.max_order, ")")
end

const default_small_group_db = [joinpath(pkgdir, "data/small_groups_extended"), joinpath(pkgdir, "data/small_groups_default")]

function small_group_database()
  for pa in default_small_group_db
    if isfile(pa)
      return SmallGroupDB(pa)
    end
  end
  throw(error("No database for small groups found"))
end

const DefaultSmallGroupDB = small_group_database()

isfrom_db(G::GrpGen) = G.isfromdb

function small_group(i, j)
  data = DefaultSmallGroupDB.db[i][j]
  #i < 1 || i > 63 && error("Group order ($i) must be between 1 and $small_groups_limit")
  #j < 1 || j > number_of_small_groups(i) && error("Index ($j) must be between 1 and $(number_of_small_groups(i))")
  P = SymmetricGroup(i)
  Gens = [P()]
  for p in data.gens
    push!(Gens, P(p))
  end
  G, PtoG, GtoP = generic_group(closure(Gens, *, P()), *)

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
  G.isnilpotent = data.isnilpotent
  G.isfromdb = true
  G.small_group_id = (i, j)
  return G
end
