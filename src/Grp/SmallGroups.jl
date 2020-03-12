################################################################################
#
#  Small groups
#
################################################################################

export number_of_small_groups, small_group, small_groups_limit

#const small_groups_limit = 63
#
#include("small_groups_1_63")
#
#function number_of_small_groups(i)
#  return length(small_groups_1_63[i])
#end
#
#isfrom_db(G::GrpGen) = G.isfromdb

# Data in the DB:
# <gens, rels, nontrivrels, orderdis, ordersubdis, IsAbelian(G), IsCyclic(G),
# IsSolvable(G), IsNilpotent(G), #AutomorphismGroup(G);

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
