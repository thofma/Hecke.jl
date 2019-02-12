################################################################################
#
#  Small groups
#
################################################################################

export number_of_small_groups, small_group, small_groups_limit

const small_groups_limit = 63

include("small_groups_1_63")

function number_of_small_groups(i)
  return length(small_groups_1_63[i])
end

# Data in the DB:
# <gens, rels, nontrivrels, orderdis, ordersubdis, IsAbelian(G), IsCyclic(G),
# IsSolvable(G), IsNilpotent(G), #AutomorphismGroup(G);

function small_group(i, j)
  i < 1 || i > 63 && error("Group order ($i) must be between 1 and $small_groups_limit")
  j < 1 || j > number_of_small_groups(i) && error("Index ($j) must be between 1 and $(number_of_small_groups(i))")
  P = PermGroup(i)
  Gens = [P()]
  for p in small_groups_1_63[i][j][1]
    push!(Gens, P(p))
  end
  G, _, _ = generic_group(closure(Gens, *, P()), *)
  G.issolvable = small_groups_1_63[i][j][8] ? 1 : 2
  G.isnilpotent = small_groups_1_63[i][j][9] ? 1 : 2
  return G
end
