# This is a list of transitive Frobenius groups G with abelian Frobenius
# kernel K and solvable H = G/K and degree(G) <= 30.
#
# Frob := []l;
# for i in [1..30] do
#   for j in [1..NumberOfTransitiveGroups(i)] do
#     G := TransitiveGroup(i, j);
#     fl := IsFrobenius(G);
#     if not fl then
#       continue;
#     end if;
#     i, j, GroupName(G);
#     Append(~Frob, <i, jj>);
#   end for;
# end for
#
# for ID in Frob do
#   G := TransitiveGroup(ID[1], ID[2]);
#   K := FittingSubgroup(G);
#   sid := IdentifyGroup(G);
#   H := Complements(G, K);
#   assert #H eq 1; H := H[1];
#   if not IsSolvable(H) or not IsAbelian(K) then
#     continue;
#   end if;
#   <sid, IdentifyGroup(H), InvariantFactors(AbelianGroup(K))>;
#   end for;
#
# For each Frobenius group we store we have a pair
# SID -> (KID, H)
# where
#  - SID is the small group ID
#  - KID is the small group ID of G/K
#  - H is the list of invariant factors of K.

global _frobenius_groups = Dict{Tuple{Int, Int}, Tuple{Tuple{Int, Int}, Vector{Int}}}(
  (600, 150) => ((24, 3), [5, 5]),
  (342, 7) => ((18, 2), [19]),
  (39, 1) => ((3, 1), [13]),
  (300, 24) => ((12, 2), [5, 5]),
  (600, 149) => ((24, 2), [5, 5]),
  (406, 1) => ((14, 2), [29]),
  (203, 1) => ((7, 1), [29]),
  (702, 47) => ((26, 2), [3, 3, 3]),
  (56, 11) => ((7, 1), [2, 2, 2]),
  (34, 1) => ((2, 1), [17]),
  (50, 1) => ((2, 1), [25]),
  (150, 6) => ((6, 2), [5, 5]),
  (54, 7) => ((2, 1), [3, 9]),
  (10, 1) => ((2, 1), [5]),
  (18, 1) => ((2, 1), [9]),
  (26, 1) => ((2, 1), [13]),
  (42, 1) => ((6, 2), [7]),
  (80, 49) => ((5, 1), [2, 2, 2, 2]),
  (136, 12) => ((8, 1), [17]),
  (46, 1) => ((2, 1), [23]),
  (156, 7) => ((12, 2), [13]),
  (57, 1) => ((3, 1), [19]),
  (21, 1) => ((3, 1), [7]),
  (38, 1) => ((2, 1), [19]),
  (78, 1) => ((6, 2), [13]),
  (48, 3) => ((3, 1), [4, 4]),
  (351, 12) => ((13, 1), [3, 3, 3]),
  (84, 11) => ((3, 1), [2, 14]),
  (22, 1) => ((2, 1), [11]),
  (300, 23) => ((12, 1), [5, 5]),
  (14, 1) => ((2, 1), [7]),
  (30, 3) => ((2, 1), [15]),
  (42, 5) => ((2, 1), [21]),
  (100, 11) => ((4, 1), [5, 5]),
  (36, 9) => ((4, 1), [3, 3]),
  (55, 1) => ((5, 1), [11]),
  (114, 1) => ((6, 2), [19]),
  (110, 1) => ((10, 2), [11]),
  (812, 7) => ((28, 2), [29]),
  (48, 50) => ((3, 1), [2, 2, 2, 2]),
  (54, 14) => ((2, 1), [3, 3, 3]),
  (100, 12) => ((4, 1), [5, 5]),
  (72, 39) => ((8, 1), [3, 3]),
  (6, 1) => ((2, 1), [3]),
  (52, 3) => ((4, 1), [13]),
  (12, 3) => ((3, 1), [2, 2]),
  (253, 1) => ((11, 1), [23]),
  (200, 40) => ((8, 1), [5, 5]),
  (171, 3) => ((9, 1), [19]),
  (68, 3) => ((4, 1), [17]),
  (200, 44) => ((8, 4), [5, 5]),
  (600, 148) => ((24, 1), [5, 5]),
  (272, 50) => ((16, 1), [17]),
  (54, 1) => ((2, 1), [27]),
  (506, 1) => ((22, 2), [23]),
  (72, 41) => ((8, 4), [3, 3]),
  (240, 191) => ((15, 1), [2, 2, 2, 2]),
  (58, 1) => ((2, 1), [29]),
  (50, 4) => ((2, 1), [5, 5]),
  (18, 4) => ((2, 1), [3, 3]),
  (116, 3) => ((4, 1), [29]),
  (100, 3) => ((4, 1), [25]),
  (20, 3) => ((4, 1), [5]),
  (75, 2) => ((3, 1), [5, 5])
)

function Hecke.primitive_frobenius_extensions(::QQField, id::Tuple{Int, Int}, B::ZZRingElem; only_real::Bool = false, only_non_real::Bool = false)
  @req haskey(_frobenius_groups, id) "id ($id) must be small group id of a transitive Frobenius group " *
                                     "with abelian Frobenius kernel and solvable quotient and degree " *
                                     "bounded by 30."
  @req !(only_real && only_non_real) "Either \"only_real\" or \"only_non_real\" must be set"
  sid, invfac = _frobenius_groups[id]
  R = ArbField(64, cached = false)
  res = AbsSimpleNumField[]
  maxB = ZZRingElem(1)
  reldeg = prod(invfac)
  k = 1
  s = (reldeg - 1)//sid[1] # (|F| - 1)/|H|
  #Ms = abelian_fields(QQ, [l], max(ZZRingElem(1), upper_bound(ZZRingElem, R(B)^(1//s))))
  Ms = Hecke.fields(sid[1], sid[2], max(ZZRingElem(1), Hecke.upper_bound(ZZRingElem, R(B)^(1//s))))
  ll = length(Ms)
  target_id = id

  for M in Ms
    k += 1
    Mnf = number_field(M)
    Mabs = Mnf
    dM = abs(discriminant(maximal_order(Mabs)))

    newB = Hecke.upper_bound(ZZRingElem, (B//R(dM)^s)^sid[1] * dM^reldeg)

    # If I want only real degree l fields, then the normal closure N can be anything
    #
    # If I want only non-real degree l fields, then the normal closure must not be real,
    # hence must be totally complex.
    kk = 1
    Ns = abelian_normal_extensions(Mabs, invfac, newB, only_complex = only_non_real)

    for N in Ns
      kk += 1
      Nabs, = absolute_simple_field(number_field(N, using_norm_relation = true))
      _A = absolute_automorphism_group(N)
      _A = closure(_A, *)
      id, = Hecke.find_small_group(generic_group(_A, *)[1])
      if id != target_id
        continue
      end

      A = automorphism_list(Nabs)
      N, AtoN, NtoA = generic_group(A, *)

      cur = nothing

      for (K, KtoN) in subgroups(N, normal = true)
        _,KK, = Hecke.find_small_group(K)
        if KK.is_nilpotent == 1 && (cur === nothing || order(KK) > order(cur[1]))
          cur = K, KtoN
        end
        if cur !== nothing && order(cur[1]) == reldeg
          break
        end
      end
      K, KtoN = cur
      @assert order(K) == reldeg
      # I found a kernel
      # Now find a complement
      comp = (K, KtoN)
      KinN = [ KtoN(k) for k in K]
      for (H, HtoN) in subgroups(N, order = sid[1])
        HinN = [HtoN(h) for h in H]
        if length(unique!([ k * h for k in KinN for h in HinN ])) == order(N)
          comp = (H, HtoN)
          break
        end
      end

      H, HtoN = comp
      @assert order(H) == sid[1]
      # trigger better automorphism group computation
      lll(maximal_order(Nabs))

      target_field,  = fixed_field1(Nabs, [ NtoA[HtoN(k)] for k in gens(H) ])
      @assert abs(discriminant(maximal_order(target_field))) <= B
      # In the only_non_real case, we already have the right fields,
      if (!only_real && !only_non_real) || (only_non_real && !is_totally_real(target_field)) || (only_real && is_totally_real(target_field))
        push!(res, target_field)
      end
    end
  end
  return res
end
