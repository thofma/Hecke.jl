# Algorithm for right class set of a quaternion order.
# See Appendix by Voight in Smit-Marseglia, "Ideal classes of orders in
# quaternion algebras".
#
# The code is inspired by the Magma implementation in
# https://github.com/dansme/hermite by Smertnig-Voight
#
# TODO: - type number
#       - has_locally_free_cancellation/is_hermite
#       - has_stably_free_cancellation
#       - has_stably_free_cancellation_using_classification
#       - put the data from test in src
#       - redo the calculations

_prime_ideals_over(R::ZZRing, pe) = pe

_prime_ideals_over(R, pe) = prime_ideals_over(R, pe)

_prime_ideals_up_to(R, B) = prime_ideals_up_to(R, B)

_prime_ideals_up_to(R::ZZRing, B) = collect(PrimesSet(2, B))

function right_class_set(O::Union{AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}}, AlgAssRelOrd})
#    { Compute the right class set of a quaternion order O in a naive way.
#      This code is originally by Voight (also appears as commented out code in
#      ideals-jv.m). Some small modifications have been made.
#
#      We use this naive version, because it works for any order.
#    }
  avoidprimes = support(_reduced_disc(O))
  A = algebra(O)
  R = base_ring(O)
  massformula = 1//length(unit_group_modulo_scalars(O))
  masses = [massformula] # record the contribution of each ideal class to the total mass
  masstotal = mass(O)
  #    vprintf Quaternion:
  #        "Starting with the trivial ideal class. \nMass %o out of total mass %o\n", massformula, masstotal;
  ideals = [1*O]
  pe = 1
  # We first try prime ideals of small norm
  primes = sort!(_prime_ideals_up_to(R, 100), by = norm)
  while massformula != masstotal
    #@info pe, massformula, masstotal
    if length(primes) == 0
      # have not found anything, so we switch over to
      # enumerating prime ideals by minimum
      pe = next_prime(pe)
      primes = _prime_ideals_over(R, pe)
    end
    pp = popfirst!(primes)
    @info norm(pp), massformula, masstotal
      if pp in avoidprimes
        continue
      end
      maxids = maximal_integral_ideals(O, pp; side = :right)
      for II in maxids
        found = false
        for J in ideals
          fl, _ = _isisomorphic_generic(II, J; side = :right)
          if fl
            found = true
            break
          end
        end
        if !found
          push!(ideals, II)
          mass = 1//length(unit_group_modulo_scalars(left_order(II)))
          massformula += mass
          push!(masses, mass)
          if massformula == masstotal
            break
          end
        end
      #end
    end
  end
  return ideals
end

# function right_class_set(O::Union{AlgAssRelOrd{<:Any, <:Any, <:QuaternionAlgebra}})
# #    { Compute the right class set of a quaternion order O in a naive way.
# #      This code is originally by Voight (also appears as commented out code in
# #      ideals-jv.m). Some small modifications have been made.
# #
# #      We use this naive version, because it works for any order.
# #    }
#   avoidprimes = support(_reduced_disc(O))
#   A = algebra(O)
#   R = base_ring(O)
#   massformula = 1//length(unit_group_modulo_scalars(O))
#   masses = [massformula] # record the contribution of each ideal class to the total mass
#   masstotal = mass(O)
#   #    vprintf Quaternion:
#   #        "Starting with the trivial ideal class. \nMass %o out of total mass %o\n", massformula, masstotal;
#   ideals = [1*O]
#   pe = 1
#   while massformula != masstotal
#     pe = next_prime(pe)
#     if pe > 300
#       error("asdS")
#     end
#     for pp in prime_ideals_over(R, pe)
#       if pp in avoidprimes
#         continue
#       end
#       I = maximal_integral_ideal(O, pp, :right)
#       found = false
#       for J in ideals
#         fl, _ = _isisomorphic_generic(I, J; side = :right)
#         if fl
#           found = true
#           break
#         end
#       end
#
#       if !found
#         @info "new, $pe"
#         push!(ideals, I)
#         mass = 1//length(unit_group_modulo_scalars(left_order(I)))
#         massformula += mass
#         push!(masses, mass)
#       end
#     end
#   end
#   return ideals
# end

#                if not found then
#                    vprintf Quaternion: "New ideal of norm %o, now found %o ideal classes\n",
#                                        Norm(Norm(I)), #ideals+1;
#                    Append(~ideals, I);
#                    mass := 1/#UnitGroup(LeftOrder(I));
#                    massformula +:= mass;
#                    Append(~masses, mass);
#                    vprintf Quaternion: "Masstotal now %o out of %o\n", massformula, masstotal;
#                    vprintf Quaternion: "Contributions: %o\n", masses;

#        factpe := Factorization(ideal<R|pe>);
#        // NB Daniel: only use primes where residue field is minimal, in an attempt to speed up the search
#        primes := [ x[1] : x in factpe | not x[1] in AvoidPrimes and Norm(x[1]) eq pe ];
#
#        for pp in primes do
#            M2F, phi := pMatrixRing(O, pp);
#
#            // Magma's choice of generators for a matrix algebra, whatev!
#            e11 := Inverse(phi)(M2F.1);
#            e21 := Inverse(phi)(M2F.2*M2F.1);
#
#            // Ideals mod pp are in 1-1 correspondence with elements
#            // of P^1(F_pp) on the first row (with zeros on the second)
#            k, mk := ResidueClassField(pp);
#
#            // Reduce mod p otherwise 'rideal' will choke  (Steve added this)
#            e11coords, e21coords := Explode(Coordinates( [A!e11,A!e21], ZbasisO ));
#
#            e11 := O! &+[ (e11coords[i] mod pe) * ZbasisO[i] : i in [1..#ZbasisO]];
#            e21 := O! &+[ (e21coords[i] mod pe) * ZbasisO[i] : i in [1..#ZbasisO]];
#            for museq in [[0,1]] cat [[1,x@@mk] : x in [x : x in k]] do
#                mu := O!(museq[1]*e11 + museq[2]*e21);
#                I := rideal<O | [mu] cat Generators(pp)>;
#                I`Norm := pp;
#
#                found := false;
#                for jj := 1 to #ideals do
#                    if IsIsomorphic(I, ideals[jj]) then
#                        found := true;
#                        break jj;
#                    end if;
#                end for;
#                if not found then
#                    vprintf Quaternion: "New ideal of norm %o, now found %o ideal classes\n",
#                                        Norm(Norm(I)), #ideals+1;
#                    Append(~ideals, I);
#                    mass := 1/#UnitGroup(LeftOrder(I));
#                    massformula +:= mass;
#                    Append(~masses, mass);
#                    vprintf Quaternion: "Masstotal now %o out of %o\n", massformula, masstotal;
#                    vprintf Quaternion: "Contributions: %o\n", masses;
#
#                end if;
#            end for;
#        end for;
#        pe := NextPrime(pe);
#    end while;
#
#    O`RightClassSet := ideals;
#    return ideals;
#end intrinsic;
#
#intrinsic TypeNumber(O::AlgAssVOrd) -> RngInt
#    { Compute type number for arbitrary order using RightClassSet }
#
#    C := RightClassSet(O);
#    orders := [ LeftOrder(OO) : OO in C ];
#    noniso := [];
#
#    for OO in orders do
#        already_seen := false;
#        for Ox in noniso do
#            if IsIsomorphic(OO,Ox) then
#                already_seen := true;
#                break;
#            end if;
#        end for;
#
#        if not already_seen then
#            Append(~noniso, OO);
#        end if;
#    end for;
#    return #noniso;
#end intrinsic;
#
#intrinsic StablyFreeMass(O::AlgAssVOrd) -> FldRatElt
#    { Compute mass(Cls^1 O) }
#    return Mass(O) / #StableClassGroup(O);
#end intrinsic;
#
#intrinsic IsHermite(O::AlgAssVOrd) -> Bool
#    { Is the quaternion order O a Hermite ring? }
#    return StablyFreeMass(O) eq 1/#Units(O);
#end intrinsic;
#
#intrinsic HasCancellation(O::AlgAssVOrd) -> Bool
#    { Does the quaternion order O have locally free cancellation? }
#    return #StableClassGroup(O) eq #RightClassSet(O);
#end intrinsic;

#  {Returns the mass of an order O in a definite quaternion algebra
#   over Q, F_q(X) or a totally real number field.}

function _zeta_denominator_bound_at_minus_one(K)
  S = lcm(cyclotomic_quadratic_extensions(K))
  # Sort out all possible m such that [F(zeta_m):F] = 2.
  Sdiv = [m for m in divisors(S) if m != 1 && valuation(m, 2) != 1]
  Sdiv = [m for m in Sdiv if all(degree(f) == 2 for (f, _) in factor(K, cyclotomic_polynomial(m)))]
  lden = lcm(ZZ.(Sdiv))
  return lden
end

function _mass_infinity(K::AbsSimpleNumField)
  if false degree(K) == 1
    return QQ(1//12)
  end
  hK = order(class_group(maximal_order(K))[1])
  z = dedekind_zeta_exact(K, -1)
  #@info "" _zeta_denominator_bound_at_minus_one(K)
  #@info "" _denominator_bound(K, -1)
  return QQ(2)^(1-degree(K)) * abs(z) * hK
end
#    L := LSeries(NumberField(F) : Precision := 6 + extra);
#    z := Real(Evaluate(L, -1));
#    tz10 := Log(Lden*Abs(z))/Log(10);
#    if tz10 ge 4 then
#      LSetPrecision(L, Ceiling(tz10) + 3 + extra );
#      z := Real(Evaluate(L, -1));
#    end if;
#    return 2^(1-Degree(F)) * Abs(Round(Lden*z)/Lden) * ClassNumber(F);
#  end if;
#end function;

function _mass_infinity(::QQField)
  return QQ(1//12)
end

#  {Sequence containing all prime powers m = p^e such that [F(zeta_m):F] <= 2}
function cyclotomic_quadratic_extensions(::QQField)
  return ZZRingElem[4, 3]
end

function cyclotomic_quadratic_extensions(F::AbsSimpleNumField)
  d = degree(F)
  OF = maximal_order(F)
  # phi(p^e) divide 2d (draw a diagram)
  P = [ p for p in PrimesSet(2, 2*d + 1) if is_divisible_by(2*d, p - 1)]
  S = [p^(valuation(2*d, p) + 1) for p in P]
  _is_cyclic_ext_quad = function(n)
    # Test the first few primes to rule out impossible ones
    for q in PrimesSet(1, 100)
      if !(gcd(q, n) == 1 && valuation(norm(discriminant(OF)), q) == 0)
        continue
      end
      facq = prime_decomposition(OF, q)
      for (Q,_) in facq
        absN = absolute_norm(Q) % n
        absN in [-1 % n, 1 % n]
        if !(absN in [1, n - 1])
          return false
        end
      end
    end
    return all(degree(f) == 2 for (f,_) in factor(F, cyclotomic_polynomial(n)))
  end
  #    for q in [q : q in [1..100] | IsPrime(q) and Gcd(q,m) eq 1 and
  #                                  Valuation(Norm(Discriminant(Z_F)),q) eq 0] do
  #      qfacts := Decomposition(Z_F,q);
  #      for qq in qfacts do
  #        if Integers(m) ! AbsoluteNorm(qq[1]) notin [Integers(m) | -1,1] then
  #          return false;
  #        end if;
  #      end for;
  #    end for;
  #    return forall{f : f in Factorization(CyclotomicPolynomial(m), F) | Degree(f[1]) eq 2};
  #  end function;
  for i in 1:length(S)
    m = S[i]
    while m > 1 && !_is_cyclic_ext_quad(m)
      m = divexact(m, P[i])
    end
    S[i] = m
  end
  return [m for m in S if m != 1]
end

_reduced_disc(O::AlgAssAbsOrd{<:QuaternionAlgebra}) = sqrt(abs(discriminant(O)))

_reduced_disc(O::AlgAssRelOrd{<:Any, <:Any, <:QuaternionAlgebra}) = is_power(discriminant(O), 2)[2]

mass(O::AlgAssAbsOrd{<:QuaternionAlgebra}) = _mass(O)

mass(O::AlgAssRelOrd{<:Any, <:Any, <:QuaternionAlgebra}) = _mass(O)

function _mass(O)
  A = algebra(O)
  F = base_ring(A)
  mass = _mass_infinity(F)
  for (p, e) in factor(_reduced_disc(O))
    #q:= T eq FldFunRat select (#BaseRing(F))^Degree(f[1]) else Norm(f[1]);
    q = norm(p)
    #@info p, e
    #@info q^e
    #@info eichler_invariant(O, p)
    #@info q^e * (1-1//q^2)/(1 - eichler_invariant(O, p)*(1//q))
    #@info p, q^e * (1-1//q^2)/(1 - eichler_invariant(O, p)*(1//q))
    mass *= q^e * (1-1//q^2)/(1 - eichler_invariant(O, p)*(1//q))
  end
  return mass
end

function eichler_invariant(O::AlgAssRelOrd, p::AbsSimpleNumFieldOrderIdeal)
  return _eichler_invariant(O, p)
end

function eichler_invariant(O::AlgAssAbsOrd, p::IntegerUnion)
  return _eichler_invariant(O, p)
end

function _eichler_invariant(O, p)
  A, = quo(O, p*O, p)
  J = radical(A)
  @req dim(J) != 0 "The prime must divide the discriminant"
  if dim(J) == 3
    return 0
  end
  B, = quo(A, J)
  # could be done quicker by testing the basis
  if is_simple(B)
    return -1
  else
    return 1
  end
end
