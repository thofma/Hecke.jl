# Algorithm for right class set of a quaternion order.
# See Appendix by Voight in Smit-Marseglia, "Ideal classes of orders in
# quaternion algebras".
#
# The code is inspired by the Magma implementation in
# https://github.com/dansme/hermite by Smertnig-Voight
#
# TODO: redo the calculations

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

# { Compute type number for arbitrary order using RightClassSet }
function type_number(O::Union{AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}}, AlgAssRelOrd})
  C = right_class_set(O)
  orders = [left_order(R) for R in C]
  nonisomorphic = typeof(O)[]
  for R in orders
    seen  = false
    for S in nonisomorphic
      if _is_isomorphic(R, S)
        seen = true
        break
      end
    end

    if !seen
      push!(nonisomorphic, R)
    end
  end
  return length(nonisomorphic)
end

function _is_isomorphic(R::T, S::T) where {T <: Union{AlgAssAbsOrd{QuaternionAlgebra{QQFieldElem}}, AlgAssRelOrd}}
  # Kirschmer, "Konstruktive Idealtheorie in Quatenionalgebren":
  # R, S sind isomorph, wenn die zugehörigen quadratischen R-Gitter isomorph sind bezüglich
  # (x, y) -> tr_D/K(x * conj(y))

  A = algebra(R)
  @assert !is_eichler(A)
  B = basis(A)
  K = base_ring(A)
  M = zero_matrix(K, 4, 4)
  for i in 1:4
    for j in 1:4
      M[i, j] = trred(B[i] * conjugate(B[j]))
    end
  end
  V = quadratic_space(K, M)
  if K isa QQField
    LR = lattice(V, basis_matrix(R))
    LS = lattice(V, basis_matrix(S))
  else
    LR = lattice(V, basis_pmatrix(R))
    LS = lattice(V, basis_pmatrix(S))
  end
  return is_isometric(LR, LS)
end

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

function locally_free_class_group(O::AlgAssRelOrd)
  AA, AAtoA  = restrict_scalars(algebra(O), QQ);
  OO = Hecke.order(AA, preimage.(AAtoA, elem_in_algebra.(absolute_basis(O))))
  return locally_free_class_group(OO)
end

function _stably_free_mass(O)
  return mass(O)//order(locally_free_class_group(O))
end

function _has_stably_free_cancellation(O)
  u = unit_group_modulo_scalars(O)
  return _stably_free_mass(O) == 1//length(u)
end

function _has_locally_free_cancellation(O)
  return order(locally_free_class_group(O)) == length(right_class_set(O))
end

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

@attr QQFieldElem mass(O::AlgAssAbsOrd{<:QuaternionAlgebra}) = _mass(O)

@attr QQFieldElem mass(O::AlgAssRelOrd{<:Any, <:Any, <:QuaternionAlgebra}) = _mass(O)

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

################################################################################
#
#  Classification
#
################################################################################

function _norms_of_ramified_primes(A::QuaternionAlgebra)
  O = maximal_order(A)
  return sort!([p isa ZZRingElem ? abs(p) : absolute_norm(p) for (p, _) in factor(discriminant(O))])
end

function _finger_print(O::Union{AlgAssAbsOrd, AlgAssRelOrd})
  A = algebra(O)
  K = base_ring(A)
  return degree(K), discriminant(maximal_order(K)), collect(coefficients(defining_polynomial(K))), _norms_of_ramified_primes(A), absolute_norm(_reduced_disc(O)), mass(O)
end

const degree_ranges = [1:40, 41:249, 250:309, 310:368, 369:373, 374:375]

# fp created with
# open("fp", "w") do io; for i in 1:length(fp); for x in fp[i]; print(io, ",", Hecke._stringify(x)); end; println(io); end; end;

function _read_fingerprint(;range = 1:375)
  res = Vector{Tuple{Int, ZZRingElem, Vector{Int}, Vector{Int}, Int, QQFieldElem}}(undef, length(range))
  j = 1
  for (i, l) in enumerate(readlines(joinpath(@__DIR__, "SVfingerprint.dat")))
    if !(i in range)
      continue
    end
    io = IOBuffer(l)
    _, deg = _parse(Int, io)
    _, discOK = _parse(ZZRingElem, io)
    _, coeffs = _parse(Vector{Int}, io)
    _, normsram = _parse(Vector{Int}, io)
    _, normdisc = _parse(Int, io)
    b, mas = _parse(QQFieldElem, io)
    res[j] = deg, discOK, coeffs, normsram, normdisc, mas
    j += 1
  end
  return res
end

# true => order not in the database
# false => order maybe in the database
function _order_not_in_db(O::AlgAssRelOrd)
  A = algebra(O)
  K = base_ring(O)
  if degree(K) > 6
    return true
  end
  fps = _read_fingerprint(; range = degree_ranges[degree(K)])
  length(fps) == 0 && return true
  filter!(x -> x[2] == discriminant(maximal_order(K)), fps)
  length(fps) == 0 && return true
  filter!(x -> x[4] == _norms_of_ramified_primes(A), fps)
  length(fps) == 0 && return true
  filter!(x -> x[5] == absolute_norm(_reduced_disc(O)), fps)
  length(fps) == 0 && return true
  filter!(x -> x[6] == mass(O), fps)
  return length(fps) == 0
end

function _order_not_in_db(O::AlgAssAbsOrd)
  A = algebra(O)
  fps = _read_fingerprint(; range = degree_ranges[1])
  filter!(x -> x[4] == _norms_of_ramified_primes(A), fps)
  length(fps) == 0 && return true
  filter!(x -> x[5] == abs(_reduced_disc(O)), fps)
  length(fps) == 0 && return true
  filter!(x -> x[6] == mass(O), fps)
  return length(fps) == 0
end

function has_stably_free_cancellation(O::Union{AlgAssAbsOrd{<:QuaternionAlgebra}, AlgAssRelOrd{<:Any, <:Any, <:QuaternionAlgebra}})
  if _order_not_in_db(O)
    return false
  end
  return _has_stably_free_cancellation(O)
end

function has_locally_free_cancellation(O::Union{AlgAssAbsOrd{<:QuaternionAlgebra}, AlgAssRelOrd{<:Any, <:Any, <:QuaternionAlgebra}})
  if _order_not_in_db(O)
    return false
  end
  return _has_locally_free_cancellation(O)
end
