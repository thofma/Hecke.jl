# Lessons from the partition-backtrack experiment

This file records what was learned building an experimental automorphism and
isometry implementation for definite lattices
(`src/QuadForm/IsometryBacktrack.jl`). The code itself is not intended to ship
with Hecke -- it is AI generated, around five thousand lines, and Hecke ships
only human-verified code. The findings below are meant to outlive it, and the
last section lists the ones small enough to be worth porting to Hecke's own
call path as reviewable diffs.

Everything here was measured, on the shared server, with both paths warmed
before timing. Where a claim rests on a single lattice it says so.

## 1. What the experiment reached

| lattice                 | experiment | Hecke tuned | Magma   |
|-------------------------|-----------|-------------|---------|
| Leech                   | 0.21 s    | 13.2 s      | 60.9 s  |
| rank 32, det 2^16       | 3.2 s     | no finish   | 6.29 s  |
| X26_no1 #1899           | 0.081 s   | 8.6 s       | 0.05 s  |
| X26_no1 #1885           | 0.187 s   | 0.41 s      | 0.15 s  |
| X26_no1 #1891           | 0.044 s   | 0.19 s      | 0.05 s  |
| X26_no1 #1901           | 0.50 s    | 0.95 s      | 16.7 s  |

"Hecke tuned" is `__assert_has_automorphisms` with `use_everything`,
`search_invariant_subspace` and, importantly, `do_lll = false`.

## 2. The ordering of the basis vectors dominates everything

This was the single largest effect found, and it took the longest to see.

The nodes of the search at level `j` are the isometric embeddings into `L` of
the sublattice `N_j` spanned by the first `j` basis vectors. Their number
factors as

    #embeddings = (#sublattices of L isometric to N_j) x |O(N_j)|

so the search pays directly for the *symmetry of the sublattice it has built
so far*. The total work is the sum over `j`, and the last term is essentially
the order of the group and independent of the ordering, so what an ordering
decides is how high the count climbs on the way there.

The classical greedy rule -- take the level with the fewest candidates next --
is myopic in a way that matters. On a lattice whose root system is `A_1^10`,
the ten roots each look cheap (ten candidates, then nine, then eight) so the
greedy rule takes all of them first, building `N_10 = A_1^10` with
`|O| = 2^10 10! = 3.7e9`. Every one of those embeddings is enumerated and
almost all are then discarded, because the glue -- which is what actually rules
them out -- is not consulted until the later levels.

Taking the *largest norm* first reverses this and was worth a factor of 45 on
one lattice (1.43 s to 0.032 s). But it is not uniformly better: on another
lattice of the same family it cost a factor of nine, because there the greedy
rule opens with levels that have a single candidate and largest-norm opens
with 22356.

Measured over three independent samples of the benchmark (1194, 626 and 785
lattices), timing every ordering, against an oracle that always picks the best:

|                                       | total          | worst on one lattice |
|---------------------------------------|----------------|----------------------|
| greedy, fewest candidates first        | 1.42 / 1.87 / 1.46x | 306 / 342 / 331x |
| largest norm first                     | 1.90 / 1.71 / 1.85x | 34 / 19 / 13x    |
| defer to largest norm unless the score  | 1.16 / 1.21 / 1.12x | 25 / 19 / 6.5x   |
| of the counts disagrees by a margin     |                |                      |

The spread between best and worst ordering has median 3.2 and worst case 504.

**No cheap estimate of the right objective beat a fitted rule.** A Gaussian
lattice-point estimate of `max_j N_j` from the leading principal minors -- the
mathematically correct shape -- did *worse* than the crude product of candidate
counts, because it knows nothing of the colours or of the Weyl vector, which
are what really cut the candidates down. A one-step lookahead, scoring each
candidate by its own count together with the counts its choice leaves behind,
cost 7.6 times the oracle. Charging for the symmetry linearly, where
`|O(A_1^m)|` grows as `2^m m!`, changed no ordering at all.

## 3. A pruning test implied by the partial Gram matrix cannot prune

The candidates offered at each level have already been filtered so that every
scalar product matches. The partial Gram matrix of the images therefore agrees
with that of the sources *on every branch the search ever considers*. Any
quantity that is a function of that matrix agrees too, and prunes nothing.

This retro-predicts three failures, each of which was built and measured before
the principle was understood:

* **Ordered partition refinement** (Leon's method, which the Magma
  implementation is described as using). Correct, and it rejects nothing: the
  node counts on the target lattice were unchanged to the last node, while the
  search went from 1.44 to 5.26 seconds.
* **Bacher polynomials**, tested through Hecke's own `bacher_depth`: 11.36 s at
  depth 0, 11.63 at depth 1, 12.05 at depth 2. Slightly worse at every depth.
* **The direct summand test**: the images must span a direct summand, since the
  sources are standard basis vectors whose matrix has all elementary divisors
  one. It rejected none of 3072 branches and cost 35 percent. The partial Gram
  already fixes the determinant of the sublattice and with it most of the
  elementary divisor information.

A fourth, **class sum refinement**, failed differently: it is genuinely ambient
but split nothing (47 classes before and after) on the lattices where more
discrimination was wanted, because those lattices' classes were already as fine
as invariants of that kind can make them.

A fifth, an **ambient look ahead** counting the vectors that could still be the
image of a later basis vector, is not Gram-implied and still failed, for a
third reason: given the images fixed at the branching levels, every later level
admitted exactly one candidate on good and bad branches alike. The branches
that die do so from constraints accumulated several levels further down, which
do not exist yet.

**The rule to apply before building any pruning idea**: ask whether the
quantity tested is a function of the partial Gram matrix, and whether the
information it needs exists at the level where the test would run.

## 4. LLL optimises the wrong target for this problem

Everything downstream is priced by the largest diagonal entry of the Gram
matrix, because that is the bound the short vectors are enumerated to and their
number prices every node of the search. LLL optimises the orthogonality defect
instead, and on a basis chosen by hand it can push the largest diagonal *up*.

On the lattices of Chenevier and Taibi, whose bases are hand-chosen, LLL raises
the largest diagonal from 4 to 5 -- the difference between 71956 short vectors
and 623892. Magma's LLL does the same; Magma's Seysen reduction does not.

Two consequences, both measured:

* Keep the reduced basis only when it does not raise the largest diagonal
  entry. One lattice went from 82 seconds to 0.93.
* Look for a basis of short vectors at a *lower* bound than either LLL or a
  greedy pass finds. Both stop at 4 on those lattices while a basis of vectors
  of norm 3 exists -- 586 vectors instead of 71956. One lattice went from 66
  seconds to 1.44, another from 0.93 to 0.17.

The second needs care: a set of vectors generating the lattice need not contain
a basis (2 and 3 generate the integers and neither is a basis), so a candidate
set must be extended only while it stays a direct summand, all elementary
divisors one.

An earlier attempt at the same choice used a predicted enumeration *tree size*
as the criterion and made things slower. The tree was never what was being paid
for; the vector count is.

## 5. Roots are far cheaper to find than they look

The norms of the roots divide twice the exponent of the discriminant group, so
for a unimodular lattice they are at most 2. The root system of a rank 26
unimodular lattice therefore comes from an enumeration to norm 2 in under a
hundredth of a second, with no need for the full short vector set. That removes
the apparent chicken-and-egg between needing the Weyl vector to prune the
enumeration and needing the enumeration to find the roots.

When the roots span the whole space the group follows from them with no short
vectors at all: the simple roots are a basis of a finite index sublattice, and
what is left after the Weyl group is exactly the permutations of the simple
roots that respect the Cartan matrix and preserve the lattice. On one rank 26
lattice with root system `A1 + A2 + A23` this replaced 11.5 seconds, almost all
of it enumerating 8299362 unnecessary vectors, with 0.34 seconds.

Two traps found by testing:

* The number of root *lengths* must be checked before the classification, or
  `B6` and `C6` are read as `E6` -- all three have 72 roots in rank 6.
* Only primitive roots may be kept, or a non-reduced system (norms 2, 4 and 8,
  where `r` and `2r` are both roots) defeats the classification.

## 6. Signs, when the vectors are stored one per pair

Short vectors are usually stored one representative per `{v, -v}` pair. An
isometry then permutes them only *up to sign*, and any invariant built from a
signed scalar product with a stored representative is not invariant: the
pairing flips with the choice of representative. Keying a partition by the
signed pairing reported a group of order 2048 for a group of order 95126814720.

The Weyl vector rescues this, because an isometry fixing `rho` preserves
`<v, rho>`, so `rho` pins the representative and the signed pairing becomes
invariant after all. Without roots, the absolute value must be used, which is
weaker.

## 6a. Lopsided lattices, and where each approach is defeated

The family `E_8 + [m]` of Example 2.4 in the write-up is the sharpest test, and
the two approaches fail on opposite inputs.

Hecke's targeted enumeration works along the flag of successive sublattices:
with `L_i` the projections of `L`, it builds vectors through
`M_1 < M_2 < ... < M_n = L`, each step going via `M_i + L_{i+1}` and testing
for integrality.  Because it works with *projections of L* rather than
sublattices of it, the integrality test is exactly what enforces the glue, so a
primitive extension of small index does not defeat it.  That matters: a
decomposition-based shortcut would be defeated by exactly that.

On `E_8 + [m]` the successive sublattices are `[8, 1]`, and the image of the
long basis vector then costs a rank one enumeration at norm `m` -- two vectors
-- instead of the shell of norm `m` in rank nine, which for `m = 30` holds
1860841 vectors.  Hecke does every member of the family in a millisecond.  The
backtrack, enumerating globally, took 16.6 seconds at `m = 30`.

The reverse holds on well-rounded lattices.  On lattice 1899 of X26_no1 the
successive sublattices are `[10, 16]`, so the decomposition is there, but the
bound is already 3 and there are only 586 short vectors: nothing is left for a
targeted enumeration to save, and the whole cost is the search.  There Hecke
takes 8.6 seconds and the backtrack 0.081.

So: **targeted enumeration wins when the bound is far above the minimum, and
search ordering wins when it is not.**  Neither subsumes the other, and an
implementation that wanted both would have to choose between them per lattice
-- cheaply, since the successive sublattice ranks and the diagonal of the Gram
matrix already say which regime a lattice is in.

## 6b. Preprocessing has to be ordered by cost, not by pipeline

Three separate factors of hundreds were lost to preprocessing that ran before
something cheaper would have answered, or that ran at all when it could not
help.

* The shortcut that reads the group off a spanning root system needs only an
  enumeration to twice the exponent of the discriminant group.  It was running
  *after* the search for a basis at a lower bound, which is expensive and
  pointless whenever the shortcut is going to answer.  On a Niemeier lattice
  with root system `D_12^2` the basis search took four seconds and the shortcut
  then took 0.013.  Reversed, the whole computation takes 0.007 seconds.
* That basis search looped over every integer between the smallest and the
  largest diagonal entry.  With a basis vector of norm 1000 that is nine
  hundred and ninety eight enumerations; only the distinct diagonal entries can
  be the bound of a basis of short vectors.  `E_8 + [1000]` went from 4.3
  seconds to 0.002.
* The greedy short basis had no cost guard at all, so at rank 64 it did not
  return.  A lattice out of range has to be declined in bounded time.

The general lesson is dull but expensive: every preprocessing step needs a
guard proportional to what it is trying to save, and the cheap decisive test
goes first.

## 7. Methodology

* **Warm every path before timing it, not just the new one.** Two conclusions
  in this work were exactly inverted by a cold first call: once reporting 30.4
  seconds for a path that takes 3 milliseconds, once making a baseline look
  like 40 to 114 seconds when it takes 0.18.
* **Compare against the tuned invocation, not the defaults**, and give both
  sides the same untouched lattice. Reducing the input first measures basis
  quality rather than the algorithm.
* **Measure before building.** Four pruning criteria were built, made correct,
  and then found to prune nothing. In each case a few minutes of instrumenting
  where the nodes actually go would have said so first. The instrumentation
  that finally explained the cost was a count of nodes per level, which took
  twenty lines.
* A shared machine's load makes single timings unreliable by a factor of
  several; ratios measured in the same process are trustworthy, wall clock
  across runs is not.

## 8. What might be worth porting to Hecke's own path

In rough order of value per line of diff:

1. **Choose between the given basis and the LLL-reduced one by the largest
   diagonal entry.** A few lines in the reduction step. This is the change that
   was worth 8.7x in short vector count on the Chenevier-Taibi lattices, and it
   is why Hecke's tuned invocation already passes `do_lll = false` there by
   hand -- this would make that choice automatic and correct in general.
2. **The level ordering rule.** Hecke's fingerprint orders levels by fewest
   candidates. Adding the largest-norm ordering and the margin rule of section
   2 is a contained change to that one function, and the measurements above say
   it is worth between 1.2x and 1.4x on average with a much better worst case.
3. **Search for a basis of short vectors at a lower bound.** Larger, but it is
   self-contained preprocessing and does not touch the search.
4. **The spanning-roots shortcut.** Self-contained, and it turns some rank 26
   computations into milliseconds. It needs the root classification traps of
   section 5 handled.
5. **Do not spend effort on Bacher polynomials for this family**: measured as
   no help at any depth on the lattices where help was wanted.
6. **The regime test.** Hecke's targeted enumeration is the right machinery
   when the largest diagonal entry is far above the minimum, and is wasted
   effort when it is not; the ranks of the successive sublattices and the
   diagonal say which is the case before any work is done.  Section 6a has the
   measurements on both sides.

## 9. Two defects on the road less travelled

Both were reachable only when a basis vector is longer than the enumeration
bound, so that its level is served from a coset rather than from the enumerated
vectors.  That path existed for a long time and was almost never taken; the
moment the bound was allowed to be small it was taken constantly, and both
defects appeared at once.

**The order was wrong.**  The search computes `Aut(L, rho)` and the answer is
that times the order of the Weyl group, so an image that does not fix `rho`
must not be counted.  That condition was applied at the levels served from
enumerated vectors and was absent at the coset levels.  On `E_8 + [4]` with the
bound at 2 it counted the reflection in the norm 4 root twice -- once inside
the Weyl group where it belongs, once again as a coset extension -- and
returned exactly twice the true order.  Every generator returned was a genuine
isometry; only the arithmetic was wrong, which is why the certificate on the
generators did not catch it.

The reason the condition could not be applied is worth recording on its own:
the table it needed was read out of an array indexed by the *enumerated
vectors*, so it held zero for exactly the levels that had no enumerated vector
-- the ones that needed it.  Reading the pairing from `G * rho` instead makes
it defined for every level, and is simpler.

**A segmentation fault.**  The array counting scalar products during the
fingerprint refinement was sized by the enumeration bound, but it is indexed by
`<v, b>` with `b` a basis vector, which Cauchy-Schwarz bounds by the square
root of the product of the two norms, and also by pairings of two basis
vectors, bounded by their own norms.  Both exceed the enumeration bound as soon
as a basis vector does.  Inside an `@inbounds` block that is a write past the
end of the array.

The pattern behind both, and behind the `BoundsError` at rank 105 earlier: an
array sized by the enumeration bound, indexed by a quantity that is *not*
bounded by it.  Worth grepping for whenever a bound becomes smaller than it
used to be.

## 10. What the fixes were worth

  E_8 + [m]      before     after     Hecke
  m = 30        16.624 s    0.002 s   0.001 s
  m = 1000       4.258 s    0.002 s   0.001 s

  Niemeier D12^2  4.108 s    0.007 s   0.006 s
  Niemeier D6^4   4.114 s    0.007 s   0.005 s

The lopsided family came down by a factor of eight thousand and the Niemeier
lattices by nearly six hundred, and in both cases the whole cost had been
preprocessing that ran before something cheaper would have answered, or a bound
chosen larger than it needed to be.
