# Automorphism and isometry of definite lattices: where we are and what is left

The goal is the fastest, most robust and provably correct automorphism group
and isometry implementation available, measured against Magma, against the
Pari/GP code of Chenevier and Taibi, and against Hecke's existing
Plesken-Souvignier path.

## Where we stand, measured

All timings on the shared server, our path against Hecke's tuned invocation
(`__assert_has_automorphisms` with `do_lll = false`) and against Magma.

| lattice                | ours    | Hecke tuned | Magma   |
|------------------------|---------|-------------|---------|
| Leech                  | 0.21 s  | 13.2 s      | 60.9 s  |
| rank 32, det 2^16      | 3.2 s   | (no finish) | 6.29 s  |
| X26_no1 #1899          | 0.081 s | 8.6 s       | 0.05 s  |
| X26_no1 #1885          | 0.187 s | 0.41 s      | 0.15 s  |
| X26_no1 #1891          | 0.044 s | 0.19 s      | 0.05 s  |
| X26_no1 #1901          | 0.50 s  | 0.95 s      | 16.7 s  |

Correctness: 15675 lattices swept across 34/71/81, X25, X26 and the Nebe
files, with no wrong order and one error, discussed below.  Every generator
returned is verified to satisfy `M G M^t = G` before it is used.

## The gaps between here and the goal

1. **Rank above 32 is untested, and out-of-range input is handled badly.**  Of
   everything swept, exactly one lattice has rank above 32.  It has rank 105,
   which is far beyond what anyone expects to be computable -- rank 32 is the
   realistic target and rank 64 would be an achievement -- so the problem is
   not that we fail on it but *how*: an older build raised a `BoundsError` and
   the current one runs for more than seven minutes without answering or
   handing back.  Preprocessing is the suspect, since the minimal-bound basis
   search runs Smith forms on matrices of that size.
2. **Not shippable.**  The include in `src/QuadForm.jl` is commented out, the
   work sits on a branch of 34 commits, and nothing routes Hecke's public
   entry points through it.
3. **Correctness is verified but not certified.**  Each generator is checked,
   so no returned isometry is wrong.  The *order* rests on the search being
   exhaustive, which rests on every pruning criterion being a necessary
   condition.  That argument is not written down in one place.
4. **Lopsided lattices are handled by retreat.**  There are 72 places where we
   hand back to Plesken-Souvignier.  A lattice with no basis of short vectors
   at any affordable bound is still not ours to compute.
5. **Isometry lags automorphism.**  It is validated on 168 pairs but has had
   none of the tuning.
6. **Symmetric sublattices are enumerated and then discarded.**  When the
   sublattice built so far has a large automorphism group, its embeddings are
   many and almost all die later.  Ordering routes around this; it does not
   fix it.

## Plan

### Phase 1 -- decline gracefully, and find the real ceiling (blocking, small)

Rank 105 is not a target.  What is wrong is the manner of failure, so put an
explicit rank and cost guard on every preprocessing step that runs
super-quadratic linear algebra: an input beyond the feasible range must be
handed back in bounded time, never ground on and never by exception.

Then find where the real ceiling is, which is not known.  Rank 32 is the
realistic target and is where the benchmark lives; rank 64 would be an
achievement.  Sweep the Nebe files between those two ranks deliberately --
the current sweep reached anything above 32 only by accident -- and record
where the enumeration, the fingerprint or the search stops being affordable.

Done when: no input raises an exception, every input answers or hands back
inside a predictable time, and we know which rank between 32 and 64 is the
practical limit and which part of the algorithm sets it.

### Phase 2 -- ship it (blocking, small)

Restore the include, route `automorphism_group` and `is_isometric` through the
backtrack with the existing hand-back as the fallback, and get Hecke's own
test suite green.  Until this is done none of the speed is available to
anyone.

Done when: the branch merges and the suite passes.

### Phase 3 -- certify the count (medium)

Write down, in one comment block, every pruning criterion the search uses and
why each is a necessary condition, so that exhaustiveness can be checked by
reading.  Four criteria built during this work are measured and disabled --
class sums, ordered partition refinement, the summand test, the look ahead --
and the note should say they are not part of the argument.  Add a slow mode
that recomputes the order by an independent route on small input, and run it
across the sweep.

Done when: the completeness argument is legible and independently checked on
thousands of lattices.

### Phase 4 -- symmetric sublattices (the real structural gap)

When the root system has many similar components, the search enumerates the
embeddings of `A_1^k` or `A_2^k` and prunes them afterwards.  The glue code --
which subsets of components have half sums in the lattice -- is a binary code
on few points whose automorphism group gives the orbits of the components
directly.  Computing it replaces a search over `k!` with a computation on `k`
points.

This is the one idea aimed at the cost itself rather than at routing around
it, and it is the natural continuation of the root system work already in
place: `rho`, the types, the per-component glue invariants and the spanning
shortcut are all built.

Risk: the payoff is unproven.  Four pruning ideas have already been built,
measured and disabled.  The difference here is that this one removes work
rather than trying to detect it as useless, so measure the orbit computation
against the search it replaces before wiring it in.

### Phase 5 -- lopsided lattices (medium, well specified)

Section 4 of the write-up: enumerate only the vectors that could be an image,
recursively over an orthogonal decomposition, with the fibre matching of
Remark 4.1(iii) which is what makes it cheaper than plain enumeration rather
than more expensive.  Section 3.1 -- the semidefinite reduction using a
generating set where no basis of short vectors exists -- covers the remainder.

Needs a target first: no lattice in the benchmark has yet been shown to defeat
the minimal-bound basis search.  Construct one (the `E_8 + [m]` family of
Example 2.4 is the natural candidate) before building against a hypothesis.

### Phase 6 -- isometry and canonization

Bring isometry to the same tuning as automorphism; both share the machinery,
so this is mostly measurement.  Then Section 6: a complete invariant via the
Weyl-marked graph, which is a separate deliverable the write-up wants and
which reuses everything in phases 4 and 5.

## Standing lessons

The ordering of the basis vectors decides more than any pruning test tried
against it, and no cheap estimate of the right objective has beaten a fitted
rule.  Any new pruning idea should first be checked against the partial Gram
matrix: if the quantity it tests is a function of that, it agrees on every
branch the search considers and will prune nothing.
