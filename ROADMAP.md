# Roadmap

What of CORA is formalized, what is being worked on, and what is left. Kept
current as work lands; each open item names what it depends on, so the ones with
no dependencies are the ones that can start.

## In flight

| Branch | Work |
| --- | --- |
| `feat/relinearize` | Nonlinear reachability beyond one step: a fresh expansion point and a fresh certificate at each |
| `feat/examples` | Use sites, so a broken instance fails the build — a library cannot notice one from the inside |

Next after those: the conversions the newest representations do not yet have,
`restructure`, and the float layers.

## Done

**Global.** Array types, the scalar a layer computes in, entrywise coordinates,
index partitions, block structure, corner combinatorics, sorting. Linear
programming: `SupportBound`, weak duality, composition across the set
operations, and the float counterpart.

**Representations.** `Interval`, `Zonotope`, `HPolytope`, `VPolytope`,
`ConZonotope`, each in both arithmetic layers, with all twenty ordered
conversions in each layer. `InflatedContSet` is what the float layer adds.

`Ellipsoid`, `Real` layer: stored as the affine image of a Euclidean ball rather
than by a shape matrix, so no inverse, no positive-semi-definiteness condition
and no matrix square root. Its support function is closed form and attained,
which makes it the only representation that answers a direction without a linear
program, and its bounding box tight.

`PolyZonotope`, `Real` layer, with `quadMap` exact — the operation the
representation exists for, and the one that needs its factors to be shared.
`compact` merges equal exponent columns, drops the generators that leaves at
zero and drops the factors nothing uses — all exact, and all of it needed before
an order bound counts anything real, since `plus` and `quadMap` grow the
generator count while the set stands still. `reduce` then ranks by Girard's
metric and boxes what it drops into the independent block. Its merging core is
stated over exponent data alone, so a constrained polynomial zonotope reuses it
unchanged at its generators *and* at its constraint columns.

With `Reduce` instantiated, linear reachability runs on `PolyZonotope` — the
first non-convex representation it does.

`ConPolyZono`, `Real` layer: the same factors additionally constrained by
polynomial equalities `A μ(α) = b`, the constraint monomials read off one
exponent matrix over the same factors as the generators. `and` is exact with no
hypotheses, and is the only place in this repository where two non-convex sets
intersect without loss — the agreement rows are constraints of the kind already
carried, so their coefficients can be monomials, which a constrained zonotope's
linear rows cannot express. `plus`, `map`, `mtimes`, `quadMap` and `dependent`
are exact as well; nothing in its `Theorems/` is `_outer`.

**Dynamics.** `LinearSysDT` with reachability. `LinearSys`: the flow in closed
form, the matrix exponential enclosure, discretization, the input solution, the
time-interval enclosure, and reachability at the sample times — stated once
against `ConvexSet` and `CompactSet` rather than once per representation.

A trajectory carries the time domain it runs on, so each guarantee asks for the
window it actually speaks about and a bounded horizon is sayable at all. The
subtlety is one-sided derivatives: `HasDerivWithinAt` at `t` within `Ici t` does
not follow from a bounded domain by monotonicity, only where the domain still
extends to the right of `t` — so the identity pinning the input runs out at the
right endpoint, and the measurability arguments moved to the open window, the
missing point being null. `discretize` and sample-time reachability still ask
for all forward time, not through the flow but through the target:
`LinearSysDT.Trajectory` is total in the step count. `reach_outer_horizon`
unrolls the recursion itself to avoid that.

`NonlinearSys`, genuinely one step by conservative linearization. The abstraction error is
a certificate rather than a derivative: a set together with the proof that it
encloses what is left of the field once the affine part is subtracted. Nothing
downstream mentions a derivative, so `A` and `B` need not be the Jacobians and a
linearization computed in float arithmetic is covered without a word about how
far it is from the true one. A confined run is then a linear run over a widened
input, and reachability is the linear theorem unchanged. Confinement is asked
for on the run's own domain, so confinement over `[0, τ]` buys a linear run over
`[0, τ]` and nothing is assumed about what happens afterwards — which is what
re-linearizing from the enclosure reached at `τ` will consume.

**Verification.** `Specification` — a safe set or an unsafe one — and the
theorem that a check passed on an outer approximation is passed by the exact
set. Separating directions and halfspace bounds discharge it.

**Neural networks.** The layer interface, the graph, propagation and its
enclosure, and the standard layers: linear, ReLU, sigmoid, tanh. Robust
classification as a specification.

**Hybrid systems.** Locations, transitions and the automaton. A run is an
inductive chain of stays joined by jumps, so chaining is the family's own
recursion and the safety statement is `Specification.holds_of_outer` in a line.
Each stay runs on a local clock, which is what lets every `LinearSys` statement
apply unchanged; global time is the sum of dwell times and never appears. The
alternative — a predicate over global time — was rejected because it would have
had to assert the jump times are discrete and increasing, putting a Zeno
condition inside the definition of a run. Guard intersection is a hypothesis
carrying its own proof rather than a class, and `ConZonotope` discharges it with
an equality.

## Open

Ordered roughly by what unblocks the most.

### Representations

- **`PolyZonotope.restructure`** — the other half of order control, moving
  independent generators back to dependent.
- **The independent block under an order bound.** `reduce` bounds the dependent
  count, and the box it drops adds `n` independent generators per call, so a
  reachability loop still grows one of the two counts without limit. Bounding it
  is `Zonotope.reduce`'s shape over a second partition.
- **Compaction for `ConPolyZono`.** The merging half carries over unchanged;
  dropping factors does not, since `p` is shared between the generator and
  constraint exponent matrices and only a factor unused by both may go.
- **`ConPolyZono`: `linComb`, `reduce`, `CompactSet`** — the first would have to
  relax the independent block, the second needs compaction in the constraint
  matrix as well as the generators, and the third is true but unproved: the sets
  are compact and the argument is simply not written.
- **An `And` class.** `ConPolyZono.and` is exact and is what a guard or an
  invariant asks for, but the only other implementor is `ConZonotope`, which
  could state it at convex sets only. The class stays unwritten until something
  needs an intersection generically — the same question `Ellipsoid.plus` raises
  from the other side.
- **`Capsule`**, **`ZonoBundle`**, **`SpectraShadow`**, **`Taylm`** — CORA has
  them; none blocks anything else.
- **Conversions** for the late arrivals. `Ellipsoid` has four of its ten pairs,
  `PolyZonotope` five, `ConPolyZono` two; the gaps differ in kind, an ellipsoid's
  polytope pairs being merely absent while a polynomial zonotope's are
  enclosures with a precision knob rather than conversions, its sets not being
  convex. `ConZonotope → ConPolyZono` is blocked by a choice of ours rather than
  by mathematics: our `ConZonotope` carries an `HPolytope`, so it admits
  inequalities, while a `ConPolyZono` admits equalities only — the conversion
  would need a slack factor per inequality together with a bound on it. CORA's
  `conZonotope` carries equalities and maps straight across.
- **`Ellipsoid.plus` as an interface.** It is implemented and proved, but
  `Plus` is not instantiated: the class field has no room for the free parameter
  `l`, and fixing a value would bury a precision choice in an interface. Whether
  the operation classes should carry a knob is a real design question and this
  is the first representation to raise it.
- **`Reduce` methods** — CORA has `girard`, `pca`, `combastel`, `methC`, and the
  order-reduction choice is a precision knob throughout reachability. Only one
  is formalized.
- **Float layers** for every representation added above.

### Dynamics

- **A bounded `LinearSysDT.Trajectory`** — the discrete run is total in the step
  count, which is why sample-time reachability cannot take a bounded domain
  directly and `reach_outer_horizon` unrolls the recursion by hand instead.
- **`TimeIntervalOuterSplitZonotope`** — the one reachability statement still
  tied to a representation. Dropping `0 ∈ U` takes the input set apart into a
  centre, a remainder, a point and a segment, and no interface offers those.
  Either a class earns them or it stays where it is.
- **Nonlinear reachability, beyond one step** — the polynomialization variant
  that uses `PolyZonotope`, and the loop that re-linearizes. The loop is now
  unblocked — a step is sound on its own interval and says nothing beyond it —
  and what it still needs is the confinement check below.
- **Discharging confinement** — the linearization step assumes the run stays
  where its certificate holds. CORA computes a candidate, checks the step's
  reachable set against it and enlarges on failure; nothing here does.
- **`NonlinearSysDT`**, **`LinParamSys`**, **`NonlinParamSys`**,
  **`NonlinDASys`** — the remaining system classes.
- **Adaptive reachability** — Wetzlinger et al., parameter tuning with a
  guaranteed error bound. Depends on the error measures being formalized first.
- **Inner approximations** — `reachInner`, which needs the `_inner` direction
  that no operation currently proves.
- **Simulation** — trajectories are defined; sampling one is not.

### Hybrid systems

- **A bounded-horizon invariant.** What chains today is an *inductive* invariant:
  a set per location closed under flowing and under jumping. Once jumps are in
  play there is no step index, so a location visited twice is answered by the
  same set both times. The bounded reading — a set per step as well as per
  location — is the same induction with an extra argument.
- **Computing an invariant.** `Invariant` states what a fixpoint iteration would
  have to produce; the iteration itself is not written.
- **`ConPolyZono` at a jump.** The reset is `mtimes` and `plus` with the offset
  as a zero-width box, so it asks for `OfInterval`, which `ConPolyZono` does not
  instantiate. Its exact non-convex intersection is therefore one conversion
  instance away from the guard, not one theorem.
- **`ParallelHybridAutomaton`** — composition. Waits on the single automaton.

### Neural networks

- **The float layer** — needs the two box classes at `Interval 𝕋 n`.
- **More layers** — softmax, batch normalization, convolution, pooling,
  reshape, and the composite layers CORA builds from them.
- **`NeurNetContrSys`** — a network in the loop of a continuous system, which is
  where the two halves of this repository meet.
- **A curvature relaxation for sigmoid and tanh** — both carry slope zero,
  which is all monotonicity certifies: the range of `σt - λt` only widens as `λ`
  leaves zero. A useful slope needs second-order information, and the
  `Relaxation` field is already where it would go.
- **Verification beyond propagation** — refinement by splitting the input set,
  which is what makes the method complete in practice.

### Infrastructure

- **A worked example per component.** In flight. `Examples/FeedForward.lean` was
  the only use site, and one is not enough: the fact that linear reachability now
  runs on `PolyZonotope` was discovered by trying it, not by reading the
  instances.
- **Specializations as regression tests.** Reachability is now stated once over
  `ConvexSet` and `CompactSet`, and the old per-representation statements were
  checked to follow with `:=` and then discarded. They belong in `Examples/`,
  where they would fail the build if the generalization ever stopped covering
  them.
- **Benchmarks** — the ARCH competition instances CORA reports on.

## Conventions

`CONTRIBUTING.md` states them and `scripts/check-conventions.sh` checks them.
Work that lands here passes both that script and a warning-free `lake build`.
