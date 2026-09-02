# Roadmap

What of CORA is formalized, what is being worked on, and what is left. Kept
current as work lands; each open item names what it depends on, so the ones with
no dependencies are the ones that can start.

## In flight

| Branch | Work |
| --- | --- |
| `feat/float-ellipsoid` | The last representation without a float layer, and a support function that wants a square root |
| `feat/nn-more-layers` | The layers CORA has beyond the four here — reshape, pooling, convolution, batch norm, softmax |

Next after those: the float layers that remain, the conversions the newest
representations do not yet have, more layers, and `restructure`.

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
Both carry a float layer. The monomial costs it nothing, which is the surprise:
a product of many rounded powers would accumulate error with the total degree,
but no monomial is ever computed — the coefficients are what the set quantifies
over, and what is stored of a monomial is its exponent column over ℕ, where
every operation is exact. So a monomial enters only through lying in `[-1,1]`,
exactly as a zonotope's free coefficient does, and a rounded generator costs one
radius of the error whatever the degree. The cost is in the number of generators
summed rather than the size of each, which is why `compact` is worth running
before `quadMap` rather than after.

`quadMap` is where directed rounding stops composing: an inner product comes
back as an interval, and multiplying by a generator cannot round in one
direction without knowing its sign, so the bounds travel as a pair and are
chosen per term. A quadratic map is also not additive, so the error box cannot
ride alongside and has to be emptied into generators first.

`ConPolyZono`'s constraints stop at something real — an equality has no
direction to round in. Perturb the right-hand side and the admissible factors
are a disjoint slice of the same cube rather than a superset, so neither
inclusion holds. `plus` and `mtimes` refine because they touch the constraint
system only by copying; `and` cannot be refined at all.

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
input, and reachability is the linear theorem unchanged, and the loop that
re-linearizes chains those steps: a fresh expansion point, matrices and
certificate at each, bundled as a `LinStep` so a certificate travels with the
data it certifies. A chain is a function of the step index rather than a list or
an inductive family — the enclosures have to be *data* a caller hands to
`Specification`, and a set that exists only once a proof has been built is not
one. The run is re-anchored at each step rather than the windows made absolute,
which costs two proved shift lemmas and keeps every existing statement usable. Confinement is asked
for on the run's own domain, so confinement over `[0, τ]` buys a linear run over
`[0, τ]` and nothing is assumed about what happens afterwards — which is what
re-linearizing from the enclosure reached at `τ` will consume.

**Verification.** `Specification` — a safe set or an unsafe one — and the
theorem that a check passed on an outer approximation is passed by the exact
set. Separating directions and halfspace bounds discharge it.

**Neural networks.** The layer interface, the graph, propagation and its
enclosure, and the standard layers: linear, ReLU, sigmoid, tanh. Robust
classification as a specification.

In float: the relaxation, the activation layer, linear and ReLU. The relaxation
absorbs the rounding by itself — `sound` states an inequality against `error`,
so nothing constrains the slope or the offset, and the float structure is the
exact one with the scalar swapped. Only the layer constructors needed
duplicating: `Layer` is a structure over any `ContSet` at a real vector, which a
float representation is through `InflatedContSet`, so the network, propagation
and the robustness bounds run at a float zonotope unchanged.

All four activations are there in float, sigmoid and tanh included. The
exponential that unblocked them evaluates no series: argument reduction removes
the division a truncated series would need, `half` being exact, and the two
seeds are one lemma used twice. There is no tail to bound because there is
nothing truncated.

The asymmetry it leaves is worth keeping in mind. `expDown` is total; `expUp`
asks that its argument be bounded, and that cannot be discharged inside the
class — every expression `FloatOps` builds is a composition of addition,
multiplication, min, max and halving, hence polynomially bounded, and no
polynomial dominates the exponential. A total upper bound would have to branch
on argument size, and `le` is deliberately unconstrained. The sigmoid and tanh
enclosures ask for the lower bound alone and are total.

ReLU's secant is a division, which the scalar now has; before it did not, and it
did not need one, since a slope is a precision knob rather than a correctness
condition and any candidate becomes legal by clamping into `[0,1]` with the
exact `minimum` and `maximum`. Only the gap rounds.

**Closed loops.** `NeurNetContrSysDT`, a network controlling a discrete plant,
and `NeurNetContrSys`, the sampled continuous one: the controller has its own
sampling time and the input is held across it, so `reach` recurses on the
control period and each period is several reachability steps under one held
input. The two rates are separate throughout.

The finding that shaped it is worth keeping: a zero-order-hold run is *not* a
`LinearSys.Trajectory` over all forward time. At a sampling instant the input
jumps, so the state has a left and a right derivative and is not differentiable
there — asking for a two-sided derivative would silently force the two inputs
equal and forbid the controller from ever switching. The flow is therefore
stated per period, within that closed period, where the endpoints are exactly
where it becomes one-sided.

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
- **Float `compact`, and float `linComb` for `PolyZonotope`.** The decidability
  obstacle inverts at a machine scalar — deciding a generator is zero and
  ordering columns both become decidable, which is why float `reduce` is
  computable where the real one is not — but arithmetic takes its place, merging
  two columns adding their entries. So a float `compact` owes an error box where
  the exact one is an equality, and the float order bounds *stored* columns
  rather than distinct monomials.
- **`ConPolyZono.and` in float** — blocked on the `Real` layer admitting either a
  slack factor with a bound or an interval right-hand side, since an equality
  constraint has no direction to round in. This is the largest gap in the repository, and it is a gap in kind
  rather than in coverage: a `Real` definition specifies something no machine
  runs. New work is expected to carry both layers — see `CONTRIBUTING.md`.

### Dynamics

- **A bounded `LinearSysDT.Trajectory`** — the discrete run is total in the step
  count, which is why sample-time reachability cannot take a bounded domain
  directly and `reach_outer_horizon` unrolls the recursion by hand instead.
- **`TimeIntervalOuterSplitZonotope`** — the one reachability statement still
  tied to a representation. Dropping `0 ∈ U` takes the input set apart into a
  centre, a remainder, a point and a segment, and no interface offers those.
  Either a class earns them or it stays where it is.
- **Nonlinear reachability: the polynomialization variant** that uses
  `PolyZonotope`. The re-linearization loop itself is done.
- **The time between the samples, along a chain.** The re-linearization loop
  encloses the step boundaries only. Covering the interior needs each step's
  time-interval enclosure chained the same way.
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

- **The float layer** — a location's sets, a guard and a reset all round.
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

- **More layers** — in flight: reshape, pooling, convolution, batch
  normalization, softmax. Several may turn out to be `Layer.linear` at a
  particular matrix, which is a result about the library rather than a
  shortfall. Softmax is the one that is genuinely new — the first layer whose
  output coordinate depends on every input coordinate through a normalization,
  which a coordinatewise relaxation cannot express. The composite layers CORA
  builds from these come after.
- **A constant-input step.** The closed loop's trajectory carries the constancy
  a zero-order hold provides; `reach` does not exploit it, handing `LinearSys` a
  *set* of admissible inputs that readmits every jittering input inside it.
  Recovering it means the exponential integral applied to one vector rather than
  `inputSolution`'s set-valued one, which `MatExp` does not offer. This is the
  single largest precision item for a controlled system.
- **A curvature relaxation for sigmoid and tanh** — both carry slope zero,
  which is all monotonicity certifies: the range of `σt - λt` only widens as `λ`
  leaves zero. A useful slope needs second-order information, and the
  `Relaxation` field is already where it would go.
- **Verification beyond propagation** — refinement by splitting the input set,
  which is what makes the method complete in practice.

### The float scalar

- **A sound comparison.** `le` is deliberately unconstrained by
  `SoundFloatArithmetic`, which is right where only a generator ranking depends
  on it. But `expUp` needs its argument bounded and there is nothing sound to
  branch on, so the hypothesis is passed to the caller instead. A constrained
  comparison would make the upper exponential total.
- **Square root**, if an ellipsoid's support function turns out to need one
  rather than a checkable candidate. An upper bound on `√x` is any `s` with
  `x ≤ s·s`, which is a multiplication the scalar already has, so this may cost
  nothing — in flight.
- **The transcendental functions beyond `exp`.** Division and the exponential
  are both there now; a logarithm, a root and the trigonometric functions are
  not, and each has the same shape of question — whether an identity removes the
  series the way argument reduction did for `exp`.

### Infrastructure

- **A worked example per component.** Four exist and each found something. The
  target is one per representation and per algorithm.
- **`HPolytope` instantiates almost nothing**, and the reason is the class shape
  rather than a missing operation. `plusOf`, `linCombOf` and `mtimesOf` all
  exist, but each takes the directions to describe the result on together with a
  bound in each — and `Plus.plus : S → S → S` has room for neither. Supplying
  them internally means solving a linear program per direction, and nothing here
  solves one: `Global/LinProg` consumes a dual solution rather than producing
  it. So a halfspace description cannot take a hybrid jump, which is why the
  bouncing ball's guard is a bounded floor rather than the halfspace it should
  be. This is the same design question `Ellipsoid.plus` and an `And` class raise:
  whether an operation class may carry a precision knob.
- **`Interval` has no vector-family notation**, `ℐ` being the interval *matrix*
  family, so its use sites spell the family out. `PolyZonotope` reaches only the
  plain reachability statement, for want of an `Mtimes ℐ` that would need a fresh
  independent generator per coordinate.
- **A location's sets share one representation** — its invariant, its input set
  and every guard. A guard is often the one thing that wants halfspaces while
  the rest wants a zonotope; separating them means a second type parameter on
  `Location`, and nothing has yet needed it enough.
- **Benchmarks** — the ARCH competition instances CORA reports on.

## Conventions

`CONTRIBUTING.md` states them and `scripts/check-conventions.sh` checks them.
Work that lands here passes both that script and a warning-free `lake build`.
