# Roadmap

What of CORA is formalized, what is being worked on, and what is left. Kept
current as work lands; each open item names what it depends on, so the ones with
no dependencies are the ones that can start.

## In flight

| Branch | Work |
| --- | --- |
| `feat/con-poly-zono` | `ConPolyZono`, `Real` layer, and the intersection that justifies a constrained representation |
| `feat/trajectory-domain` | A time domain on `Trajectory`, so a bounded horizon is sayable — what the re-linearization loop and hybrid automata both wait on |

Next after those: hybrid automata, the conversions the newest representations do
not yet have, `PolyZonotope.reduce`, and the float layers.

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
`reduce` is deliberately absent; see below.

**Dynamics.** `LinearSysDT` with reachability. `LinearSys`: the flow in closed
form, the matrix exponential enclosure, discretization, the input solution, the
time-interval enclosure, and reachability at the sample times — stated once
against `ConvexSet` and `CompactSet` rather than once per representation.

`NonlinearSys`, one step by conservative linearization. The abstraction error is
a certificate rather than a derivative: a set together with the proof that it
encloses what is left of the field once the affine part is subtracted. Nothing
downstream mentions a derivative, so `A` and `B` need not be the Jacobians and a
linearization computed in float arithmetic is covered without a word about how
far it is from the true one. A confined run is then a linear run over a widened
input, and reachability is the linear theorem unchanged.

**Verification.** `Specification` — a safe set or an unsafe one — and the
theorem that a check passed on an outer approximation is passed by the exact
set. Separating directions and halfspace bounds discharge it.

**Neural networks.** The layer interface, the graph, propagation and its
enclosure, and the standard layers: linear, ReLU, sigmoid, tanh. Robust
classification as a specification.

## Open

Ordered roughly by what unblocks the most.

### Representations

- **`PolyZonotope.reduce`** — absent on purpose rather than overlooked. It is
  not the zonotope's generator ranking: it also has to merge equal exponent
  columns and drop factors that fall out of use, and without that compaction an
  order bound means nothing. `restructure` likewise.
- **`Capsule`**, **`ZonoBundle`**, **`SpectraShadow`**, **`Taylm`** — CORA has
  them; none blocks anything else.
- **Conversions** for the late arrivals. `Ellipsoid` has four of its ten pairs
  and `PolyZonotope` four of its ten; the gaps differ in kind, an ellipsoid's
  polytope pairs being merely absent while a polynomial zonotope's are
  enclosures with a precision knob rather than conversions, its sets not being
  convex.
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

- **`TimeIntervalOuterSplitZonotope`** — the one reachability statement still
  tied to a representation. Dropping `0 ∈ U` takes the input set apart into a
  centre, a remainder, a point and a segment, and no interface offers those.
  Either a class earns them or it stays where it is.
- **Nonlinear reachability, beyond one step** — the polynomialization variant
  that uses `PolyZonotope`, and the loop that re-linearizes. The loop is blocked
  on `feat/trajectory-domain`: re-linearizing means each step is sound only on
  its own interval, and a `Trajectory` cannot yet name one.
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

- **`Location`, `Transition`, `HybridAutomaton`** — guard intersection and the
  jump map. Guard intersection wants `ConZonotope`, which exists, and the
  time-triggered case wants nothing else.
- **`ParallelHybridAutomaton`** — composition.

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

- **A worked example per component.** `Examples/FeedForward.lean` is the first,
  and it exists because a library cannot notice a broken instance from the
  inside — only a use site can. One per representation and per algorithm is the
  target.
- **Specializations as regression tests.** Reachability is now stated once over
  `ConvexSet` and `CompactSet`, and the old per-representation statements were
  checked to follow with `:=` and then discarded. They belong in `Examples/`,
  where they would fail the build if the generalization ever stopped covering
  them.
- **Benchmarks** — the ARCH competition instances CORA reports on.

## Conventions

`CONTRIBUTING.md` states them and `scripts/check-conventions.sh` checks them.
Work that lands here passes both that script and a warning-free `lake build`.
