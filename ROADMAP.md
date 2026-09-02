# Roadmap

What of CORA is formalized, what is being worked on, and what is left. Kept
current as work lands; each open item names what it depends on, so the ones with
no dependencies are the ones that can start.

## In flight

| Branch | Work |
| --- | --- |
| `refactor/dynamics-interfaces` | One file per operation in `ContDynamics`, and reachability stated once against a convexity/compactness class instead of once per representation |
| `feat/poly-zonotope` | `PolyZonotope`, `Real` layer: the type, `plus`, `map`, and the three conversions that check the definition |
| `feat/ellipsoid` | `Ellipsoid`, `Real` layer, stored by generator matrix rather than shape matrix; the support function in closed form, and the tight box that follows from it |

Next up, in rough order: conversions for the two new representations, a
curvature-based relaxation for sigmoid and tanh, nonlinear reachability by
conservative linearization, and the float layers.

## Done

**Global.** Array types, the scalar a layer computes in, entrywise coordinates,
index partitions, block structure, corner combinatorics, sorting. Linear
programming: `SupportBound`, weak duality, composition across the set
operations, and the float counterpart.

**Representations.** `Interval`, `Zonotope`, `HPolytope`, `VPolytope`,
`ConZonotope`, each in both arithmetic layers, with all twenty ordered
conversions in each layer. `InflatedContSet` is what the float layer adds.

**Dynamics.** `LinearSysDT` with reachability. `LinearSys`: the flow in closed
form, the matrix exponential enclosure, discretization, the input solution, the
time-interval enclosure, and reachability at the sample times.
`NonlinearSys` has the representation and its trajectories only.

**Verification.** `Specification` — a safe set or an unsafe one — and the
theorem that a check passed on an outer approximation is passed by the exact
set. Separating directions and halfspace bounds discharge it.

**Neural networks.** The layer interface, the graph, propagation and its
enclosure, and the standard layers: linear, ReLU, sigmoid, tanh. Robust
classification as a specification.

## Open

Ordered roughly by what unblocks the most.

### Representations

- **`PolyZonotope`** — Kochdumper & Althoff, *Sparse polynomial zonotopes*
  (2021). The representation nonlinear reachability needs; nothing below that
  mentions non-convexity can start without it. Real layer first: the type,
  `plus`, `mtimes`, `linComb`, `reduce`, `quadMap`, `restructure`, and the
  interval enclosure.
- **`ConPolyZono`** — constrained polynomial zonotopes, Kochdumper & Althoff
  (2020). Depends on `PolyZonotope`.
- **`Ellipsoid`** — Kurzhanski & Varaiya. Minkowski sum and intersection are
  both outer approximations with a free parameter, which makes it the first
  representation whose operations have a precision knob in the definition.
- **`Capsule`**, **`ZonoBundle`**, **`SpectraShadow`**, **`Taylm`** — CORA has
  them; none blocks anything else.
- **Conversions** for each new representation. Twenty pairs exist for five
  representations; a sixth adds ten more, so these are their own tasks and need
  not land with the representation.
- **`Reduce` methods** — CORA has `girard`, `pca`, `combastel`, `methC`, and the
  order-reduction choice is a precision knob throughout reachability. Only one
  is formalized.
- **Float layers** for every representation added above.

### Dynamics

- **Unified reachability over the interfaces** — one theorem stated against
  `Plus`, `Mtimes`, `LinComb` and the topological properties, rather than one
  per representation. `ReachOuterZonotope` and `ReachOuterConZonotope` are the
  same proof twice.
- **Nonlinear reachability by conservative linearization** — Althoff's thesis,
  ch. 3. Needs the Lagrange remainder as an interval matrix, and
  `PolyZonotope` for the polynomialization variant.
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

- **A curvature-based relaxation for sigmoid and tanh** — both currently carry
  slope zero, which is all monotonicity certifies. Convexity on each half-line
  plus a derivative bound is what CORA uses, and the `Relaxation` field is where
  it goes.
- **The float layer** — needs the two box classes at `Interval 𝕋 n`.
- **More layers** — softmax, batch normalization, convolution, pooling,
  reshape, and the composite layers CORA builds from them.
- **`NeurNetContrSys`** — a network in the loop of a continuous system, which is
  where the two halves of this repository meet.
- **Verification beyond propagation** — refinement by splitting the input set,
  which is what makes the method complete in practice.

### Infrastructure

- **A worked example per component**, executable, so that a representation's
  operations are exercised end to end rather than only proved about.
- **Benchmarks** — the ARCH competition instances CORA reports on.

## Conventions

`CONTRIBUTING.md` states them and `scripts/check-conventions.sh` checks them.
Work that lands here passes both that script and a warning-free `lake build`.
