# Reachability Analysis of Nonlinear Systems with Uncertain Parameters using Conservative Linearization

M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear Systems with Uncertain Parameters using Conservative Linearization". In Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008, pp. 4042-4048.

**Source:** https://skoge.folk.ntnu.no/prost/proceedings/cdc-2008/data/papers/0299.pdf (the proceedings PDF, ThTA08.5, 7 pages, read in full; text extracted with `pypdf`)  
**Inventory:** confirmed (Definitions 1-2 and Propositions 1-3, each with its own counter, equations (1)-(7) and Fig. 1; there are no Theorems, Lemmas or numbered Algorithms)

The origin of CORA's `'lin'` algorithm for `nonlinearSys`: linearize on the fly,
bound the Lagrange remainder by a box that is added as an uncertain input, and
split the start set when the box exceeds an admissible one. Althoff's thesis (2010)
reproduces it in its §3.4, and the rows
below that are the same result link the same files; this page is where the
propositions first appeared.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | The exact reachable set R_e(r) at time r of ẋ = f(x(t), u(t), p(t)) from x(0) ∈ X_0, for Lipschitz-continuous inputs u(t) ∈ U and time-varying parameters p(t) ∈ P: {x \| x(t) is a solution of (1), t = r}. | [`ReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/ReachSetExact.lean) — `NonlinearSys.reachSetExact`; a parameter that may vary in time within `P` is one more input, so `(u, p)` is the input and `U × P` its set; the trajectories are the tree's Carathéodory runs, the integral equation with a measurable field and no Lipschitz condition on the input; the paper's solutions, under Lipschitz-continuous inputs, are among them and are the classical ones (`NonlinearSys.IsTrajectory.hasDerivWithinAt`) | `correct` |
| `Def. 2` | (Zonotope) Z = {c + Σ β^(i) g^(i) \| -1 ≤ β^(i) ≤ 1}, written (c, g^(1...p)); order p/n. | n/a — restated; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 2` | The first-order Taylor expansion of f_i at z* with Lagrange remainder ½(z - z*)ᵀ ∂²f_i(ξ, p)/∂z² (z - z*), ξ on the segment from z* to z, encloses ẋ_i. | [`TaylorLagrangeSegment.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/TaylorLagrangeSegment.lean) — `f(z) = f(z*) + ∇f(z*)(z - z*) + ½ D²f(ξ)(z - z*, z - z*)` at some `ξ` on the segment from `z*` to `z`, for `f` of class `C²` in the stacked variable, a parameter being one more coordinate of it; [`AbstractionErrorOfHessian.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AbstractionErrorOfHessian.lean) — the same remainder bounded by an entrywise bound on the second derivative over the segment, the form `Prop. 1` spends | `correct` |
| `Eq. 3` | The linearized system ẋ ∈ AΔx + BΔu + f(x*, u*, p) + L, A and B the Jacobians at the expansion point and L the set of linearization errors. | [`IsAbstractionError.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/IsAbstractionError.lean) — `L` as a certificate over `R × U`; `A` and `B` need not be the Jacobians, and there is no parameter, the input standing for it as in `Def. 1` | `correct` |
| `Eq. 4` | The interval hull of a zonotope, IH(Z) = [c - Σ\|g^(i)\|, c + Σ\|g^(i)\|]. | n/a — restated from [18]; tracked as `Sec. 3.4` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Sec. IV-A` | By superposition, R(t) = R_lin(t) + R_err(t), the reachable set of the linearized system without error plus that due to the error input L, encloses the reachable set of the nonlinear system, since L contains every linearization error. | n/a — done differently on purpose: the error set `L` joins the linearized system's input set and that system is run once, a confined nonlinear run being one of its runs and so in its reachable set ([`Linearize.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/Linearize.lean), [`ReachOuter.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ReachOuter.lean)). The printed `R_lin ⊕ R_err` needs the run's input split into a measurable linear part and a measurable error part, and a run here carries a measurable field, not a measurable input; [the coverage README, departures from CORA](../coverage/README.md#departures-from-cora-that-belong-to-no-single-method) | `done-differently` |
| `Prop. 1` | \|L_i\| ⊆ [0, L̂_i] with L̂_i = ½ γᵀ max(\|J_i(ξ(z), p)\|) γ over z ∈ Z, p ∈ P, and γ = \|c - z*\| + Σ\|g^(i)\| for Z = (c, g^(1...p)); max and absolute values entrywise. | [`AbstrErrLin.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AbstrErrLin.lean), [`AbstractionErrorOfHessian.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AbstractionErrorOfHessian.lean), [`FloatModel.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/FloatModel.lean), [`SlopeRemainder.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/SlopeRemainder.lean) — the bound on `\|J_i\|` is an argument `H`, its interval-arithmetic evaluation the caller's, and no parameter box, as for the thesis's `Prop. 3.7` | `correct` |
| `Prop. 2` | The bound L̂ of Prop. 1 is minimized by choosing z* = c. | [`AbstrErrLinCenterSubset.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AbstrErrLinCenterSubset.lean) — at one entrywise-nonnegative bound `H` on both sides | `proof-gap` — the proof says `max(\|J_i(ξ(z), p)\|)` is not affected by `z*`; the range of `ξ` grows when `z* ∉ Z`, and the claim holds because a bound valid at any `z*` is valid at the center; see Findings |
| `Sec. V` | The expansion point, z* = ĉ + (r/2) f(ĉ, mid(p)), ĉ the center of Z(0), approximates the center of Z([0, r]), which is not yet known. | [`LinPoint.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/LinPoint.lean) — the state part moved half a step along the field, the input part at the input set's center | `underspecified` — `ĉ` is the center of `R(0) × U` and `f` is n-dimensional, so the sum is read as moving the state block only |
| `Eq. 7` | With R̄_err(r) = A⁻¹(e^{Ar} - I)[-L̂, L̂] and the requirement R̄_err(r) ⊆ [-θr, θr] (6), (e^{Ar} - I)⁻¹A[-θr, θr] ⊇ [-L̂, L̂], "which is fulfilled if" \|(e^{Ar} - I)⁻¹A\| θ r =: L̄ ≥ L̂. | [`AdmissibleLinError.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/AdmissibleLinError.lean), [`AdmissibleLinErrorNotSufficient.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AdmissibleLinErrorNotSufficient.lean), [`ErrReachSubsetOfAbsLe.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ErrReachSubsetOfAbsLe.lean) — `L̄` as printed, the two-dimensional counterexample, and the condition that does suffice, `\|A⁻¹(e^{Ar} - I)\| L̂ ≤ θ r` **Counterexample:** `NonlinearSys.admissibleLinError_not_sufficient` **Counterexample:** `NonlinearSys.admissibleLinError_not_sufficient` | `fixed` — `L̂ ≤ L̄` does not give (6): at `A = [[1, 1], [0, 2]]`, `r = 1`, `θ = (1, 1)` the corner `L̄` leaves the box; corrected to a test on `A⁻¹(e^{Ar} - I)` itself; see Findings |
| `Prop. 3` | A zonotope Z = (c, g^(1...p)) is split along its j-th generator into Z_1 = (c - ½g^(j), ..., ½g^(j), ...) and Z_2 = (c + ½g^(j), ..., ½g^(j), ...) with Z_1 ∪ Z_2 = Z and Z_1 ∩ Z_2 = Z* = (c, g^(1...j-1), g^(j+1...p)). | [`Split.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/Split.lean), [`SplitUnion.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SplitUnion.lean), [`SplitIntersection.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SplitIntersection.lean) | `proof-gap` — `Z₁ ∩ Z₂ = Z*` is read off `(Z* + S₁) ∩ (Z* + S₂) = Z* + (S₁ ∩ S₂)`, false for sets; it holds because `Z*` is convex; see Findings |
| `Sec. VI-A` | The generator to split is the j of least performance index ρ_j = max(L̂_{1,j}/L̄_j) · max(L̂_{2,j}/L̄_j); a value below one means the limit (7) is met by both halves. | [`SplitRank.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/SplitRank.lean) | `underspecified` — printed as a product, but "less than one implies (7) holds" needs both factors below one, which a product under one does not give; formalized as printed |
| `Fig. 1` | One time step: linearize, compute R_lin, obtain L̄, compute L from R_lin and L̄; if L ⊄ L̄ split R((k-1)r) into two sets and repeat, else R(kr) = R_lin(kr) + R_err; cancel redundant sets; next step. | [`SplitReach.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/SplitReach.lean), [`SplitReachOuter.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/SplitReachOuter.lean) — the step with its split-and-repeat branch, the step and the choice of generator as arguments and the depth bounded by fuel; what the step promises for an accepted set holds for every start in `R`. The time loop and the cancellation are not in it | `underspecified` — the figure's split-and-repeat has no bound; a fuel bound makes it terminate |
| `Sec. VI-B` | Redundant reachable sets are cancelled: enclosed by polytopes, a segment whose set difference with the polytopes of the past ζ steps is empty is dropped, every δ steps. | [`CancelRedundant.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/CancelRedundant.lean), [`CancelRedundantCovers.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/CancelRedundantCovers.lean) — `NonlinearSys.cancelRedundant` drops, at every δ-th step, the segments whose polytope minus the polytopes of the past ζ steps is empty; `cancelRedundant_covers`: every point of a current segment is in a kept segment or in a past polytope. The polytope enclosure and the conversion of the kept polytopes back to zonotopes are the caller's | `underspecified` — "reached before" holds up to the polytope enclosures of the past segments, and nothing printed says why dropping a segment loses no later reachable state; see Findings |
| `Sec. VII` | Van der Pol oscillator and water-tank systems with 6 to 30 states (Figs. 5-6, Table I). | n/a — an experiment, not a claim to formalize | `not-a-claim` |

## Findings

**`Eq. 7` — the admissible error.** The paper multiplies the requirement `R̄err(r) =
A⁻¹(e^{Ar} - I)[-L̂, L̂] ⊆ [-θr, θr]` by `M := (e^{Ar} - I)⁻¹A` to get `[-L̂, L̂] ⊆
M[-θr, θr]`, and says this "is fulfilled if `|M| θ r =: L̄ ≥ L̂`". But `|M| θ r` is
the radius of the interval hull of `M[-θr, θr]`, and a box inside the hull of a
parallelotope need not be inside the parallelotope. At `A = [[1, 1], [0, 2]]`, `r = 1`,
`θ = (1, 1)` and `L̂ = L̄ = (2e/(e² - 1), 2/(e² - 1))`, the corner `L̂` is mapped by
`A⁻¹(e^{A} - I) = [[e - 1, (e - 1)²/2], [0, (e² - 1)/2]]` to a point with first
coordinate `(3e - 1)/(e + 1) > 1`. The condition holds in one dimension and at a
diagonal `A`; in general what suffices is the test on the matrix itself, `|A⁻¹(e^{Ar}
- I)| L̂ ≤ θ r`. The formula for `R̄err(r)` is quoted from the authors' earlier work
and not examined here.
[`AdmissibleLinErrorNotSufficient.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AdmissibleLinErrorNotSufficient.lean),
[`ErrReachSubsetOfAbsLe.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/ErrReachSubsetOfAbsLe.lean)

**`Prop. 2` — the Hessian range.** The proof says that at `z* = c`, `{ξ(z) | z ∈ Z} = Z`
"(which is independent of `z*`)", so that `max(|J_i(ξ(z), p)|)` is not affected by the
linearization point. That range is the convex hull of `Z` and `z*`, which is `Z` only
when `z* ∈ Z` and is larger otherwise, so the max is affected. The proposition holds
because the dependence runs one way: a bound valid at any `z*` is valid at the center.
The thesis repeats the argument for its `Cor. 3.2`.
[`AbstrErrLinCenterSubset.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AbstrErrLinCenterSubset.lean)

**`Prop. 3` — the intersection.** The proof reads `Z₁ ∩ Z₂ = Z*` off
`(-½g^(j), ½g^(j)) ∩ (½g^(j), ½g^(j)) = {0}`, which needs `(Z* + S₁) ∩ (Z* + S₂) =
Z* + (S₁ ∩ S₂)`, false for sets (`Z* = [0, 1]`, `S₁ = {0}`, `S₂ = {1}` in ℝ). The
claim holds because `Z*` is convex.
[`SplitIntersection.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/SplitIntersection.lean)

**`Sec. VI-A` — the performance index.** `ρ_j` is printed as a product of the two
halves' worst ratios, and the next sentences read a value below one as both halves
meeting the limit (7). A product below one bounds neither factor (`0.1 · 5 < 1`); a
maximum or a sum of the two would. Formalized as printed: a ranking carries no
soundness obligation.
[`SplitRank.lean`](../../src/CORALean/ContSet/Zonotope/Real/Operations/SplitRank.lean)

**`Sec. VI-B` — what a cancelled segment has reached.** The check compares the polytope enclosure of a segment with the polytopes of the past `ζ` steps, so a dropped segment is only inside an over-approximation of the sets reached before, which the paper grants ("leads to an over-approximation"). Whether dropping it also loses no state reached *later* is not argued: it needs the start set of the segment to lie in a start set already propagated, a time-invariant system and the horizon not shortening the earlier copy's future. What is proved is the covering the check gives, `cancelRedundant_covers`; the effect on later steps is not, the time loop not being in the tree.
[`CancelRedundantCovers.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/CancelRedundantCovers.lean)
