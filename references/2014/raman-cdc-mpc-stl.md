# Model Predictive Control with Signal Temporal Logic Specifications

V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and S. A. Seshia. "Model Predictive Control with Signal Temporal Logic Specifications". In Proc. of the 53rd IEEE Conference on Decision and Control (CDC), pp. 81-87, 2014.

**Source:** http://www.cds.caltech.edu/~murray/preprints/ram+14-cdc.pdf (the authors' copy from R. M. Murray's preprint page, headed "2014 Conference on Decision and Control (CDC)", 7 pages, read in full; text extracted with `pypdf`, so `□` and `◇` print alike and are told apart by the text around them). CORA's `stl/robustnessEncodingMILP`, `falsifyTemporalLogic` and `falsifySingleOpt` cite it as "V. Raman and et al, 'Model Predictive Control for Signal Temporal Logic Specifications', 2016"; no 2016 publication of that title by these authors was found, and the encodings CORA cites, Eqs. (3)-(5), are this paper's.  
**Inventory:** confirmed (the numbered items are Equations (1)-(7), Problems 1-2, Table I and Figures 1-2; the encodings of Sec. IV-B and Sec. V are stated in prose, rows of their own named by section)

The source of CORA's mixed-integer encoding of STL robustness (`robustnessEncodingMILP`, used by
the falsification functions). Over discrete time, every subformula `φ` of a formula in negation
normal form gets a variable — binary-valued `z^φ_t` for satisfaction (Sec. IV), real `r^φ_t` for
robustness (Sec. V) — tied to its operands by linear constraints with big-`M` constants, so that
the variable at `t = 0` decides the formula. CORALean formalizes discrete-time STL, its
robustness, each constraint gadget (that it forces the Boolean or `min`/`max` value, and is
satisfiable when `M` is large enough), and the encodings as the values the gadgets force: they
decide the formula and compute its robustness, for a horizon covering the formula's bound and the
until recursion corrected; as printed, the until encoding disagrees with the paper's own
semantics, with a counterexample in Lean, and so do two other claims at their edge cases.

CORA's `robustnessEncodingMILP` encodes the until directly as the robust semantics, a maximum over
`t'` of the minimum of `r^{φ₂}_{t'}` and `r^{φ₁}` on `[t, t']` (`rTmp = [r2(index(i)); r1(cnt:index(i))]`),
not by the printed decomposition; it does not have the finding below, and no coverage note is
needed. Its minimum gadget keeps (3), (4) and the lower half of (5), the upper half being implied
by (4).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. II-A` | Discrete-time systems `x_{t+1} = f(x_t, u_t)` with continuous and logical states and inputs; the horizon-`N` run `x(x₀, u^N) = x₀ x₁ … x_N`; a cost `J`. | n/a — the modelling setting; a run is a signal `ℕ → X` | `not-a-claim` |
| `Sec. II-B (NNF)` | STL formulas are assumed in negation normal form; every STL formula can be rewritten into one of length linear in the original. | n/a — CORALean's discrete-time formulas are in negation normal form by construction, as the encodings require, and it has no discrete-time STL with negation to translate from; note that the grammar has no release operator, so the negation of an until has to be expanded with its operands repeated | `not-covered` |
| `Sec. II-B (semantics)` | `φ ::= μ \| ¬μ \| φ ∧ ψ \| φ ∨ ψ \| □[a,b] ψ \| φ U[a,b] ψ`, `μ` holding where `μ(x(t)) > 0`, `□` on every step of `[t+a, t+b]`, `φ U[a,b] ψ` where `ψ` holds at some `t' ∈ [t+a, t+b]` and `φ` on all of `[t, t']`; `x ⊨ φ` at `t = 0`. | [`DiscreteFormula.lean`](../../src/CORALean/Specification/STL/Definitions/DiscreteFormula.lean) — `STL.DFormula` and `Sat`, with `◇` beside the printed operators, as the encodings treat it, and `a ≤ b` carried by every interval | `correct` |
| `Sec. II-B (eventually)` | `◇[a,b] φ = ⊤ U[a,b] φ`, so that `x ⊨ ◇[a,b] φ` iff `φ` holds at some step between `a` and `b`. | [`EventuallySatIff.lean`](../../src/CORALean/Specification/STL/Theorems/EventuallySatIff.lean) | `correct` |
| `Sec. II-B (bound)` | The bound of a bounded formula, the maximum over the sums of nested upper bounds, is a conservative trajectory length to decide satisfiability; `□[0,10] □[1,6] φ` needs `N ≥ 16`. | [`DFormulaBound.lean`](../../src/CORALean/Specification/STL/Operations/DFormulaBound.lean), [`SatCongr.lean`](../../src/CORALean/Specification/STL/Theorems/SatCongr.lean) — whether `φ` holds at `t` depends only on the run on `[t, t + bound(φ)]`, and the example's bound is `16`  | `correct` |
| `Sec. II-B (bound) (complexity)` | The bound of a bounded formula is computed in time linear in the formula. | n/a — a running time stated of the construction, which the tree can only assert (`Complexity/Time/`) and never prove; see CONTRIBUTING.md, "A size is proved; a running cost is asserted" | `not-a-claim` |
| `Sec. II-C` | The robustness `ρ^φ(x, t)`, by `min` and `max` along the semantics, with `(x, t) ⊨ φ ≡ ρ^φ(x, t) > 0`; e.g. `ρ(□[0,2] μ₁)(x, t) = min_{t∈[0,2]} x(t) - 3`. | [`DiscreteFormula.lean`](../../src/CORALean/Specification/STL/Definitions/DiscreteFormula.lean), [`RobSound.lean`](../../src/CORALean/Specification/STL/Theorems/RobSound.lean), [`Rob.lean`](../../src/CORALean/Specification/STL/Counterexamples/Rob.lean) — `ρ > 0` implies satisfaction and satisfaction `ρ ≥ 0`; the equivalence fails at `ρ = 0`, with a counterexample; the example is the definition at a predicate. The paper prints no `ρ` of `◇`, taken as the `max` dual to `□` **Counterexample:** `STL.DFormula.rob_counterexample` | `fixed` — `≡` fails at `ρ = 0`, see the findings |
| `Sec. III (Problem 1)` | Optimal controller synthesis: minimize `J(x(x₀, u^N))` subject to `x(x₀, u^N) ⊨ φ`. | n/a — a problem statement | `not-a-claim` |
| `Sec. III (Problem 2)` | MPC from STL: at each step, minimize over the horizon-`H` input subject to `x(x₀, u) ⊨ φ`. | n/a — a problem statement | `not-a-claim` |
| `Sec. IV-A` | The system constraints hold iff the trajectory satisfies (1). | n/a — an assumption on the system model, which any MILP-representable system meets by its own encoding | `not-a-claim` |
| `Sec. IV-B` | Each subformula `φ` gets a variable `z^φ_t` with constraints such that `z^φ_t = 1` iff `φ` holds at `t`, generated recursively from `z^φ_0`. | n/a — the plan of the section; the claim is `Sec. IV-B.3 (correctness)` | `not-a-claim` |
| `Sec. IV-B.1` | `μ(x_t) ≤ M_t z^μ_t - ε_t`, `-μ(x_t) ≤ M_t(1 - z^μ_t) - ε_t`, `z^μ_t ∈ {0, 1}`, `M_t` large and `ε_t` small, enforce `z^μ_t = 1` iff `μ(x_t) > 0`. | [`PredEncodingIff.lean`](../../src/CORALean/Specification/STL/Theorems/PredEncodingIff.lean) — for every feasible `z`, `z = 1 ↔ μ(x_t) > 0`; feasible when `ε ≤ \|μ(x_t)\| ≤ M - ε`, a run with `0 < \|μ(x_t)\| < ε` cut off as "bound away from `0`" says | `correct` |
| `Sec. IV-B.2` | Negation `z^ψ_t = 1 - z^μ_t` for `ψ = ¬μ`; the operations enforce `z^ψ_t = 1` if `ψ` holds and `0` otherwise. | [`PredEncodingIff.lean`](../../src/CORALean/Specification/STL/Theorems/PredEncodingIff.lean) — `1 - z = 1 ↔ ¬ μ(x_t) > 0` | `correct` |
| `Sec. IV-B.2 (conjunction)` | `z^ψ_t ≤ z^{φᵢ}_{tᵢ}` and `z^ψ_t ≥ 1 - m + Σᵢ z^{φᵢ}_{tᵢ}`, `z^ψ_t ∈ [0, 1]`. | [`ConjEncodingIff.lean`](../../src/CORALean/Specification/STL/Theorems/ConjEncodingIff.lean) — for binary operands, every feasible `z` is the conjunction, which is feasible | `correct` |
| `Sec. IV-B.2 (disjunction)` | `z^ψ_t ≥ z^{φᵢ}_{tᵢ}` and `z^ψ_t ≤ Σᵢ z^{φᵢ}_{tᵢ}`, `z^ψ_t ∈ [0, 1]`. | [`DisjEncodingIff.lean`](../../src/CORALean/Specification/STL/Theorems/DisjEncodingIff.lean) — for binary operands, every feasible `z` is the disjunction, which is feasible | `correct` |
| `Sec. IV-B.3 (temporal)` | With `a^N_t = min(t+a, N)`, `b^N_t = min(t+b, N)`: `z^{□[a,b] φ}_t = ⋀_{i=a^N_t}^{b^N_t} z^φ_i` enforces `φ` at every step of `[a, b]` relative to `t`; `◇[a,b]` with `⋁`, at some step. | [`MILPEncoding.lean`](../../src/CORALean/Specification/STL/Definitions/MILPEncoding.lean), [`ZEncIffSat.lean`](../../src/CORALean/Specification/STL/Theorems/ZEncIffSat.lean), [`ZEnc.lean`](../../src/CORALean/Specification/STL/Counterexamples/ZEnc.lean) — exact when the horizon covers the bound, `t + bound(φ) ≤ N`; past it the truncated window reads steps the formula does not, with a counterexample **Counterexample:** `STL.DFormula.zEnc_counterexample` **Counterexample:** `STL.DFormula.zEnc_counterexample` | `fixed` — false for a horizon shorter than the bound, where the truncated window reads steps the formula does not; needs `N ≥ t + bound(φ)`, see the findings |
| `Sec. IV-B.3 (until)` | `φ₁ U[a,b] φ₂ = □[0,a] φ₁ ∧ ◇[a,b] φ₂ ∧ ◇[a,a](φ₁ U φ₂)` [7], with `z^{φ₁ U φ₂}_t = z^{φ₂}_t ∨ (z^{φ₁}_t ∧ z^{φ₁ U φ₂}_{t+1})` for `t = 1, …, N-1` and `z^{φ₁ U φ₂}_N = z^{φ₂}_N`. | [`MILPEncoding.lean`](../../src/CORALean/Specification/STL/Definitions/MILPEncoding.lean), [`UntilEncNonstrictIff.lean`](../../src/CORALean/Specification/STL/Theorems/UntilEncNonstrictIff.lean), [`UntilDecompIff.lean`](../../src/CORALean/Specification/STL/Theorems/UntilDecompIff.lean), [`ZEnc.lean`](../../src/CORALean/Specification/STL/Counterexamples/ZEnc.lean) — the recursion as printed lets `φ₂` end the until at a step where `φ₁` fails, which the printed semantics forbids, with a counterexample; with `z^{φ₂}_t ∧ z^{φ₁}_t` in place of `z^{φ₂}_t` (and at `N`), the decomposition is exactly the bounded until; the recursion is read from `t = 0` **Counterexample:** `STL.DFormula.zEnc_counterexample` **Counterexample:** `STL.DFormula.zEnc_counterexample` | `fixed` — the unbounded until's recursion is the strict one, see the findings |
| `Sec. IV-B.3 (correctness)` | By induction on the structure of `φ`, `z^φ_t = 1` iff `φ` holds on the system at `t`. | [`ZEncIffSat.lean`](../../src/CORALean/Specification/STL/Theorems/ZEncIffSat.lean), [`ZEnc.lean`](../../src/CORALean/Specification/STL/Counterexamples/ZEnc.lean) — with the corrected until and `t + bound(φ) ≤ N`; false as printed, both for the until and past the horizon **Counterexample:** `STL.DFormula.zEnc_counterexample` | `fixed` — the until recursion corrected and the horizon assumed, see the findings |
| `Eq. 2` | The final constraint `z^φ_0 = 1`; with the system constraints it gives the MILP of Problem 1, whose feasibility is checked by a solver. | n/a — the constraint; that it selects exactly the satisfying runs is `Sec. IV-B.3 (correctness)` | `not-a-claim` |
| `Sec. IV-B (size)` | `O(N·\|P\|)` binary and `O(N·\|φ\|)` continuous variables; loop constraints add `N` binaries. | n/a — the size of the MILP; CORALean states the encodings by the values they force, with no MILP data structure to count, and the paper defines no loop constraints | `not-covered` |
| `Sec. V` | A variable `r^φ_t` per subformula, generated with the constraints; predicates `r^μ_t = μ(x_t)`, negation `r^ψ_t = -r^μ_t`. | [`MILPEncoding.lean`](../../src/CORALean/Specification/STL/Definitions/MILPEncoding.lean) — `rEnc`, the values the robust constraints force; the claim is `Sec. V (correctness)` | `correct` |
| `Eq. 3-5` | `Σᵢ p^{φᵢ}_{tᵢ} = 1` (3), `r^ψ_t ≤ r^{φᵢ}_{tᵢ}` (4), `r^{φᵢ}_{tᵢ} - (1 - p^{φᵢ}_{tᵢ})M ≤ r^ψ_t ≤ r^{φᵢ}_{tᵢ} + M(1 - p^{φᵢ}_{tᵢ})` (5), binary `p`, `M` large: together they enforce `r^ψ_t = minᵢ r^{φᵢ}_{tᵢ}`. | [`RobustConjEncoding.lean`](../../src/CORALean/Specification/STL/Theorems/RobustConjEncoding.lean) — every feasible `r` is the minimum, for any `M`; the minimum is feasible for `M` at least the spread of the operands | `correct` |
| `Eq. 5` | (3) leaves one `p_j = 1`, and (5) enforces `r^ψ_t = r^{φ_j}_{t_j}` iff `p_j = 1`. | [`RobustSelector.lean`](../../src/CORALean/Specification/STL/Counterexamples/RobustSelector.lean) — the "if" holds; the "only if" fails when two operands tie, with a counterexample **Counterexample:** `STL.robust_selector_counterexample` | `fixed` — only the "if" holds, see the findings |
| `Sec. V (disjunction)` | Disjunction as conjunction with (4) replaced by `r^ψ_t ≥ r^{φᵢ}_{tᵢ}`, enforcing `r^ψ_t = maxᵢ r^{φᵢ}_{tᵢ}`. | [`RobustDisjEncoding.lean`](../../src/CORALean/Specification/STL/Theorems/RobustDisjEncoding.lean) | `correct` |
| `Sec. V (correctness)` | The temporal operators are encoded as in Sec. IV-B.3, `sup` and `inf` being `max` and `min` on a finite trajectory; by induction `r^φ_t > 0` iff `φ` is satisfied at `t`, and the constraints enforce `r^φ_t = ρ^φ(x, t)`. | [`REncEqRob.lean`](../../src/CORALean/Specification/STL/Theorems/REncEqRob.lean), [`UntilRobNonstrictLeIff.lean`](../../src/CORALean/Specification/STL/Theorems/UntilRobNonstrictLeIff.lean), [`REnc.lean`](../../src/CORALean/Specification/STL/Counterexamples/REnc.lean), [`Rob.lean`](../../src/CORALean/Specification/STL/Counterexamples/Rob.lean) — `r^φ_t = ρ^φ(x, t)` with the corrected until and `t + bound(φ) ≤ N`, so `r > 0` implies satisfaction (`Sec. II-C`); as printed the until gives `r = 1` where `ρ = -1`, and at `ρ = 0` the "iff" fails as in `Sec. II-C` **Counterexample:** `STL.DFormula.rEnc_counterexample`, `STL.DFormula.rob_counterexample` | `fixed` — the until recursion corrected and the horizon assumed; `r > 0` is sufficient, not necessary, see the findings |
| `Sec. V (softening)` | The robust encoding allows maximizing `r^φ_0` and relaxing `ρ^φ_0 > 0` to `> -ε`; its cost is more binaries and a nonconvex objective. | n/a — a discussion of the encoding's use | `not-a-claim` |
| `Sec. VI-A` | MPC for bounded formulas: horizon at least the bound, history kept so that the length-`H` prefix satisfies `φ`. | n/a — a control scheme; the property it rests on, that a bounded formula is decided by a prefix, is `Sec. II-B (bound)` | `not-a-claim` |
| `Sec. VI-B` | For safety formulas `□φ_MPC`, trajectories of length `H` satisfying `φ_MPC` are stitched into an infinite one. | n/a — a control scheme for unbounded formulas, outside the bounded grammar | `not-a-claim` |
| `Table I` | Constraints, YALMIP and solver times of the Boolean and robust encodings for four formulas, `N = 30`. | n/a — experiments | `not-a-claim` |
| `Sec. VII` | The experiments, including the building's thermal model, Eqs. (6)-(7), and its MPC formulation. | n/a — experiments and a plant model | `not-a-claim` |
| `Fig. 1` | Resistor-capacitor model of a room. | n/a — an illustration of the plant | `not-a-claim` |
| `Fig. 2` | Room temperature control under an occupancy-dependent STL constraint. | n/a — an experiment | `not-a-claim` |
| `Sec. VIII` | Conclusions and future work. | n/a — discussion | `not-a-claim` |

## Findings

**The until encoding contradicts the paper's own until semantics.** The semantics (Sec. II-B) asks
`φ₁` on all of `[t, t']`, the step `t'` where `φ₂` holds included, and so does the robustness
(Sec. II-C), `min_{t''∈[t,t']} ρ^{φ₁}`. The unbounded until of the encoding,
`z_t = z^{φ₂}_t ∨ (z^{φ₁}_t ∧ z_{t+1})`, asks `φ₁` only before `t'`. On the run
`(1, -1), (-1, 1), …` with `μ₁ = x⁽¹⁾`, `μ₂ = x⁽²⁾`, the formula `μ₁ U[0,1] μ₂` is false at `0`
(`μ₂` fails at `0`, and at `1` `μ₁` does), while the encoding with `N = 1` — enough for the
formula's bound — sets `z = 1`, and the robust encoding `r = 1` where `ρ = -1`
([`ZEnc.lean`](../../src/CORALean/Specification/STL/Counterexamples/ZEnc.lean),
[`REnc.lean`](../../src/CORALean/Specification/STL/Counterexamples/REnc.lean)).
The cause is the identity taken from [7], `φ₁ U[a,b] φ₂ = □[0,a] φ₁ ∧ ◇[a,b] φ₂ ∧ ◇[a,a](φ₁ U φ₂)`,
combined with the strict recursion: it holds for the non-strict unbounded until,
`z_t = (z^{φ₂}_t ∧ z^{φ₁}_t) ∨ (z^{φ₁}_t ∧ z_{t+1})` and `z_N = z^{φ₂}_N ∧ z^{φ₁}_N`, and with it
both encodings are exact
([`ZEncIffSat.lean`](../../src/CORALean/Specification/STL/Theorems/ZEncIffSat.lean),
[`REncEqRob.lean`](../../src/CORALean/Specification/STL/Theorems/REncEqRob.lean)). The recursion
is also printed for `t = 1, …, N-1`, leaving `t = 0`, which a formula at `0` with `a = 0` reads,
undefined; it is read from `0`. CORA's encoding follows the semantics directly and is not
affected.

**The encodings need the horizon to cover the bound.** The windows `[min(t+a, N), min(t+b, N)]`
are cut at the horizon, so for `t + bound(φ) > N` they read fewer steps than the formula: with
`N = 0`, `□[0,1] μ₁` is encoded as `μ₁` at `0` alone and set true on a run where `μ₁` fails at `1`
([`ZEnc.lean`](../../src/CORALean/Specification/STL/Counterexamples/ZEnc.lean)).
Sec. II-B says a trajectory of the bound's length is needed to decide satisfiability; the
correctness claims hold under it, at every `t` with `t + bound(φ) ≤ N`.

**`ρ > 0` is sufficient for satisfaction, not equivalent to it.** With `μ(x₀) = 0`, `¬μ` holds at
`0` while `ρ^{¬μ}(x, 0) = -μ(x₀) = 0`
([`Rob.lean`](../../src/CORALean/Specification/STL/Counterexamples/Rob.lean)).
What holds is `ρ > 0 ⇒ (x, t) ⊨ φ ⇒ ρ ≥ 0`
([`RobSound.lean`](../../src/CORALean/Specification/STL/Theorems/RobSound.lean)), and the robust
encoding inherits it: `r^φ_0 > 0`, the constraint replacing Eq. (2), is sound and misses only
runs on the boundary. The Boolean encoding avoids the case by `ε`: its constraints cut every
run with `|μ(x_t)| < ε`, `μ(x_t) = 0` included.

**Eq. (5) does not pin the selector.** "(5) enforces that `r^ψ_t = r^{φ_j}_{t_j}` iff
`p^{φ_j}_{t_j} = 1`" holds from right to left only: with `r₁ = r₂ = 0`, `p = (1, 0)`, `r = 0`,
`M = 1` all of (3)-(5) hold, and `r = r₂` with `p₂ = 0`
([`RobustSelector.lean`](../../src/CORALean/Specification/STL/Counterexamples/RobustSelector.lean)).
The conclusion drawn from it, `r^ψ_t = minᵢ r^{φᵢ}_{tᵢ}`, needs only the "if" and holds for any
`M`.
