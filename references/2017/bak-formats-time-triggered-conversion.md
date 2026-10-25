# Time-Triggered Conversion of Guards for Reachability Analysis of Hybrid Automata

```bibtex
@inproceedings{bak2017time,
  author = {Bak, S. and Bogomolov, S. and Althoff, M.},
  title = {Time-Triggered Conversion of Guards for Reachability Analysis of Hybrid Automata},
  booktitle = {Formal Modeling and Analysis of Timed Systems},
  year = {2017}
}
```

**Source:** https://stanleybak.com/papers/bak2017formats.pdf (the author's version on Stanley Bak's page, "DISTRIBUTION A. Approved for public release", 18 pages including the references, read in full; text extracted with `pypdf`). It carries the correction of the scaling function's footnote 4 ("an earlier version had this incorrectly stated"). Volume and pages from the published record (the Springer chapter, doi:10.1007/978-3-319-65765-3_8, was not reachable). CORA cites it in `hybridDynamics/@location/guardIntersect_pancake.m` and `guardIntersect.m` ("Time-Triggered Conversion of Guards for Reachability Analysis of Hybrid Automata"), without a result number.  
**Inventory:** confirmed (against the author's version: Definitions 1-9, Assumptions 1-4, Lemmas 1-2, Corollary 1 and Theorem 1, each with its own counter; Sec. 3.1-3.3 are constructions)

A space-triggered transition, taken when the state meets a linear guard, becomes two time-triggered
ones: an intermediate mode in which the automaton may be in either mode (`Lemma 1`), reached after
the dynamics of the first mode are scaled by the distance to the guard so that the set of
reachable states flattens against the guard (`Lemma 2`), after which the time spent in the
intermediate mode, the only source of error, shrinks with the scaling time (`Thm. 1`). CORA's
`guardIntersect_pancake` is this construction, with the scaled system `ẋ = g(x) f(x)`,
`g(x) = (-a·x + b)/‖a‖`, run by its own `reach`. The results are statements about executions of a
hybrid automaton with differential-inclusion flows (`Def. 1`-`Def. 9`), which the tree's
`HybridAutomaton` (linear location flows driven by an input set, a `IsRun` relation that carries no
elapsed time) does not model, so they live in their own class,
[`DiffInclAutomaton.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/DiffInclAutomaton.lean):
a flow is a set-valued map, a continuous successor a differentiable curve on `[0, t]` with the
invariant and the flow checked on `(0, t)` as `Def. 4` prints it, and `IsExec d m x` an execution of
duration `d`, so `Reach≤T` is `reachLE T`. The paper leaves open one point, which the formalization
settles by proving both readings: `Def. 9` measures the error against `Reach≤T(H)`, the states
reached within time `T`, while the proofs of `Lemma 2` and `Thm. 1` show that every state of the
scaled automaton is reached by some execution of `H` of any duration, a distance of zero to the
unbounded `Reach(H)`. Against `Reach≤T(H)` the printed `Lemma 2` and `Thm. 1` are false; against
`Reach(H)` `Lemma 2` is proved (`fixed`), and `Thm. 1` stays false, since its construction keeps the
dwell time `t₂` of `H` in `m_either`. Flows are Lipschitz by `Def. 2`, which gives the solutions of
`ẋ = f(x)` the proofs use without saying so (existence on every horizon:
[`LipschitzSolution.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/LipschitzSolution.lean)).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Hybrid automaton) H = (Modes, Var, Init, Flow, Trans, Inv) with finitely many modes, n real variables, bounded initial sets Init(m), flows ẋ ∈ f_m(x) (differential inclusions, Lipschitz in the sense of `Def. 2`), transitions (m, G, υ, m') with guard G and reset υ, and invariants Inv(m). | n/a — a definition; the tree's `HybridAutomaton` has linear location flows with an input set and no elapsed time in its runs | `not-a-claim` |
| `Def. 2` | (Distance) d(x, x') = ‖x - x'‖ (L2), d_S(x) = inf{d(x, x') \| x' ∈ S}; the flows are Lipschitz: for each mode some L_m with, for y₁ ∈ f_m(x₁), some y₂ ∈ f_m(x₂) with d(y₁, y₂) ≤ L_m d(x₁, x₂). | n/a — a definition | `not-a-claim` |
| `Def. 3` | (State) A pair (m, x) of a mode and the continuous part x ∈ ℝⁿ. | n/a — a definition | `not-a-claim` |
| `Def. 4` | (Continuous successor) (m, x') follows (m, x) if a differentiable g on [0, t] has g(0) = x, g(t) = x', and (g(δ), ġ(δ)) in the invariant and the flow for δ ∈ (0, t); t is the dwell time. | n/a — a definition | `not-a-claim` |
| `Def. 5` | (Discrete successor) (m', x') follows (m, x) if a transition (m, G, υ, m') has x ∈ G and υ(x) = x'. | n/a — a definition | `not-a-claim` |
| `Def. 6` | (Execution) A finite or infinite sequence of states from an initial state, each a continuous or discrete successor of the one before; its duration is the sum of the dwell times; a prefix. | n/a — a definition | `not-a-claim` |
| `Def. 7` | (Reachable states) Reach(H), the continuous parts of the end states of all executions, and Reach≤T(H) for those of duration at most T. | n/a — a definition | `not-a-claim` |
| `Def. 8` | (Continuous overapproximation) H' is one of H if Reach(H') ⊇ Reach(H) (after projecting out the new variables); with time bounds, Reach≤T(H) ⊆ Reach≤T'(H'). | n/a — a definition | `not-a-claim` |
| `Def. 9` | (Time-bounded continuous overapproximation error) sup_{x' ∈ Reach≤T'(H')} d_{Reach≤T(H)}(x'), the asymmetric Hausdorff distance from Reach≤T'(H') to Reach≤T(H). | n/a — a definition | `not-a-claim` |
| `Assumption 1` | The automaton has two modes m₁ and m₂ with deterministic dynamics connected by one transition, all initial states in m₁. | n/a — a hypothesis of the construction | `not-a-claim` |
| `Assumption 2` | The single transition is space-triggered with one linear condition G = {x \| a·x = b}: no reset, and the invariant of m₁ is a·x ≤ b. | n/a — a hypothesis of the construction | `not-a-claim` |
| `Assumption 3` | At some time t_max all executions have taken the transition. | n/a — a hypothesis of the construction | `not-a-claim` |
| `Assumption 4` | For every time t_γ there is a distance γ from G such that every execution within γ of G takes the transition before t_γ; ensured by ∂B/∂x f_{m₁}(x) ≥ ε > 0 at every point where a transition may occur, B(x) = a·x - b. | n/a — a hypothesis of the proof of `Thm. 1` | `not-a-claim` |
| `Sec. 3.1` | (Direct time-triggered conversion) H_tt: drop the space-triggered transition, add a mode m_either with flow f_either ⊇ f₁ ∪ f₂ and the time variable t, and time-triggered transitions m₁ → m_either at t = t₁ and m_either → m₂ at t = t₂, t₁ such that every execution of duration up to t₁ ends in m₁, and t₂ the smallest time such that every execution of duration at least t₁ + t₂ ends in m₂. | n/a — a construction; its property is `Lemma 1` | `not-a-claim` |
| `Lemma 1` | For any time bound T, H_tt is a time-bounded continuous overapproximation of H with the same time bound. | [`DirectConversionOverapprox.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/DirectConversionOverapprox.lean), [`DirectConversion.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Operations/DirectConversion.lean), [`SpaceTriggered.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Operations/SpaceTriggered.lean), [`IsFirstDwell.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Definitions/IsFirstDwell.lean), [`IsSecondDwell.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Definitions/IsSecondDwell.lean), [`IsContOverapprox.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Definitions/IsContOverapprox.lean) — `H` is `spaceTriggered` (two modes, one linear guard, `Assumption 1`, `Assumption 2`), `H_tt` is `directConversion`, `Reach≤T(H) ⊆ Reach≤T(H_tt)↓Var` for every `T`, under the two properties of the dwell times the construction selects (`IsFirstDwell t₁`, `IsSecondDwell t₁ t₂`) and `f_either ∋ f₁(x), f₂(x)` | `proof-gap` — the proof's first case, "if the mode of s is m₁ then ξ is also directly an execution of H_tt", fails for an execution still in m₁ after t₁: `H_tt` leaves m₁ at t₁ and runs it in m_either, which is why `f_either` must contain `f₁`; the statement holds, and is proved for any t₁, t₂ with the two properties (t₁ is described as "the minimum duration" with them, which is zero, and t₂ as "the smallest time", which need not exist); see Findings |
| `Sec. 3.2` | (Dynamics scaling) For a single-mode H_single, add two copies m_scaling and m' of the mode, a time variable, time-triggered transitions at t_begin and t_scaling, and the flow ẋ = g(x) f(x) in m_scaling, g ≥ 0 a user-defined scalar function. | n/a — a construction; its property is `Lemma 2` | `not-a-claim` |
| `Lemma 2` | For any times T and t_scaling, H_scaling with time bound T' = T + t_scaling is a zero-error time-bounded continuous overapproximation of H_single with time bound T. | [`SingleMode.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Operations/SingleMode.lean), [`ScalingConversion.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Operations/ScalingConversion.lean), [`ScalingConversionNotZeroError.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/ScalingConversionNotZeroError.lean), [`ScalingConversionZeroError.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/ScalingConversionZeroError.lean), [`ScalingConversionContOverapprox.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/ScalingConversionContOverapprox.lean), [`ScalingConversionSubsetReach.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/ScalingConversionSubsetReach.lean), [`ScaledSolutionUnscale.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/ScaledSolutionUnscale.lean), [`IsOverapproxErrorLE.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Definitions/IsOverapproxErrorLE.lean) — `H_single` is `singleMode`, `H_scaling` is `scalingConversion`; `scalingConversion_zeroError` proves the overapproximation at `T + t_scaling` and that everything `H_scaling` reaches, in any time, `H_single` reaches (error zero against `Reach(H)`), for `f` Lipschitz, `g` continuous and nonnegative with `g · f` Lipschitz (`Def. 2`) and `t_begin, t_scaling > 0` (`Sec. 3.2`); `scalingConversion_not_zeroError` is the counterexample at `ẋ = 1`, `g ≡ 1` **Counterexample:** `DiffInclAutomaton.scalingConversion_not_zeroError` | `fixed` — against `Reach≤T(H_single)`, as `Def. 9` and the statement have it, the error is not zero (at ẋ = 1, g ≡ 1, t_begin = t_scaling = T = 1 the scaled automaton reaches 2 by time 2 and `Reach≤1 = [0, 1]`); corrected to the error against the unbounded `Reach(H)`, which is zero, as the proof shows; see Findings |
| `Sec. 3.3` | (Combined scaled time-triggered transformation) Apply the conversion to H, then the scaling to m₁ of H_tt with t_begin = t₁ and the scaling function g(x) = (-a·x + b)/‖a‖, the distance d_G(x), nonnegative in m₁, then the transition m_scaling → m_either directly. | n/a — a construction; its properties are `Cor. 1` and `Thm. 1` | `not-a-claim` |
| `Cor. 1` | For any t_scaling ≥ 0, H_final with time bound T' = T + t_scaling is a time-bounded continuous overapproximation of H with time bound T. | [`FinalConversionContOverapprox.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/FinalConversionContOverapprox.lean), [`FinalConversion.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Definitions/FinalConversion.lean), [`SpaceTriggeredExecOrbit.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/SpaceTriggeredIsExecOrbit.lean), [`ScaledSolutionClockLe.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/ScaledSolutionClockLe.lean), [`ScaledSolutionNonneg.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/ScaledSolutionNonneg.lean) — `H_final` is `finalConversion`, with `g(x) = (b - a·x)/‖a‖` the distance to the guard; for `f₁`, `f₂` Lipschitz and `g · f₁` Lipschitz (`Def. 2`), `t₁, t_scaling ≥ 0` and the two dwell-time properties, `Reach≤T(H) ⊆ Reach≤T+t_scaling(H_final)↓Var` | `proof-gap` — the statement holds, but "since Lemma 1 and Lemma 2 hold" does not give it: `Lemma 2` is about one mode and is false as printed, and the run of `H_final` must be built from the end state of one of `H`, with the scaled run never passing the guard point (`g` and so `g · f₁` vanish on `G`, the step the paper does not mention) and `m_either` getting what is left of the orbit within `t₂`; the duration is `d + t_scaling - σ ≤ T + t_scaling`; see Findings |
| `Thm. 1` | For any time T and error δ > 0 there is a t_scaling such that the time-bounded continuous overapproximation error between H with time bound T and H_final with time bound T' = T + t_scaling is less than δ; one choice is t_scaling > t_max γ, γ the slowdown from the distance bound of `Assumption 4`. | [`FinalConversionNotErrorLt.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/FinalConversionNotErrorLt.lean), [`FinalConversion.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Definitions/FinalConversion.lean), [`IsOverapproxErrorLE.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Definitions/IsOverapproxErrorLE.lean) — at `f₁ = 1`, `f₂ = 0`, guard `x = 0`, initial states `-100` and `-10`, `t₁ = 10`, `t₂ = 100`, `f_either = [0, 1]`, `T = 100`: both dwell-time properties hold, and for every `t_scaling ≥ 0` the error of `finalConversion` against `Reach≤T` is at least 50, so none brings it below δ = 50 (all executions of `H` end in `[-100, 0]`, so against the unbounded `Reach(H)` too) **Counterexample:** `DiffInclAutomaton.finalConversion_not_error_lt` | `false` — the proof bounds the time spent in m_either by t₂ ≤ t_γ, but t₂ is the dwell time of `H` (more than the spread of the arrival times at the guard, here 90), which scaling does not shrink: the run from the state already at the guard spends all of it in m_either; the case m' = m₁ also takes the states of `H_final` of duration up to T + t_scaling for states of `H` of duration T; the claim needs a different construction (a dwell time in m_either recomputed for the scaled automaton), not a different measure; see Findings |
| `Sec. 4` | A drivetrain with backlash, n = 7 + 2θ dimensions, two guards: the transformation analyzes n up to 51 in about 18 minutes in CORA, SpaceEx only n = 11 and 21 (Fig. 5, Table 1). | n/a — an experiment | `not-a-claim` |
| `Sec. 5` | Related work on hybrid automata, flow-pipe construction and guard handling. | n/a — related work | `not-a-claim` |

## Findings

**`Lemma 1` — the case of an execution still in m₁.** The proof starts "If the mode of s is m₁,
then ξ is also directly an execution of H_tt". An execution of `H` can stay in m₁ up to the
largest arrival time at the guard, which is later than `t₁`, the smallest, while `H_tt` leaves m₁
at exactly `t₁` (the guard is `t = t₁` and the invariant `t ≤ t₁`). Such an execution is mirrored
in m_either, whose flow contains `f₁` for this reason; the lemma is true and the induction in
`directConversion_overapprox` carries the `H_tt` execution through m₁, m_either and m₂ by the
duration. The selection of the dwell times is also misworded: `t₁` is "the minimum duration when
every finite execution with duration up to `t₁` has an end state in mode m₁", but the property
holds for every smaller duration too, so what is meant is the largest `t₁` (and the proof needs only
`d < t₁`), and `t₂` is "the smallest time" such that every execution of duration at least
`t₁ + t₂` ends in m₂, which does not exist when an execution is still in m₁ exactly at the
transition (one that reaches the guard at that duration): the admissible `t₂` are open at their
lower end. The lemma holds for every pair with the two properties, and `IsFirstDwell`, `IsSecondDwell`
state them. The invariant of m₂ is not given and is the whole space here.
[`DirectConversionOverapprox.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/DirectConversionOverapprox.lean),
[`IsFirstDwell.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Definitions/IsFirstDwell.lean),
[`IsSecondDwell.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Definitions/IsSecondDwell.lean)

**`Lemma 2` — zero error against which set.** The statement is that `H_scaling` with time bound
`T + t_scaling` is a *zero-error* overapproximation of `H_single` with time bound `T`, that is by
`Def. 9` that every state it reaches within `T + t_scaling` is at distance zero from
`Reach≤T(H_single)`. The proof shows something else: "the point x' will eventually be the continuous
part of a reachable state of H", `d_{Reach(H)}(x') = 0` for the unbounded `Reach(H)`. These differ
as soon as the scaled automaton is not slower than the original: at `ẋ = 1` in one dimension
from `x = 0`, with `g ≡ 1` and `t_begin = t_scaling = T = 1`, `H_scaling` is `H_single` with two
extra mode changes and reaches `2` by time `T' = 2`, while `Reach≤1(H_single) = [0, 1]`. The proof's
own remark that "if ever g(x) > 1, more states may be reached by H_scaling than H for the same
time-bound" is the same observation, and it holds for `g ≤ 1` too: the extra time `t_scaling` is
spent. What is true, and proved, is the overapproximation at `T + t_scaling` and zero error against
`Reach(H)`. Both need what the paper does not say: `g` continuous and nonnegative along the run,
`g · f` Lipschitz so that the scaled flow has solutions (`Def. 2`), `f` Lipschitz so that the
orbit is unique, and `t_begin, t_scaling > 0`; the scaled solution is the original one at the
clock `∫ g`, by uniqueness of solutions of `v̇ = g(y(u)) f(v)`.
[`ScalingConversionNotZeroError.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/ScalingConversionNotZeroError.lean),
[`ScalingConversionZeroError.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/ScalingConversionZeroError.lean),
[`ScaledSolutionUnscale.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/ScaledSolutionUnscale.lean)

**`Cor. 1` — what "follows" needs.** The corollary is read off `Lemma 1` and `Lemma 2`. `H_final`
is not `H_tt` with `Lemma 2` applied to one mode: the m₁ of `H_final` is run for `t₁` and the scaled
copy for `t_scaling`, whose end is `z(t₁ + σ)` on the orbit `z` of `f₁` for a clock `σ`, and the rest
of the orbit and the orbit of `f₂` are then run in m_either and m₂. The clock has to stop at the
guard point `z(τ)`: the scaled run does not cross `G`, because `g` vanishes on `G` and a solution
through a zero of `g · f₁` is constant (`scaledSolution_clock_le`), a step neither lemma contains;
and `g` stays nonnegative along the run (`scaledSolution_nonneg`), as the construction needs and
only says for m₁. With them the execution of `H_final` has duration `d + t_scaling - σ`, at most
`T + t_scaling`. `t_scaling ≥ 0` is enough, `t_scaling = 0` having a scaling mode of dwell zero.
[`FinalConversionContOverapprox.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/FinalConversionContOverapprox.lean),
[`ScaledSolutionClockLe.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/ScaledSolutionClockLe.lean),
[`ScaledSolutionNonneg.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/ScaledSolutionNonneg.lean)

**`Thm. 1` — the error does not go to zero.** The proof treats four cases for the end mode of an
execution `ξ'` of `H_final`. Two of them are about the time bound: in the case m' = m₁ it says
`ξ'` "is directly an execution of H" and so `d(x, x') = 0`, but `ξ'` has duration up to
`T + t_scaling` and the distance is to `Reach≤T`; the same holds for m' = m_scaling, "for any value of
t_scaling" (this is the `Lemma 2` confusion, and it is the reason a state is far from `Reach≤T` here
too). The case m' = m_either is the one that fails for every `t_scaling`: "`t_either` is upper bounded
by `t₂`, which is the maximum amount of time it takes for all executions to reach the single guard
`G`", and then `t₂ ≤ t_γ`, which Assumption 4 gives for the *time needed to take the transition*,
not for the dwell time `t₂` of the construction, which is fixed by `H` (any `t₂` above the spread of
arrival times at `G`, and `H_final` keeps it in m_either) and which scaling does not change. At
`ẋ = 1` in m₁ and `ẋ = 0` in m₂ with the guard `x = 0` and initial states `-100` and `-10` (arrival
times `100` and `10`, so `t₁ = 10` and every `t₂ > 90`), the run from `-10` is on the guard at `t₁`,
where the scaling does nothing, and spends the dwell in m_either with `f_either = [0, 1]`, so with
`t₂ = 100` it reaches `50` within `T' = 100 + t_scaling` for every `t_scaling ≥ 0`, while all
executions of `H` end in `[-100, 0]`. Assumptions 1 to 3 hold, and 4 in the form the paper gives
as sufficient: `∂B/∂x f₁ = 1`. The theorem would need the dwell time in m_either recomputed for the
scaled automaton, which is a different construction, and the bound `‖x'_prefix‖(e^{L t} - 1)` for
the displacement in m_either has no reason to hold either (it is zero at `x'_prefix = 0` for every
`L`, while a constant field moves).
[`FinalConversionNotErrorLt.lean`](../../src/CORALean/HybridDynamics/TimeTriggered/Theorems/FinalConversionNotErrorLt.lean)
