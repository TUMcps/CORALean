# Time-Triggered Conversion of Guards for Reachability Analysis of Hybrid Automata

S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.

**Source:** https://stanleybak.com/papers/bak2017formats.pdf (the author's version on Stanley Bak's page, "DISTRIBUTION A. Approved for public release", 18 pages including the references, read in full; text extracted with `pypdf`). It carries the correction of the scaling function's footnote 4 ("an earlier version had this incorrectly stated"). Volume and pages from the published record (the Springer chapter, doi:10.1007/978-3-319-65765-3_8, was not reachable). CORA cites it in `hybridDynamics/@location/guardIntersect_pancake.m` and `guardIntersect.m` ("Time-Triggered Conversion of Guards for Reachability Analysis of Hybrid Automata"), without a result number.  
**Inventory:** confirmed (against the author's version: Definitions 1-9, Assumptions 1-4, Lemmas 1-2, Corollary 1 and Theorem 1, each with its own counter; Sec. 3.1-3.3 are constructions)

A space-triggered transition, taken when the state meets a linear guard, becomes two time-triggered
ones: an intermediate mode in which the automaton may be in either mode (`Lemma 1`), reached after
the dynamics of the first mode are scaled by the distance to the guard so that the set of
reachable states flattens against the guard (`Lemma 2`), after which the time spent in the
intermediate mode, the only source of error, shrinks with the scaling time (`Thm. 1`). CORA's
`guardIntersect_pancake` is this construction, with the scaled system `ẋ = g(x) f(x)`,
`g(x) = (-a·x + b)/‖a‖`, run by its own `reach`. Nothing here is formalized: the results are
statements about executions of a hybrid automaton with differential-inclusion flows (`Def. 1`-`Def. 9`),
which the tree's `HybridAutomaton` (linear location flows driven by an input set, a `Run`
relation that carries no elapsed time) does not model, and the scaled automata they compare. A reader formalizing them has to settle one point the proofs
leave open: `Def. 9` measures the error against `Reach≤T(H)`, the states reached within time `T`,
while the proofs of `Lemma 2` and `Thm. 1` show that every state of the scaled automaton is reached
by some execution of `H` of any duration, a distance of zero to the unbounded `Reach(H)`.

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
| `Lemma 1` | For any time bound T, H_tt is a time-bounded continuous overapproximation of H with the same time bound. | — | — |
| `Sec. 3.2` | (Dynamics scaling) For a single-mode H_single, add two copies m_scaling and m' of the mode, a time variable, time-triggered transitions at t_begin and t_scaling, and the flow ẋ = g(x) f(x) in m_scaling, g ≥ 0 a user-defined scalar function. | n/a — a construction; its property is `Lemma 2` | `not-a-claim` |
| `Lemma 2` | For any times T and t_scaling, H_scaling with time bound T' = T + t_scaling is a zero-error time-bounded continuous overapproximation of H_single with time bound T. | — | — |
| `Sec. 3.3` | (Combined scaled time-triggered transformation) Apply the conversion to H, then the scaling to m₁ of H_tt with t_begin = t₁ and the scaling function g(x) = (-a·x + b)/‖a‖, the distance d_G(x), nonnegative in m₁, then the transition m_scaling → m_either directly. | n/a — a construction; its properties are `Cor. 1` and `Thm. 1` | `not-a-claim` |
| `Cor. 1` | For any t_scaling ≥ 0, H_final with time bound T' = T + t_scaling is a time-bounded continuous overapproximation of H with time bound T. | — | — |
| `Thm. 1` | For any time T and error δ > 0 there is a t_scaling such that the time-bounded continuous overapproximation error between H with time bound T and H_final with time bound T' = T + t_scaling is less than δ; one choice is t_scaling > t_max γ, γ the slowdown from the distance bound of `Assumption 4`. | — | — |
| `Sec. 4` | A drivetrain with backlash, n = 7 + 2θ dimensions, two guards: the transformation analyzes n up to 51 in about 18 minutes in CORA, SpaceEx only n = 11 and 21 (Fig. 5, Table 1). | n/a — an experiment | `not-a-claim` |
| `Sec. 5` | Related work on hybrid automata, flow-pipe construction and guard handling. | n/a — related work | `not-a-claim` |
