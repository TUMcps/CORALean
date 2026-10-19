# Parsimonious, Simulation Based Verification of Linear Systems

P. S. Duggirala and M. Viswanathan. "Parsimonious, Simulation Based Verification of Linear Systems". CAV, 2016.

**Source:** https://www.cs.unc.edu/~psd/files/research/2016/duggirala-cav-2016-parsimonious-verification.pdf (the first author's copy of the paper, read in full; text extracted with `pypdf`). Numbering is that of this copy.  
**Inventory:** confirmed (the numbered items are Definitions 1-4, Examples 1-2, Algorithms 1-3, Theorems 1-3, Remark 1 and Corollary 1)

Where the star set comes from: the paper introduces the *generalized star set* `⟨x₀, V, P⟩`, a center, a
basis and a predicate on the coefficients, as the representation in which the reachable set of a linear
system is computed from `n + 1` simulations. CORALean takes the representation only. Its `StarSet` is
the definition with the predicate any of CORALean's representations in coefficient space (a
`LevelSet` for a nonlinear one, as the paper's disc example) and, as in CORA, a box on the
coefficients always beside it; CORA's `neuralNetwork` uses an `HPolytope` predicate, at which a star
set is a bounded polytope. The simulation-based reachability algorithms and their
guarantees are not formalized.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Generalized star set) A tuple Θ = ⟨x₀, V, P⟩ with center x₀ ∈ ℝⁿ, basis V = {v₁, …, v_m} of m (≤ n) vectors, and a predicate P : ℝⁿ → {⊤, ⊥}; it denotes {x \| ∃ ᾱ, x = x₀ + Σ αᵢvᵢ ∧ P(ᾱ) = ⊤}. | n/a — done differently on purpose: [`StarSet.lean`](../../src/CORALean/ContSet/StarSet/Real/StarSet.lean) — `StarSet P n` carries CORA's coefficient box `[l, u]` beside the predicate, an element of the family `P` of coefficient-space representations, so it denotes the star sets whose coefficients are bounded, and a `LevelSet` states an arbitrary predicate ([`OfPred.lean`](../../src/CORALean/ContSet/StarSet/Real/Operations/OfPred.lean), any predicate on a box as a star set); [`StarSet.lean`](../../src/CORALean/ContSet/StarSet/Float/StarSet.lean), the float layer, at CORA's polytope predicate only; [the coverage README, departures from CORA](../coverage/README.md#departures-from-cora-that-belong-to-no-single-method) | `done-differently` |
| `Example 1` | A rectangle as a star set with the linear predicate Cᾱ ≤ g, and a disc with a quadratic predicate. | n/a — an illustration of Def. 1, not a claim | `not-a-claim` |
| `Def. 2` | (Validated simulation) A sequence of sets Rᵢ with time steps at most h, each containing the trajectory on its interval and of diameter at most ϵ. | n/a — simulation-based verification, a subject CORALean does not cover | `not-covered` |
| `Def. 3` | The set reachable within time T, and over- and under-approximations of it. | n/a — restates the standard notion of a reachable set and its enclosures | `not-a-claim` |
| `Def. 4` | The system is safe for time T if ReachSet(Θ, T) ∩ U = ∅. | n/a — restates the standard notion of safety | `not-a-claim` |
| `Alg. 1` | Reachable set at time t from n + 1 exact trajectories, by superposition. | n/a — simulation-based verification, a subject CORALean does not cover | `not-covered` |
| `Thm. 1` | The set returned by Algorithm 1 is the reachable set at time t. | n/a — simulation-based verification, a subject CORALean does not cover | `not-covered` |
| `Example 2` | A car in one dimension, Algorithm 1 run by hand. | n/a — an illustration, not a claim | `not-a-claim` |
| `Alg. 2` | Over- and under-approximation of the reachable set from validated simulations. | n/a — simulation-based verification, a subject CORALean does not cover | `not-covered` |
| `Thm. 2` | OverReach[j] and UnderReach[j] of Algorithm 2 over- and under-approximate the reachable set on the j-th interval. | n/a — simulation-based verification, a subject CORALean does not cover | `not-covered` |
| `Remark 1` | Algorithm 2 can be used for safety verification with an SMT solver. | n/a — a remark on use, not a claim to formalize | `not-a-claim` |
| `Thm. 3` | The over-approximation OA lies in the bloating Bδ(R) of a star set R, with δ = 3ϵ. | n/a — simulation-based verification, a subject CORALean does not cover | `not-covered` |
| `Cor. 1` | The same bound for an ellipsoidal initial set ⟨x₀, V, C, 1⟩. | n/a — simulation-based verification, a subject CORALean does not cover | `not-covered` |
| `Alg. 3` | Reachable set of a hybrid system by iterating Algorithm 2 and the invariant and guard steps; need not terminate. | n/a — simulation-based verification, a subject CORALean does not cover | `not-covered` |
