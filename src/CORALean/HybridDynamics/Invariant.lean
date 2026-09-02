import CORALean.HybridDynamics.HybridAutomaton

/-!
# A set per location that a run cannot leave

One set per location, closed under both things a run does: flowing inside a
location keeps the state in that location's set, and jumping out of it lands
inside the target's. Everything a run can reach is then covered, by induction on
the run and nothing else — which is `Theorems.RunOuter`.

An inductive invariant rather than a list indexed by step count, because a run
here is unbounded in length: `LinearSysDT.holds_of_reach` can answer per step
since `reach` is a function of the step count, and no such index exists once
jumps are in play. The bounded-horizon reading — a family `R : ℕ → L → S n` with
the two conditions shifting the index — is the same induction with an extra
argument and is not written until something needs it.

Both fields are obligations on the caller, and that is deliberate. `flow` is
discharged by `Theorems.FlowOuter`, which is `LinearSys`'s time-interval
enclosure with its hypotheses about the input set; `jump` by
`Theorems.JumpOuter`, whose one hypothesis is an enclosure of the intersection
with the guard. Neither is computed here: finding an `R` that satisfies both is
a fixpoint iteration, and this file states what such an iteration would have to
produce.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet Scalar

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}

structure HybridAutomaton.Invariant (HA : HybridAutomaton S L 𝕋 n) (R : L → S n) : Prop where
  flow {ℓ : L} {τ : ℝ} {x u : ℝ → Vec ℝ n} (h : (HA.loc ℓ).Trajectory τ x u)
    (h₀ : x 0 ∈ construct (R ℓ)) {t : ℝ} (ht : t ∈ Set.Icc 0 τ) :
    x t ∈ construct (R ℓ)
  jump {ℓ : L} {e : Transition S L n} (hmem : e ∈ (HA.loc ℓ).trans) {z : Vec ℝ n}
    (hz : z ∈ construct (R ℓ)) (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (R e.target)

end CORALean.Real
