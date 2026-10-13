import CORALean.HybridDynamics.HybridAutomaton

/-!
# A set per location that a run cannot leave

One set per location, closed under both things a run does: flowing inside a
location keeps the state in that location's set, and jumping out of it lands
inside the target's. Everything a run can reach is then covered, by induction on
the run and nothing else — which is `Theorems.RunOuter`.

`R` is in the state's representation `S`, the guard it is cut against in `G`:
the two never meet except as sets, `construct (R ℓ) ∩ construct e.guard` (#39).

An inductive invariant rather than a family indexed by step count, because a run
here is unbounded in length: `LinearSysDT.holds_of_reach` answers per step since
`reach` is a function of that count, and no such index exists once jumps appear.

Both fields are obligations on the caller. `flow` is discharged by
`Theorems.FlowOuter`, `LinearSys`'s time-interval enclosure with its hypotheses
about the input set; `jump` by `Theorems.JumpOuter`, whose one hypothesis is an
enclosure of the intersection with the guard. Neither is computed here.
-/

-- Authors:       Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure HybridAutomaton.Invariant (HA : HybridAutomaton S G L 𝕋 n) (R : L → S n) : Prop where
  flow {ℓ : L} {τ : ℝ} {x u : ℝ → Vec ℝ n} (h : (HA.loc ℓ).Trajectory τ x u)
    (h₀ : x 0 ∈ construct (R ℓ)) {t : ℝ} (ht : t ∈ Set.Icc 0 τ) :
    x t ∈ construct (R ℓ)
  jump {ℓ : L} {e : Transition G L 𝕋 n} (hmem : e ∈ (HA.loc ℓ).trans) {z : Vec ℝ n}
    (hz : z ∈ construct (R ℓ)) (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (R e.target)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
