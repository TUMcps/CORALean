module

public import CORALean.HybridDynamics.HybridAutomaton

@[expose] public section

/-!
# Urgent runs

[1, Def. 1]'s transitions are urgent: a transition is taken as soon as its guard is hit.
`IsUrgentRun` is `IsRun` with that semantics: every stay meets no guard of its location before its
end, and a stay that ends in a jump ends at the first time a guard is met. `IsRun` admits the
non-urgent runs as well, so every enclosure of its reachable states encloses the urgent ones
(`IsUrgentRun.toIsRun`); the reachability results are stated for `IsRun`.

## Inputs
* `ℓ` – location
* `τ` – stay duration
* `x` – trajectory

## Output
* the trajectory meets no guard before time `τ`

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A stay that meets no guard of its location before its end. -/
def Location.IsGuardFreeBefore (ℓ : Location S G L 𝕋 n) (τ : ℝ) (x : ℝ → Vec ℝ n) : Prop :=
  ∀ t ∈ Set.Ico 0 τ, ∀ e ∈ ℓ.trans, x t ∉ construct e.guard

/-- [1, Def. 1]'s runs: as `IsRun`, with every transition taken at the first time its
location's guards are met. -/
inductive HybridAutomaton.IsUrgentRun {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}
    (HA : HybridAutomaton S G L 𝕋 n) :
    L → Vec ℝ n → L → Vec ℝ n → Prop where
  | flow {ℓ : L} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w} (h : (HA.loc ℓ).IsTrajectory τ x u w)
      (hfree : (HA.loc ℓ).IsGuardFreeBefore τ x) :
      HA.IsUrgentRun ℓ (x 0) ℓ (x τ)
  | jump {ℓ ℓ' : L} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w} {y : Vec ℝ n} {e : Transition G L 𝕋 n}
      (h : (HA.loc ℓ).IsTrajectory τ x u w) (hfree : (HA.loc ℓ).IsGuardFreeBefore τ x)
      (hmem : e ∈ (HA.loc ℓ).trans) (hguard : x τ ∈ construct e.guard)
      (rest : HA.IsUrgentRun e.target (e.reset (x τ)) ℓ' y) :
      HA.IsUrgentRun ℓ (x 0) ℓ' y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
