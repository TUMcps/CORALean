import CORALean.ContSet.HPolytope.Real.Operations.OfBounds

/-!
# `HPolytope.ofBoundsOpt`

`ofBounds` where a direction may come back without a bound. The missing row is
not dropped — that would change the row count, and the count is a field — but
replaced by `0 x ≤ 0`, which every point satisfies and which therefore says
nothing.

That is what makes a *total* `plus` possible on a type that admits unbounded
sets: the oracle a closed-over instance would need does not exist, but a partial
one does, and a direction it cannot answer costs precision rather than the
operation.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ} {S : Set α}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One row per direction, a direction with no bound contributing the vacuous
row `0 x ≤ 0`. -/
def HPolytope.ofBoundsOpt (Aq : Fin q → (α →ₗ[ℝ] ℝ))
    (u : ∀ i, Option (SupportBound S (Aq i))) : HPolytope α where
  m := q
  A := fun i => (u i).elim 0 fun _ => Aq i
  b := fun i => (u i).elim 0 SupportBound.val
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
