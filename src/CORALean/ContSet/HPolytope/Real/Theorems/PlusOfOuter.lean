import CORALean.ContSet.HPolytope.Real.Operations.Plus

/-!
# The certified Minkowski sum encloses

One line: `plusOf` is `ofBounds` over directions the caller chose, `ofBounds`
states exactly what its certificates say, and the certificates were composed to
speak about the sum. The work is in `Global.LinProg`, and none of it is repeated
here.

Not exact, and the loss is not in the proof but in the choice of directions —
which is the caller's, and a precision knob rather than a correctness one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]
variable {q : ℕ}

theorem HPolytope.plusOf_outer {P₁ P₂ : HPolytope α} (Aq : Fin q → (α →ₗ[ℝ] ℝ))
    (u₁ : ∀ i, SupportBound P₁.construct (Aq i))
    (u₂ : ∀ i, SupportBound P₂.construct (Aq i)) :
    P₁.construct + P₂.construct ⊆ (HPolytope.plusOf Aq u₁ u₂).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Real
