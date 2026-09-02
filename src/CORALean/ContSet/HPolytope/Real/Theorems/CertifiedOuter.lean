import CORALean.ContSet.HPolytope.Real.Operations.Plus
import CORALean.ContSet.HPolytope.Real.Operations.LinComb
import CORALean.ContSet.HPolytope.Real.Operations.Mtimes
import CORALean.ContSet.HPolytope.Real.Operations.IntervalOf

/-!
# The certified operations enclose

All four for the same reason and in one line each: each is `ofBounds` over
directions the caller chose, `ofBounds` states exactly what its certificates
say, and the certificates were composed to speak about the result. The work is
in `Global.LinProg`, and none of it is repeated here.

None of these is exact, and the loss is not in the proof but in the choice of
directions — which is the caller's, and a precision knob rather than a
correctness one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Pointwise

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
variable {q n : ℕ}

theorem HPolytope.plusOf_outer {P₁ P₂ : HPolytope α} (Aq : Fin q → (α →ₗ[ℝ] ℝ))
    (u₁ : ∀ i, SupportBound P₁.construct (Aq i))
    (u₂ : ∀ i, SupportBound P₂.construct (Aq i)) :
    P₁.construct + P₂.construct ⊆ (HPolytope.plusOf Aq u₁ u₂).construct :=
  HPolytope.subset_ofBounds _ _

theorem HPolytope.linCombOf_outer {P₁ P₂ : HPolytope α} (Aq : Fin q → (α →ₗ[ℝ] ℝ))
    (u₁ : ∀ i, SupportBound P₁.construct (Aq i))
    (u₂ : ∀ i, SupportBound P₂.construct (Aq i)) :
    segments P₁.construct P₂.construct ⊆ (HPolytope.linCombOf Aq u₁ u₂).construct :=
  HPolytope.subset_ofBounds _ _

theorem HPolytope.mtimesOf_outer {P : HPolytope α} (M : α →ₗ[ℝ] β)
    (Aq : Fin q → (β →ₗ[ℝ] ℝ)) (u : ∀ i, SupportBound P.construct ((Aq i).comp M)) :
    ⇑M '' P.construct ⊆ (HPolytope.mtimesOf M Aq u).construct :=
  HPolytope.subset_ofBounds _ _

theorem HPolytope.intervalOf_outer {P : HPolytope (Vec ℝ n)}
    (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.intervalOf up lo).construct :=
  Interval.subset_ofBounds up lo

end CORALean.Real
