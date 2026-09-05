import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPlusIff
import CORALean.ContSet.ConPolyZono.Real.Operations.Plus

/-!
# `ConPolyZono.plus`'s constraint reads each side's own factors
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

omit [Module ℝ α] in
/-- The same at a sum, where the two systems are the two sets'. -/
theorem ConPolyZono.satisfies_plus_iff (C₁ C₂ : ConPolyZono α)
    (a : Fin (C₁.p + C₂.p) → ℝ) :
    (C₁.plus C₂).satisfies a ↔
      C₁.satisfies (fun k => a (Fin.castAdd C₂.p k))
        ∧ C₂.satisfies (fun k => a (Fin.natAdd C₁.p k)) :=
  ConPolyZono.holds_plus_iff C₁.A C₁.b C₁.EC C₂.A C₂.b C₂.EC a

end CORALean.Real
