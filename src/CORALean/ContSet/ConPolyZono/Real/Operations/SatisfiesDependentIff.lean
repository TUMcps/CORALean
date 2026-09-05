import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPadEIff

/-!
# `ConPolyZono.dependent`'s constraint reads the original factors
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

omit [AddCommGroup α] [Module ℝ α] in
theorem ConPolyZono.satisfies_dependent_iff (C : ConPolyZono α)
    (a : Fin (C.p + C.q) → ℝ) :
    C.dependent.satisfies a ↔ C.satisfies (fun k => a (Fin.castAdd C.q k)) :=
  ConPolyZono.holds_padE_iff C.A C.b C.EC C.q a

end CORALean.Real
