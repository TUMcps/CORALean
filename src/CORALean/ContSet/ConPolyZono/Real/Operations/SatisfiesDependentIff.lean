import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPadEIff

/-!
# `ConPolyZono.dependent`'s constraint reads the original factors
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [AddCommGroup α] [Module ℝ α] in
theorem ConPolyZono.satisfies_dependent_iff (cPZ : ConPolyZono α)
    (a : Fin (cPZ.p + cPZ.q) → ℝ) :
    cPZ.dependent.satisfies a ↔ cPZ.satisfies (fun k => a (Fin.castAdd cPZ.q k)) :=
  ConPolyZono.holds_padE_iff cPZ.A cPZ.b cPZ.EC cPZ.q a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
