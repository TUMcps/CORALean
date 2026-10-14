module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
public import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPadEIff

@[expose] public section

/-!
# `ConPolyZono.dependent`'s constraint reads the original factors
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [AddCommGroup α] [Module ℝ α] in
theorem ConPolyZono.satisfies_dependent_iff (cPZ : ConPolyZono α)
    (a : Fin (cPZ.p + cPZ.qI) → ℝ) :
    cPZ.dependent.satisfies a ↔ cPZ.satisfies (fun k => a (Fin.castAdd cPZ.qI k)) :=
  ConPolyZono.holds_padE_iff cPZ.A cPZ.b cPZ.R cPZ.qI a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
