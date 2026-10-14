module

public import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPlusIff
public import CORALean.ContSet.ConPolyZono.Real.Operations.Plus

@[expose] public section

/-!
# `ConPolyZono.plus`'s constraint reads each side's own factors
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
/-- The same at a sum, where the two systems are the two sets'. -/
theorem ConPolyZono.satisfies_plus_iff (cPZ₁ cPZ₂ : ConPolyZono α)
    (a : Fin (cPZ₁.p + cPZ₂.p) → ℝ) :
    (cPZ₁.plus cPZ₂).satisfies a ↔
      cPZ₁.satisfies (fun k => a (Fin.castAdd cPZ₂.p k))
        ∧ cPZ₂.satisfies (fun k => a (Fin.natAdd cPZ₁.p k)) :=
  ConPolyZono.holds_plus_iff cPZ₁.A cPZ₁.b cPZ₁.R cPZ₂.A cPZ₂.b cPZ₂.R a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
