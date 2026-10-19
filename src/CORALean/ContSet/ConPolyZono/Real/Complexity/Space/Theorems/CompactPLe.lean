module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Compact

@[expose] public section

/-!
# `ConPolyZono.compact_p_le`

An upper bound on the `p` count of `compact`'s result.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
/-- An upper bound on the `p` count of `compact`'s result. -/
theorem ConPolyZono.compact_p_le (cPZ : ConPolyZono α) : (cPZ.compact).p ≤ cPZ.p := by
  show (ConPolyZono.usedFactors cPZ.compactGens.compactCons.E
    cPZ.compactGens.compactCons.cons.R).card ≤ cPZ.p
  calc _ ≤ Fintype.card (Fin cPZ.p) := Finset.card_le_univ _
    _ = cPZ.p := Fintype.card_fin cPZ.p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
