module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Compact

@[expose] public section

/-!
# `ConPolyZono.compact_q_le`

An upper bound on the `q` count of `compact`'s result.
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
/-- An upper bound on the `q` count of `compact`'s result. -/
theorem ConPolyZono.compact_q_le (cPZ : ConPolyZono α) : (cPZ.compact).q ≤ cPZ.q := by
  show (PolyZonotope.compactKeep cPZ.compactGens.R
    (ConPolyZono.consCol cPZ.compactGens.A)).card ≤ cPZ.q
  calc _ ≤ Fintype.card (Fin cPZ.q) := Finset.card_le_univ _
    _ = cPZ.q := Fintype.card_fin cPZ.q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
