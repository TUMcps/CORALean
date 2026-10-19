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
theorem ConPolyZono.compact_q_le (cPZ : ConPolyZono α) : (cPZ.compact).cons.q ≤ cPZ.cons.q := by
  show (PolyZonotope.compactKeep cPZ.compactGens.cons.R
    (ConPolyZono.consCol cPZ.compactGens.cons.A)).card ≤ cPZ.cons.q
  calc _ ≤ Fintype.card (Fin cPZ.cons.q) := Finset.card_le_univ _
    _ = cPZ.cons.q := Fintype.card_fin cPZ.cons.q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
