module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Compact

@[expose] public section

/-!
# `ConPolyZono.compact` bounds three counts

Three stages, each keeping a `Finset` of the columns it filters down to: a
merged column never adds one, so the dependent-generator, constraint-generator
and factor counts each shrink or stand, never grow. `m` and `qI` are untouched
by any stage and so carry no bound of their own. `Finset.card_le_univ` against
each stage's ambient `Fin` index closes all three.
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
theorem ConPolyZono.compact_h_le (cPZ : ConPolyZono α) : (cPZ.compact).h ≤ cPZ.h := by
  show (PolyZonotope.compactKeep cPZ.E cPZ.G).card ≤ cPZ.h
  calc (PolyZonotope.compactKeep cPZ.E cPZ.G).card
      ≤ Fintype.card (Fin cPZ.h) := Finset.card_le_univ _
    _ = cPZ.h := Fintype.card_fin cPZ.h

omit [Module ℝ α] in
theorem ConPolyZono.compact_q_le (cPZ : ConPolyZono α) : (cPZ.compact).q ≤ cPZ.q := by
  show (PolyZonotope.compactKeep cPZ.compactGens.R
    (ConPolyZono.consCol cPZ.compactGens.A)).card ≤ cPZ.q
  calc _ ≤ Fintype.card (Fin cPZ.q) := Finset.card_le_univ _
    _ = cPZ.q := Fintype.card_fin cPZ.q

omit [Module ℝ α] in
theorem ConPolyZono.compact_p_le (cPZ : ConPolyZono α) : (cPZ.compact).p ≤ cPZ.p := by
  show (ConPolyZono.usedFactors cPZ.compactGens.compactCons.E
    cPZ.compactGens.compactCons.R).card ≤ cPZ.p
  calc _ ≤ Fintype.card (Fin cPZ.p) := Finset.card_le_univ _
    _ = cPZ.p := Fintype.card_fin cPZ.p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
