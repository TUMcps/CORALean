import CORALean.ContSet.ConPolyZono.Real.Operations.Compact

/-!
# `ConPolyZono.compact` bounds three counts

Three stages, each keeping a `Finset` of the columns it filters down to: a
merged column never adds one, so the dependent-generator, constraint-generator
and factor counts each shrink or stand, never grow. `m` and `q` are untouched
by any stage and so carry no bound of their own. `Finset.card_le_univ` against
each stage's ambient `Fin` index closes all three.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
theorem ConPolyZono.compact_h_le (C : ConPolyZono α) : (C.compact).h ≤ C.h := by
  show (PolyZonotope.compactKeep C.E C.G).card ≤ C.h
  calc (PolyZonotope.compactKeep C.E C.G).card ≤ Fintype.card (Fin C.h) := Finset.card_le_univ _
    _ = C.h := Fintype.card_fin C.h

omit [Module ℝ α] in
theorem ConPolyZono.compact_s_le (C : ConPolyZono α) : (C.compact).s ≤ C.s := by
  show (PolyZonotope.compactKeep C.compactGens.EC
    (ConPolyZono.consCol C.compactGens.A)).card ≤ C.s
  calc _ ≤ Fintype.card (Fin C.s) := Finset.card_le_univ _
    _ = C.s := Fintype.card_fin C.s

omit [Module ℝ α] in
theorem ConPolyZono.compact_p_le (C : ConPolyZono α) : (C.compact).p ≤ C.p := by
  show (ConPolyZono.usedFactors C.compactGens.compactCons.E
    C.compactGens.compactCons.EC).card ≤ C.p
  calc _ ≤ Fintype.card (Fin C.p) := Finset.card_le_univ _
    _ = C.p := Fintype.card_fin C.p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
