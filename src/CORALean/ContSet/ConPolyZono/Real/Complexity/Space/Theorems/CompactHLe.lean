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
/-- An upper bound on the `h` count of `compact`'s result. -/
theorem ConPolyZono.compact_h_le (cPZ : ConPolyZono α) : (cPZ.compact).h ≤ cPZ.h := by
  show (PolyZonotope.compactKeep cPZ.E cPZ.G).card ≤ cPZ.h
  calc (PolyZonotope.compactKeep cPZ.E cPZ.G).card
      ≤ Fintype.card (Fin cPZ.h) := Finset.card_le_univ _
    _ = cPZ.h := Fintype.card_fin cPZ.h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
