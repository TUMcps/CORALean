module

public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.splitAt`

Bisect one coordinate at its midpoint: the first half keeps `inf`, its `sup`
lowered to the midpoint at coordinate `j`; the second is the mirror image,
`inf` raised to the same midpoint, `sup` kept. Every other coordinate is
untouched in both halves. `Theorems/SplitAtCover` is the fact that makes this
a splitter — the two halves cover `I`, overlapping exactly at the midpoint.

Which coordinate to bisect is a heuristic this owes no proof to:
`NeuralNetwork.holds_of_split` is sound for any choice of `j`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι] [DecidableEq ι]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Bisect coordinate `j` at the midpoint, `inf` kept in the first half and
`sup` kept in the second. -/
noncomputable def Interval.splitAt (I : Interval α) (j : ι) : Interval α × Interval α :=
  (⟨I.inf, ofEntry (Function.update (entry I.sup) j (entry I.center j))⟩,
   ⟨ofEntry (Function.update (entry I.inf) j (entry I.center j)), I.sup⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
