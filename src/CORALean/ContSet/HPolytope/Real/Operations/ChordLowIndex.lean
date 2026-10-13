module

public import CORALean.ContSet.HPolytope.Real.Operations.HitTime

@[expose] public section

/-!
# `HPolytope.chordLowIndex`

`[1, Eq. 1]`: the row attaining `t̲ = max_{i : tᵢ < 0} tᵢ`, the first hyperplane the line
meets going backward; `none` when no `tᵢ` is negative.

## References

* [1] B. T. Polyak and E. N. Gryazina. "Billiard walk - a new sampling algorithm for control
      and optimization". In Proc. of the 19th IFAC World Congress, Cape Town, South Africa,
      IFAC Proceedings Volumes 47(3), pp. 6123-6128, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The index of `t̲` in `[1, Eq. 1]`. -/
noncomputable def HPolytope.chordLowIndex (P : HPolytope α) (x d : α) : Option (Fin P.m) :=
  List.argmax (P.hitTime x d) ((List.finRange P.m).filter fun i => decide (P.hitTime x d i < 0))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
