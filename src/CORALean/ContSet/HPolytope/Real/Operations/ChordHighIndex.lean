module

public import CORALean.ContSet.HPolytope.Real.Operations.HitTime

@[expose] public section

/-!
# `HPolytope.chordHighIndex`

`[1, Eq. 1]`: the row attaining `t̄ = min_{i : tᵢ > 0} tᵢ`, the first hyperplane the line
meets going forward. `none` when no `tᵢ` is positive, the ray never leaves (an unbounded set,
not the paper's bounded `Q`). The first minimizer is taken; a tie is a corner, which the billiard
walk then discards.

## Inputs
* `P` – H-polytope
* `x` – point
* `d` – direction

## Output
* the index of `t̄` in `[1, Eq. 1]`

## References

* [1] [B. T. Polyak and E. N. Gryazina. "Billiard walk - a new sampling algorithm for control and
      optimization". IFAC Proceedings Volumes,
      2014.](../../../../../../references/2014/polyak-ifac-billiard-walk.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The index of `t̄` in `[1, Eq. 1]`. -/
noncomputable def HPolytope.chordHighIndex (P : HPolytope α) (x d : α) : Option (Fin P.m) :=
  List.argmin (P.hitTime x d) ((List.finRange P.m).filter fun i => decide (0 < P.hitTime x d i))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
