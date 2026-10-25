module

public import CORALean.ContSet.HPolytope.Real.Operations.ChordHighIndex

@[expose] public section

/-!
# `HPolytope.chordHigh`

`[1, Eq. 1]`: `t̄ = min_{i : tᵢ > 0} tᵢ`, the upper end of the Boundary Oracle's segment
`[t̲, t̄]`; `none` for a ray that never leaves.

## Inputs
* `P` – H-polytope
* `x` – point
* `d` – direction

## Output
* the upper end `t̄` of the chord through `x` along `d`, as in [1, Eq. 1]

## References

* [1] B. T. Polyak and E. N. Gryazina. "Billiard walk - a new sampling algorithm for control and
      optimization". IFAC Proceedings Volumes, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `t̄` of `[1, Eq. 1]`. -/
noncomputable def HPolytope.chordHigh (P : HPolytope α) (x d : α) : Option ℝ :=
  (P.chordHighIndex x d).map (P.hitTime x d)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
