module

public import CORALean.ContSet.HPolytope.Real.Operations.ChordLowIndex

@[expose] public section

/-!
# `HPolytope.chordLow`

`[1, Eq. 1]`: `t̲ = max_{i : tᵢ < 0} tᵢ`, the lower end of the Boundary Oracle's segment
`[t̲, t̄]`; `none` for a ray that never leaves backward.

## Inputs
* `P` – H-polytope
* `x` – point
* `d` – direction

## Output
* `t̲` of `[1, Eq. 1]`

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

/-- `t̲` of `[1, Eq. 1]`. -/
noncomputable def HPolytope.chordLow (P : HPolytope α) (x d : α) : Option ℝ :=
  (P.chordLowIndex x d).map (P.hitTime x d)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
