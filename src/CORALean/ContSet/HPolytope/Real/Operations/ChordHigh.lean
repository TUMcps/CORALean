import CORALean.ContSet.HPolytope.Real.Operations.ChordHighIndex

/-!
# `HPolytope.chordHigh`

`[1, Eq. 1]`: `t̄ = min_{i : tᵢ > 0} tᵢ`, the upper end of the Boundary Oracle's segment
`[t̲, t̄]`; `none` for a ray that never leaves.

## References

* [1] B. T. Polyak and E. N. Gryazina. "Billiard walk - a new sampling algorithm for control
      and optimization". In Proc. of the 19th IFAC World Congress, Cape Town, South Africa,
      IFAC Proceedings Volumes 47(3), pp. 6123-6128, 2014.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `t̄` of `[1, Eq. 1]`. -/
noncomputable def HPolytope.chordHigh (P : HPolytope α) (x d : α) : Option ℝ :=
  (P.chordHighIndex x d).map (P.hitTime x d)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
