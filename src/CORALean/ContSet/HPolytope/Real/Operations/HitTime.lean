module

public import CORALean.ContSet.HPolytope.Real.HPolytope

@[expose] public section

/-!
# `HPolytope.hitTime`

`[1, Eq. 1]`: the parameter `tᵢ = (bᵢ - (aᵢ, xₖ)) / (aᵢ, d)` at which the line `xₖ + t d`
meets the hyperplane of the `i`-th inequality. Division is Lean's, so a row parallel to the
line (`(aᵢ, d) = 0`) has `tᵢ = 0`, which neither extreme of the chord ever picks: the paper
leaves the parallel rows out silently.

## References

* [1] B. T. Polyak and E. N. Gryazina. "Billiard walk - a new sampling algorithm for control
      and optimization". In Proc. of the 19th IFAC World Congress, Cape Town, South Africa,
      IFAC Proceedings Volumes 47(3), pp. 6123-6128, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `tᵢ` of `[1, Eq. 1]`, for the row `i` of `P` and the line through `x` along `d`. -/
noncomputable def HPolytope.hitTime (P : HPolytope α) (x d : α) (i : Fin P.m) : ℝ :=
  (P.b i - P.A i x) / P.A i d

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
