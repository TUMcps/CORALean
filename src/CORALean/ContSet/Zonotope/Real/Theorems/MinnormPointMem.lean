import CORALean.ContSet.Zonotope.Real.Theorems.MinnormPointDist
import CORALean.ContSet.Zonotope.Real.Theorems.MinnormBallSubset

/-!
# `minnormPoint` lies in the zonotope

The point lies in the ball of radius `minnorm Z` about the centre (`minnormPoint_dist`), which is
inside the zonotope (`minnorm_ball_subset`).

Source: [1].

## References

* [1] `contSet/@zonotope/minnorm.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minnormPoint_mem (Z : Zonotope (Vec ℝ (n + 1)))
    (hspan : Submodule.span ℝ (Set.range Z.G) = ⊤) (S : Fin n → Fin Z.h)
    (hC : Z.facetNormal S ≠ 0) (hoff : Z.minnormOffset S = Z.minnorm) :
    Z.minnormPoint S ∈ Z.construct := by
  have := Zonotope.minnorm_ball_subset Z hspan (Z.minnormPoint S - Z.c)
    (le_of_eq (Zonotope.minnormPoint_dist Z S hC hoff))
  rwa [add_sub_cancel] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
