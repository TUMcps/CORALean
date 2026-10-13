import CORALean.ContSet.Taylm.Real.Operations.BnbLoop
import CORALean.ContSet.Taylm.Real.Operations.PolyBoxBounds
import CORALean.ContSet.Taylm.Real.Operations.ReexpBoxBounds

/-!
# Branch and bound

[1, Alg. 1], `BranchAndBound(P, [x], ε)`: lines 2-5 start from the one box `[x]` bounded by
interval arithmetic, eq. (12), and the loop splits until the union settles. `adv` chooses the
source's two settings: `standard` bounds each sub-box by interval arithmetic directly, `advanced`
re-expands `P` at the sub-box's centre first (lines 15, 22, 28).

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.branchAndBound (P : List (ℝ × (Fin n → ℕ))) (X : Fin n → ℝ × ℝ)
    (ε : ℝ) (adv : Bool) (fuel : ℕ) : ℝ × ℝ :=
  -- 15-16, 22-23, 28-29: a sub-box's bound, re-expanded first in the advanced setting
  let bnd := fun B => if adv then Taylm.reexpBoxBounds P B else Taylm.polyBoxBounds P B
  -- 2-5: one box, `[x]` itself
  Taylm.bnbLoop bnd ε fuel [X]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
