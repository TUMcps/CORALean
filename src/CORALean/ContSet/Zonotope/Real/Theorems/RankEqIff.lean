import CORALean.ContSet.Zonotope.Real.Theorems.RankEqFinrankIff
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas

/-!
# `Zonotope.rank_eq_iff`

`Zonotope.rank_eq_finrank_iff` at `Vec ℝ n`, whose dimension is `n`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.rank_eq_iff (Z : Zonotope (Vec ℝ n)) :
    Z.rank = n ↔ (interior Z.construct).Nonempty := by
  rw [← Zonotope.rank_eq_finrank_iff]
  simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
