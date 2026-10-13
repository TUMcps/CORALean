module

public import CORALean.ContSet.Zonotope.Real.Theorems.RankEqFinrankIff
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Lemmas

@[expose] public section

/-!
# `Zonotope.rank_eq_iff`

`Zonotope.rank_eq_finrank_iff` at `Vec ℝ n`, whose dimension is `n`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
