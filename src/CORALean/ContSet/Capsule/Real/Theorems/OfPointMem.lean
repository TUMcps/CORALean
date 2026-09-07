import CORALean.ContSet.Capsule.Real.Operations.OfPoint

/-!
# A direction-free, radius-free capsule contains its own centre

`ofPoint v` states its own `g` and `r`, both `0`, so the segment endpoint at
any `t` collapses to `v` and the ball shrinks to `Real.sqrt 0 ≤ 0`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.mem_ofPoint (v : Vec ℝ n) : v ∈ (Capsule.ofPoint v).construct := by
  refine ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
  simp [Capsule.ofPoint]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
