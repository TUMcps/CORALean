module

public import CORALean.ContSet.Capsule.Real.Operations.Empty
public import CORALean.ContSet.Capsule.Real.Operations.OfPoint
public import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqEmpty

@[expose] public section

/-!
# `ContSet/Capsule/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ==================================  `Capsule.empty_exact`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- `Capsule.empty` denotes the empty set -/
theorem Capsule.empty_exact (n : ℕ) : (Capsule.empty n).construct = ∅ :=
  Capsule.construct_eq_empty (by simp [Capsule.empty])

end CORALean.Real


-- ==================================  `Capsule.mem_ofPoint`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- `ofPoint v` states its own `g` and `r`, both `0`, so the segment endpoint at
any `t` collapses to `v` and the ball shrinks to `Real.sqrt 0 ≤ 0`. -/
theorem Capsule.mem_ofPoint (v : Vec ℝ n) : v ∈ (Capsule.ofPoint v).construct := by
  refine ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
  simp [Capsule.ofPoint]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
