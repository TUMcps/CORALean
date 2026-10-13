import CORALean.ContSet.HPolytope.Real.HPolytope
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith

/-!
# A halfspace description is convex

An intersection of halfspaces and hyperplanes, each cut by one linear
functional, so a weighted average satisfies every constraint the two endpoints
do. Holds for any constraints, the infeasible case included.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.convex_construct (P : HPolytope α) : Convex ℝ P.construct := by -- --- PROOF ---
  rintro x ⟨hx, hex⟩ y ⟨hy, hey⟩ a b ha hb hab
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left (hx i) ha
    have h2 := mul_le_mul_of_nonneg_left (hy i) hb
    -- the weights sum to one, so the bound is its own weighted average
    have hb' : a * P.b i + b * P.b i = P.b i := by rw [← add_mul, hab, one_mul]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    linarith
  · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hex i, hey i, ← add_mul, hab,
      one_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
