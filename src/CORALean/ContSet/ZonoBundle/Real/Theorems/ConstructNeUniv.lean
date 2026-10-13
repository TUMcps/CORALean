import CORALean.ContSet.ZonoBundle.Real.Theorems.IsBounded
import Mathlib.Analysis.Normed.Module.Basic

/-!
# A bundle is not the whole space

`representsa_(zB, 'fullspace')` is `false` when there is a coordinate: a bundle with a member is
bounded.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.construct_ne_univ (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k)
    (hn : 0 < n) : zB.construct ≠ Set.univ := by -- --- PROOF ---
  intro h
  have hb := ZonoBundle.isBounded_construct (zB := zB) hk
  rw [h] at hb
  -- with a coordinate the space has two distinct points
  haveI : Nontrivial (Vec ℝ n) := ⟨⟨0, fun _ => 1, fun h0 => by
    have := congrFun h0 ⟨0, hn⟩
    simp at this⟩⟩
  exact (NormedSpace.unbounded_univ ℝ (Vec ℝ n)) hb


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
