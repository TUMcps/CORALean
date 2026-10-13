import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# A per-coordinate bound on `absBound` is a bound on the whole zonotope

The direction `mtimesIntervalMat_subset_closedBall` already proves at one
operation: `absBound` bounded by `r` in every coordinate puts the whole
zonotope inside the sup-norm ball of that radius, `Vec ℝ n`'s norm being the
supremum one. What is new here is stating it for the zonotope alone, with no
operation attached, so it composes with any bound on `absBound` rather than
only the one that proof derives.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A zonotope reaches no further than `r`, in the sup norm, once every
coordinate's `absBound` stays under `r`. -/
theorem Zonotope.subset_closedBall_of_absBound_le {Z : Zonotope (Vec ℝ n)} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ j, Z.absBound j ≤ r) :
    Z.construct ⊆ Metric.closedBall (0 : Vec ℝ n) r := by -- --- PROOF ---
  intro x hx
  obtain ⟨β, hβ, hxeq⟩ := Zonotope.mem_construct_iff.mp hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr]
  intro j
  rw [Real.norm_eq_abs]
  exact (Zonotope.abs_le_absBound hβ hxeq j).trans (h j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
