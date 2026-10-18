module

public import CORALean.ContSet.Ellipsoid.Real.Operations.IntersectStripLiu1D
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# CORA's `intersectStrip` (Liu) does not enclose the intersection

The ellipsoid `[-1, 1]` (`Q = 1`, `c = 0`, `σ²_prev = 1`, so the paper's set
`{x | (x - c)ᵀ Q⁻¹ (x - c) ≤ σ²_prev}` and CORA's ellipsoid object agree) and the measurement
`y = 1/2` with `C = 1` and noise `V = 1` (`barV = chol(inv(V)) = 1`), that is the set
`[-1/2, 3/2]`: the intersection is `[-1/2, 1]`, and the trigger `σ²_prev + δ² > 1` holds. CORA's
update has `g = 1`, `β = 0`, `λ = 1/2`, `Q_tmp = 4`, `K = 1/2`, and returns the center `1/4` and
the shape `1/4`, the interval `[-1/4, 3/4]`, which misses `x = 1`: `(1 - 1/4)² / (1/4) = 9/4`.
The fusion `(1 - λ)(x - c)ᵀ Q⁻¹ (x - c) + λ (y - C x)ᵀ V⁻¹ (y - C x) ≤ (1 - λ) σ²_prev + λ`
completes to the shape `(1 - K C) Q / (1 - λ)` at the level `σ²` (`intersectStripLiu`), where
the code has `(1 - λ)(1 - K C) Q`; here that is `1` at the level `σ² = 15/16`, which contains
`[-1/2, 1]`. CORA's ellipsoid object is the level-`1` set of its shape, and the level-`σ²` set is
inside it (`σ² ≤ 1`), so `x = 1` is missed under either reading.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.intersectStripLiu1D_counterexample : -- --- STMT ---
    1 < (1 : ℝ) + ((1 / 2 : ℝ) - 1 * 0) ^ 2 ∧ ((1 : ℝ) - 0) ^ 2 / 1 ≤ 1 ∧
      ((1 / 2 : ℝ) - 1 * 1) ^ 2 / 1 ≤ 1 ∧
      1 < (1 - (Ellipsoid.intersectStripLiu1D 1 0 1 1 1 (1 / 2) 1).1) ^ 2 /
        (Ellipsoid.intersectStripLiu1D 1 0 1 1 1 (1 / 2) 1).2.1 := by -- --- PROOF ---
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  -- the update in closed form: `λ = 1/2`, center `1/4`, shape `1/4`
  have hc : (Ellipsoid.intersectStripLiu1D 1 0 1 1 1 (1 / 2) 1).1 = 1 / 4 := by
    norm_num [Ellipsoid.intersectStripLiu1D]
  have hq : (Ellipsoid.intersectStripLiu1D 1 0 1 1 1 (1 / 2) 1).2.1 = 1 / 4 := by
    norm_num [Ellipsoid.intersectStripLiu1D]
  rw [hc, hq]
  norm_num

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
