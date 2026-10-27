module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstructIff
public import CORALean.Global.EuclideanNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `[1, Sec. II (sign of the distance)]`: zero, not negative, on the boundary

"The distance is negative if the point is inside the ellipsoid, or the two ellipsoids and the
ellipsoid and hyperplane have a non-empty intersection." For the unit interval `E(0, 1) ⊂ ℝ` the
boundary point `1` is in `E`, yet the point formula is `0` along `l = 1`, and no direction makes
it positive (`dist_point_eq_max`), so its maximum is `0`. Touching sets give `0` the same way.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a boundary point has distance zero, not negative

## References

* [1] [A. A. Kurzhanskiy and P. Varaiya. "Ellipsoidal Toolbox (ET)". Proceedings of the 45th IEEE
      Conference on Decision and Control,
      2006.](../../../../../../references/2006/kurzhanskiy-cdc-ellipsoidal-toolbox.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix
open scoped MatrixOrder


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.dist_point_nonneg_counterexample : -- --- CONCL ---
    ∃ (E : Ellipsoid 1) (a l : Vec ℝ 1), a ∈ E.construct ∧ ‖l‖₂ = 1 ∧
      l ⬝ᵥ a - l ⬝ᵥ E.q - √(l ⬝ᵥ (E.Q *ᵥ l)) = 0 := by -- --- PROOF ---
  have hG : (⟨1, 0, .one⟩ : Ellipsoid 1).G = 1 := CFC.sqrt_one
  refine ⟨⟨1, 0, .one⟩, ![1], ![1], Ellipsoid.mem_construct_iff.2 ⟨![1], by simp [norm₂], ?_⟩,
    by simp [norm₂], ?_⟩
  · rw [hG, Matrix.one_mulVec, zero_add]
  · show _ - _ - √(_ ⬝ᵥ ((1 : Mat ℝ 1 1) *ᵥ _)) = 0
    rw [Matrix.one_mulVec]
    simp [dotProduct]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
