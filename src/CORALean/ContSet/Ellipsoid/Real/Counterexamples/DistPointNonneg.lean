module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Shape
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

## References

* [1] A. A. Kurzhanskiy and P. Varaiya. "Ellipsoidal Toolbox (ET)". In Proc. of the 45th
      IEEE Conference on Decision and Control (CDC), pp. 1498-1503, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.dist_point_nonneg_counterexample :
    ∃ (E : Ellipsoid 1) (a l : Vec ℝ 1), a ∈ E.construct ∧ ‖l‖₂ = 1 ∧
      l ⬝ᵥ a - l ⬝ᵥ E.c - √(l ⬝ᵥ (E.shape *ᵥ l)) = 0 := by -- --- PROOF ---
  have hsh : (⟨1, 0, !![1]⟩ : Ellipsoid 1).shape = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Ellipsoid.shape, Matrix.mul_apply]
  refine ⟨⟨1, 0, !![1]⟩, ![1], ![1], ⟨![1], by simp [norm₂], ?_⟩, by simp [norm₂], ?_⟩
  · funext i
    fin_cases i
    simp
  · rw [hsh, Matrix.one_mulVec]
    simp [dotProduct]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
