module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import CORALean.Global.Tensor

@[expose] public section

/-!
# A generator of the wrong horizontal direction cannot come first

In the upper half-plane `y > 0 ∨ (y = 0 ∧ x ≥ 0)`, a vector `u` pointing against `σ` (`σ u₀ < 0`)
and one `w` pointing along it (`σ w₀ > 0`) have `σ cross(u, w) < 0`. So in an order with
`σ cross(u, w) ≥ 0` for `u` before `w`, the generators before a right-pointing one are not
left-pointing: the chain of [1, Alg. 3] and [1, Alg. 4] from the lowest vertex moves monotonically
in `x`.

## Inputs
* `σ` – direction sign
* `u` – first planar vector
* `w` – second planar vector

## Hypotheses
* `hσ` – `σ` is plus or minus one
* `hu` – `u` points upward
* `hw` – `w` points upward
* `hwx` – `w` points along `σ`
* `hux` – `u` points against `σ`

## Conclusion
* the signed cross product is negative

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cross_neg_of_horizontal {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {u w : Vec ℝ 2}
    (hu : 0 ≤ u 1 ∧ (0 < u 1 ∨ 0 ≤ u 0)) (hw : 0 ≤ w 1 ∧ (0 < w 1 ∨ 0 ≤ w 0))
    (hwx : 0 < σ * w 0) (hux : σ * u 0 < 0) : σ * (u 0 * w 1 - u 1 * w 0) < 0 := by -- --- PROOF ---
  rcases hσ with rfl | rfl
  · simp only [one_mul] at *
    have hu1 : 0 < u 1 := hu.2.resolve_right (not_le.mpr hux)
    nlinarith [mul_nonneg (neg_nonneg.mpr hux.le) hw.1, mul_pos hu1 hwx]
  · have hw1 : 0 < w 1 := hw.2.resolve_right (by linarith)
    nlinarith [mul_pos (show 0 < u 0 by linarith) hw1, mul_nonneg hu.1 (show 0 ≤ -w 0 by linarith)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
