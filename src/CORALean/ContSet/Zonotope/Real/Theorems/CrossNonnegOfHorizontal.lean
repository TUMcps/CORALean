module

public import CORALean.ContSet.Zonotope.Real.Theorems.CrossNegOfHorizontal

@[expose] public section

/-!
# A generator pointing along `σ` has a nonnegative cross product with one that does not

In the upper half-plane, `σ u₀ > 0` and `σ w₀ ≤ 0` give `σ cross(u, w) ≥ 0`: the complement of
`cross_neg_of_horizontal`, with the vertical and zero generators `σ w₀ = 0` included. It is the
side condition for the generators not in the search set `G` of [1, Alg. 4], which lie after every
generator of `G` in the walk.

## Inputs
* `σ` – direction sign
* `u` – first planar vector
* `w` – second planar vector

## Hypotheses
* `hσ` – `σ` is plus or minus one
* `hu` – `u` points upward
* `hw` – `w` points upward
* `hux` – `u` points along `σ`
* `hwx` – `w` does not point along `σ`

## Conclusion
* the signed cross product is nonnegative

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

theorem Zonotope.cross_nonneg_of_horizontal {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {u w : Vec ℝ 2}
    (hu : 0 ≤ u 1 ∧ (0 < u 1 ∨ 0 ≤ u 0)) (hw : 0 ≤ w 1 ∧ (0 < w 1 ∨ 0 ≤ w 0))
    (hux : 0 < σ * u 0) (hwx : σ * w 0 ≤ 0) : -- --- CONCL ---
    0 ≤ σ * (u 0 * w 1 - u 1 * w 0) := by -- --- PROOF ---
  rcases hwx.lt_or_eq with h | h
  · have := Zonotope.cross_neg_of_horizontal hσ hw hu hux h
    nlinarith
  · have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hw0 : w 0 = 0 := (mul_eq_zero.mp h).resolve_left hσne
    rw [hw0]
    nlinarith [mul_nonneg hux.le hw.1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
