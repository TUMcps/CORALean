module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

/-!
# The derivative of the shape matrix in the parameter

[1, Eq. 15]: for `Q(β) = (1 + 1/β) Q₁ + (1 + β) Q₂` and `R = Q₁⁻¹ Q₂`,
`∂Q/∂β = −(1/β²) Q₁ (I − β² R)`: the derivative of `Q₁/β + β Q₂` is `−Q₁/β² + Q₂`, and
`Q₁ R = Q₂`. Stated entrywise, since a matrix is a function of its entries.

## Inputs
* `Q₁` – first shape matrix
* `Q₂` – second shape matrix
* `β` – weight of the shape sum
* `i` – row
* `j` – column

## Hypotheses
* `h₁` – `Q₁` positive definite
* `hβ` – `0 < β`

## Conclusion
* entry `(i, j)` of `Q(β)` has the derivative of `−(1/β²) Q₁ (I − β² R)`

## References

* [1] [A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of Minkowski
      sum of ellipsoids". 2018 IEEE Conference on Decision and Control (CDC),
      2018.](../../../../../../references/2018/halder-cdc-minkowski-sum-ellipsoids.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 15]: every entry of `Q(β)` has derivative that of `−(1/β²) Q₁ (I − β² R)`. -/
theorem Ellipsoid.halder_deriv_shape {Q₁ Q₂ : Matrix n n ℝ} (h₁ : Q₁.PosDef) {β : ℝ}
    (hβ : 0 < β) (i j : n) : -- --- CONCL ---
    HasDerivAt (fun b : ℝ => (((1 + 1 / b) • Q₁ + (1 + b) • Q₂) i j))
      ((-(1 / β ^ 2) • (Q₁ * (1 - β ^ 2 • (Q₁⁻¹ * Q₂))) : Matrix n n ℝ) i j)
      β := by -- --- PROOF ---
  have hQ : Q₁ * (Q₁⁻¹ * Q₂) = Q₂ := by
    rw [← mul_assoc, mul_nonsing_inv Q₁ ((isUnit_iff_isUnit_det Q₁).1 h₁.isUnit), one_mul]
  -- the right side is `−Q₁/β² + Q₂` entrywise
  have hrhs : (-(1 / β ^ 2) • (Q₁ * (1 - β ^ 2 • (Q₁⁻¹ * Q₂))) : Matrix n n ℝ) i j
      = -(1 / β ^ 2) * Q₁ i j + Q₂ i j := by
    rw [mul_sub, mul_one, mul_smul_comm, hQ]
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    field_simp
    ring
  rw [hrhs]
  have h := (((hasDerivAt_inv hβ.ne').const_add 1).mul_const (Q₁ i j)).add
    (((hasDerivAt_id β).const_add 1).mul_const (Q₂ i j))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp
  · filter_upwards with b
    simp [one_div]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
