module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The remainder of `1/x`'s Taylor polynomial in closed form

`1/x - Σₖ₌₀ᴺ (-1)ᵏ (x - c)ᵏ / cᵏ⁺¹ = (-1)ᴺ⁺¹ (x - c)ᴺ⁺¹ / (x cᴺ⁺¹)`: the geometric series' tail,
exactly. The exact remainder of [1, Eq. 34], which [1, Eq. 38] bounds in closed form.

## Inputs
* `c` – center
* `x` – point
* `N` – expansion order

## Hypotheses
* `hc` – the center is nonzero
* `hx` – the point is nonzero

## Conclusion
* the remainder of the reciprocal's Taylor polynomial has a closed form

## References

* [1] [M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.](../../../../../../references/2018/althoff-arch-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.inv_sub_sum_eq {c x : ℝ} (hc : c ≠ 0) (hx : x ≠ 0) (N : ℕ) : -- --- CONCL ---
    x⁻¹ - ∑ k ∈ Finset.range (N + 1), (-1) ^ k * (x - c) ^ k / c ^ (k + 1)
      = (-1) ^ (N + 1) * (x - c) ^ (N + 1) / (x * c ^ (N + 1)) := by -- --- PROOF ---
  induction N with
  | zero => simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, pow_one,
      one_mul]; field_simp; ring
  | succ N ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih]
    field_simp
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
