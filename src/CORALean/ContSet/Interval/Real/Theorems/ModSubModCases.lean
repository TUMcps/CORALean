module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# Bounds reduced modulo a period differ by the width, or by the width less a period

[1, Prop. 1]: for `x̅ - x̲ < 2π`, the reduced bounds `y = mod(x, 2π)` of [1, Eq. 11] satisfy
`x̅ - x̲ = y̅ - y̲` (case 1) or `x̅ - x̲ = (y̅ - y̲) + 2π` (case 2). Stated for any period `p > 0`,
since the tangent and cotangent of [1, Eq. 14] reduce modulo `π`, and with which case is which:
case 1 exactly when `y̲ ≤ y̅`, which is the test [1] says suffices. `mod(x, p)` is MATLAB's,
`x - p⌊x/p⌋`.

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1], with the case split by `y̲ ≤ y̅`. -/
theorem Interval.mod_sub_mod_cases {p lo hi : ℝ} (hp : 0 < p) (hle : lo ≤ hi)
    (hw : hi - lo < p) : -- --- STMT ---
    (lo - p * ⌊lo / p⌋ ≤ hi - p * ⌊hi / p⌋ ∧
        hi - lo = (hi - p * ⌊hi / p⌋) - (lo - p * ⌊lo / p⌋)) ∨
      (hi - p * ⌊hi / p⌋ < lo - p * ⌊lo / p⌋ ∧
        hi - lo = (hi - p * ⌊hi / p⌋) - (lo - p * ⌊lo / p⌋) + p) := by -- --- PROOF ---
  -- the two floors differ by `0` or `1`
  have h1 : ⌊lo / p⌋ ≤ ⌊hi / p⌋ := Int.floor_le_floor (div_le_div_of_nonneg_right hle hp.le)
  have h2 : ⌊hi / p⌋ ≤ ⌊lo / p⌋ + 1 := by
    have : hi / p < lo / p + 1 := by
      rw [div_add_one hp.ne', div_lt_div_iff_of_pos_right hp]; linarith
    have := Int.floor_le_floor this.le
    rwa [Int.floor_add_one] at this
  -- both reduced bounds lie in `[0, p)`
  have hl1 : (⌊lo / p⌋ : ℝ) ≤ lo / p := Int.floor_le _
  have hl2 : lo / p < ⌊lo / p⌋ + 1 := Int.lt_floor_add_one _
  have hh1 : (⌊hi / p⌋ : ℝ) ≤ hi / p := Int.floor_le _
  have hh2 : hi / p < ⌊hi / p⌋ + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hp] at hl1 hh1
  rw [div_lt_iff₀ hp] at hl2 hh2
  rcases (show ⌊hi / p⌋ = ⌊lo / p⌋ ∨ ⌊hi / p⌋ = ⌊lo / p⌋ + 1 by omega) with h | h
  · -- the same period: case 1
    left
    rw [h]
    exact ⟨by linarith, by ring⟩
  · -- the next period: case 2
    right
    rw [h]
    push_cast
    constructor
    · nlinarith
    · ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
