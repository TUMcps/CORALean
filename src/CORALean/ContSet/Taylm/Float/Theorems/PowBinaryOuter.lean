module

public import CORALean.ContSet.Taylm.Float.Operations.PowBinary
public import CORALean.ContSet.Taylm.Float.Operations.TimesMerged
public import CORALean.ContSet.Taylm.Float.Theorems.Basic
public import CORALean.ContSet.Taylm.Float.Theorems.TimesMergedOuter

@[expose] public section

/-!
# `Taylm.powBinary` encloses the power

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `k` – exponent

## Hypotheses
* `h` – `T` encloses `f`

## Conclusion
* the power model encloses `fᵏ`
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The loop encloses `g · hᵏ` when its passes reach `k`: an odd `k` moves one factor into the
result, the base squares. -/
private theorem Taylm.aux_loop (N fuel k : ℕ) (hk : k ≤ fuel) {R B : Taylm 𝕋 n}
    {g h : Vec ℝ n → ℝ} (hR : R.Encloses g) (hB : B.Encloses h) : -- --- CONCL ---
    (Taylm.step_powBinary N fuel R B k).Encloses fun t => g t * h t ^ k := by -- --- PROOF ---
  induction fuel generalizing k R B g h with
  | zero =>
    obtain rfl : k = 0 := by omega
    simpa [Taylm.step_powBinary] using hR
  | succ fuel ih =>
  rw [Taylm.step_powBinary]
  by_cases hk0 : k = 0
  · subst hk0
    simpa using hR
  rw [if_neg hk0]
  have hle : k / 2 ≤ fuel := by omega
  by_cases hodd : k % 2 = 1
  · -- an odd exponent: the result takes the base
    have hR' := Taylm.timesMerged_outer N hR hB
    by_cases h₁ : 1 < k
    · have := ih (k / 2) hle hR' (Taylm.timesMerged_outer N hB hB)
      simp only [hodd, h₁, if_true]
      convert this using 2 with t
      rw [mul_assoc, ← pow_two, ← pow_mul, ← pow_succ', show 2 * (k / 2) + 1 = k by omega]
    · have := ih (k / 2) hle hR' hB
      simp only [hodd, h₁, if_true, if_false]
      convert this using 2 with t
      have : k = 1 := by omega
      subst this
      simp
  · -- an even exponent: only the base is squared
    have h₁ : 1 < k := by omega
    have := ih (k / 2) hle hR (Taylm.timesMerged_outer N hB hB)
    simp only [hodd, h₁, if_true, if_false]
    convert this using 2 with t
    rw [← pow_two, ← pow_mul, show 2 * (k / 2) = k by omega]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.powBinary_outer {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (k : ℕ) : (T.powBinary k).Encloses fun t => f t ^ k := by
  have := Taylm.aux_loop T.maxOrder k k le_rfl (Taylm.const_outer (n := n) one T.maxOrder) h
  simpa [Taylm.powBinary, toReal_one] using this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
