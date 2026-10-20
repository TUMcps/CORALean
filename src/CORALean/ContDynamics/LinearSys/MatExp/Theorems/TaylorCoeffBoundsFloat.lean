module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.TaylorCoeffBoundsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.InvFactorialBoundsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowDownFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowUpFloat

@[expose] public section

/-!
# `MatExp.taylorCoeffBounds` encloses `r ^ k / k!`

Each end is a product of two one-sided bounds of nonnegative quantities: the
power (`powDown_le`/`le_powUp`) and the reciprocal factorial
(`invFactorialBounds_mem`), multiplied and then rounded the same way.

## Inputs
* `r` – float step length
* `k` – order index

## Hypotheses
* `hr` – step length nonnegative

## Conclusion
* the float interval encloses the Taylor coefficient
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.taylorCoeffBounds_mem {r : 𝕋} (hr : 0 ≤ toReal r) (k : ℕ) :
    toReal (MatExp.taylorCoeffBounds r k).inf ≤ toReal r ^ k / (Nat.factorial k : ℝ)
      ∧ toReal r ^ k / (Nat.factorial k : ℝ)
        ≤ toReal (MatExp.taylorCoeffBounds r k).sup := by -- --- PROOF ---
  obtain ⟨hlo, hhi⟩ := MatExp.invFactorialBounds_mem (𝕋 := 𝕋) k
  have hpk : 0 ≤ toReal r ^ k := pow_nonneg hr k
  have hinv : (0 : ℝ) ≤ (Nat.factorial k : ℝ)⁻¹ := by positivity
  rw [div_eq_mul_inv]
  constructor
  · -- the clamped reciprocal is in `[0, 1/k!]`, so the lower power may be compared first
    set y := maximum zero (MatExp.invFactorialBounds (𝕋 := 𝕋) k).inf
    have hy0 : 0 ≤ toReal y := by rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
    have hy1 : toReal y ≤ (Nat.factorial k : ℝ)⁻¹ := by
      rw [toReal_maximum, toReal_zero]; exact max_le hinv hlo
    exact le_trans (mulDown_le_mul _ _) (le_trans
      (mul_le_mul_of_nonneg_right (MatExp.powDown_le hr k) hy0)
      (mul_le_mul_of_nonneg_left hy1 hpk))
  · have hup := MatExp.le_powUp hr k
    exact le_trans (mul_le_mul_of_nonneg_right hup hinv) (le_trans
      (mul_le_mul_of_nonneg_left hhi (le_trans hpk hup)) (mul_le_mulUp _ _))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
