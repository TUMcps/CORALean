import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorExactFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylorTailFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalWFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorTwo
import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
import CORALean.ContSet.Interval.Float.Theorems.MemPoint
import CORALean.ContSet.Interval.Float.Theorems.SmulOuter

/-!
# `expIntervalTaylorExact` encloses the truncation of every member, over a float

The float counterpart of `Real.MatExp.expTaylor_mem_expIntervalTaylorExact`: the truncation
splits at order three into `expTaylor (t • M) 2`, which `expTaylor_two` turns into `I + W(t)`,
and the orders past it. `2 ≤ κ` is what makes the split legitimate.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expTaylor_mem_expIntervalTaylorExact (A : Interval (Mat 𝕋 n n)) (t : 𝕋)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) {κ : ℕ} (hκ : 2 ≤ κ) :
    Real.MatExp.expTaylor (toReal t • M) κ
      ∈ (MatExp.expIntervalTaylorExact A t κ).construct := by -- --- PROOF ---
  -- the truncation splits at order three, which is where the exact part stops
  have hsplit : Real.MatExp.expTaylor (toReal t • M) κ
      = Real.MatExp.expTaylor (toReal t • M) 2
        + ∑ i ∈ Finset.Ico 3 (κ + 1), ((Nat.factorial i : ℝ)⁻¹) • (toReal t • M) ^ i := by
    rw [Real.MatExp.expTaylor, Real.MatExp.expTaylor, Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (by omega) (by omega)).symm
  rw [hsplit, Real.MatExp.expTaylor_two]
  simp only [MatExp.expIntervalTaylorExact, Interval.materialiseMat_eq]
  -- the identity is `M ^ 0`, which `matPow` holds as the stored identity block
  have hI : (1 : Mat ℝ n n) ∈ (Interval.matPow A 0).construct := by
    simpa using Interval.matPow_outer A hM 0
  exact Interval.matPlus_outer _ _
    (Interval.matPlus_outer _ _ (by simpa [Interval.matPow] using hI)
      (MatExp.expW_mem_expIntervalW A t hM))
    (MatExp.taylorTail_mem_expIntervalTaylorTail _
      (Interval.smul_outer (le_refl _) (le_refl _) A hM) κ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
