module

public import CORALean.ContSet.Interval.Float.Operations.IntervalMatrix
public import CORALean.ContSet.Interval.Float.Theorems.CenterMemCenterBoxMat
public import CORALean.ContSet.Interval.Float.Theorems.RadiusMatGe
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# `Interval.intervalMatrix` contains the box it is rebuilt from

The bounds are the center minus the radius and the center plus the radius, and the center is
bracketed and the radius rounded up, so the rounded rebuild contains every matrix of the box.

## Inputs
* `I` – interval matrix

## Hypotheses
* none

## Conclusion
* every matrix of the box lies in the rebuilt box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.intervalMatrix_outer (I : Interval (Mat 𝕋 m n)) : -- --- CONCL ---
    I.construct ⊆ I.intervalMatrix.construct := by -- --- PROOF ---
  intro A hA
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have hc := Interval.mem_mat_iff.mp (Interval.center_mem_centerBoxMat I) i j
  have hr := Interval.radiusMat_ge I i j
  have hA' := Interval.mem_mat_iff.mp hA i j
  -- the real center and radius of the stored bounds
  have hrad : I.nominal.radius i j = (toReal (I.sup i j) - toReal (I.inf i j)) / 2 := by
    show (2:ℝ)⁻¹ * (toReal (I.sup i j) - toReal (I.inf i j)) = _
    ring
  have hcen : I.nominal.center i j = (toReal (I.inf i j) + toReal (I.sup i j)) / 2 := by
    show (2:ℝ)⁻¹ * (toReal (I.inf i j) + toReal (I.sup i j)) = _
    ring
  rw [hrad] at hr
  rw [hcen] at hc
  exact ⟨le_trans (subDown_le_sub _ _) (by linarith [hA'.1, hc.1]),
    le_trans (by linarith [hA'.2, hc.2]) (add_le_addUp _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
