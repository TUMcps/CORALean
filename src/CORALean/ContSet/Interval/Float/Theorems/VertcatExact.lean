module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.VertcatExact

@[expose] public section

/-!
# `Interval.vertcat` over floats is exact

Stacking commutes with reading the floats as reals, so the stored box denotes the exact layer's
stack of the readings.

## Inputs
* `I` – top interval matrix
* `J` – bottom interval matrix

## Hypotheses
* none

## Conclusion
* the stacked box is exactly the set of stacked pairs
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m₁ m₂ n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.vertcat_exact (I : Interval (Mat 𝕋 m₁ n)) (J : Interval (Mat 𝕋 m₂ n)) :
    (I.vertcat J).construct = (fun p : Mat ℝ m₁ n × Mat ℝ m₂ n => Fin.append p.1 p.2) ''
      (I.construct ×ˢ J.construct) := by -- --- PROOF ---
  have h : (I.vertcat J).nominal = Real.Interval.vertcat I.nominal J.nominal := by
    unfold Interval.nominal Interval.vertcat Real.Interval.vertcat
    congr 1 <;> funext k j <;> refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
      simp [RealImage.realImage, toRealMat]
  show (I.vertcat J).nominal.construct = _
  rw [h]
  exact Real.Interval.vertcat_exact I.nominal J.nominal

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
