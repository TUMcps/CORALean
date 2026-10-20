module

public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.ContSet.Interval.Real.Theorems.MtimesIntervalMatOuter
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# `Interval.mtimesIntervalMat` over-approximates every matrix in the box

Nothing about a matrix in a box acting on a box appears here — `Real` has
already proved that. The whole obligation is that each corner and each row sum
rounds the right way, exactly as `MatMulOuter.lean`'s does.

## Inputs
* `IM` – interval matrix
* `I` – box

## Hypotheses
* none

## Conclusion
* every matrix in the box applied to every vector lies in the result
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Interval.aux_mtimesIntervalMat_outer_refines (IM : Interval (Mat 𝕋 m n))
    (I : Interval (Vec 𝕋 n)) :
    (Real.Interval.mtimesIntervalMat IM.nominal I.nominal).construct
      ⊆ (Interval.mtimesIntervalMat IM I).construct := by -- --- PROOF ---
  intro X hX i
  have h := hX i
  simp only [Real.Interval.mtimesIntervalMat, Interval.nominal, RealImage.realImage,
    toRealMat, toRealVec] at h
  constructor
  · show toReal (sumDown fun k =>
        Interval.mulLo (IM.inf i k) (IM.sup i k) (I.inf k) (I.sup k)) ≤ X i
    exact le_trans (sumDown_le_sum _)
      (le_trans (Finset.sum_le_sum fun k _ => Interval.mulLo_le _ _ _ _) h.1)
  · show X i ≤ toReal (sumUp fun k =>
        Interval.mulHi (IM.inf i k) (IM.sup i k) (I.inf k) (I.sup k))
    exact le_trans h.2
      (le_trans (Finset.sum_le_sum fun k _ => Interval.le_mulHi _ _ _ _) (sum_le_sumUp _))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mtimesIntervalMat_outer (IM : Interval (Mat 𝕋 m n)) (I : Interval (Vec 𝕋 n)) :
    (⋃ A ∈ IM.construct, (A *ᵥ ·) '' I.construct) ⊆ (Interval.mtimesIntervalMat IM I).construct :=
  subset_trans (Real.Interval.mtimesIntervalMat_outer IM.nominal I.nominal)
    (Interval.aux_mtimesIntervalMat_outer_refines IM I)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
