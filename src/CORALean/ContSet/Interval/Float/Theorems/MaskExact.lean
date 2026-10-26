module

public import CORALean.ContSet.Interval.Float.Operations.Mask
public import CORALean.ContSet.Interval.Real.Theorems.MaskExact

@[expose] public section

/-!
# `Interval.mask` over floats is exact

`zero` reads as `0`, so the stored box denotes the exact layer's masked box of the reading, and
the image statement carries over for a box with no empty entry.

## Inputs
* `keep` – predicate selecting the entries to keep
* `I` – interval matrix

## Hypotheses
* `hI` – `I` has ordered bounds

## Conclusion
* the masked box is exactly the image with unkept entries zeroed
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem Interval.aux_mask_nominal (keep : Fin m → Fin n → Prop)
    [∀ i j, Decidable (keep i j)] (I : Interval (Mat 𝕋 m n)) :
    (I.mask keep).nominal = Real.Interval.mask keep I.nominal := by
  unfold Interval.nominal Interval.mask Real.Interval.mask
  congr 1 <;> funext i j <;> by_cases h : keep i j <;>
    simp [RealImage.realImage, toRealMat, h, toReal_zero]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mask_exact (keep : Fin m → Fin n → Prop) [∀ i j, Decidable (keep i j)]
    (I : Interval (Mat 𝕋 m n)) (hI : ∀ i j, toReal (I.inf i j) ≤ toReal (I.sup i j)) :
    (I.mask keep).construct = (fun (A : Mat ℝ m n) (i : Fin m) (j : Fin n) =>
      if keep i j then A i j else 0) '' I.construct := by
  show (I.mask keep).nominal.construct = _
  rw [Interval.aux_mask_nominal]
  exact Real.Interval.mask_exact keep I.nominal hI

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
