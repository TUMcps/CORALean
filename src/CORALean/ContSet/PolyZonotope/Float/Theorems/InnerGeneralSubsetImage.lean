module

public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerGeneral
public import CORALean.ContSet.PolyZonotope.Float.Theorems.InnerTestSubsetImage

@[expose] public section

/-!
# `innerGeneral` proves an inner box

Both passes of `innerGeneral`, the preconditioned one and the one with `C = eye(n)`, are `innerTest`
at the columns `step_innerColumns` picked, so `innerTest_subset_image` is the guarantee of either;
where no columns are found the answer is `false`.

## Inputs
* `pZ` – polynomial zonotope
* `X` – factor box
* `X₀` – inner factor box
* `Y` – target box
* `inv` – matrix inverse routine
* `iter` – number of iterations

## Hypotheses
* `hT` – the test returns true

## Conclusion
* the target box lies in the image of the factor box
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.innerGeneral_subset_image (pZ : PolyZonotope (Vec 𝕋 n))
    (X X₀ : Interval (Vec 𝕋 pZ.p)) (Y : Interval (Vec 𝕋 n))
    (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k) (iter : ℕ)
    (hT : PolyZonotope.innerGeneral pZ X X₀ Y inv iter = true) : -- --- CONCL ---
    Y.construct ⊆ (PolyZonotope.nominal pZ).point '' X.construct := by -- --- PROOF ---
  unfold PolyZonotope.innerGeneral at hT
  split at hT
  · cases hT
  · -- either pass of the test
    rcases Bool.or_eq_true_iff.mp hT with h | h
    · exact PolyZonotope.innerTest_subset_image pZ X X₀ Y _ _ _ iter h
    · exact PolyZonotope.innerTest_subset_image pZ X X₀ Y _ _ _ iter h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
