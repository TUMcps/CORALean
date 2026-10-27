module

public import CORALean.ContSet.Interval.Float.Operations.Unvec
public import CORALean.ContSet.Interval.Float.Theorems.VecExact

@[expose] public section

/-!
# `Interval.unvec` is exactly the unstacked set

Unstacking undoes `Interval.vec`, which is exact, so the unstacked box denotes the images of the
stacked members under the inverse of the vectorisation.

## Inputs
* `I` – interval vector of stacked bounds

## Hypotheses
* none

## Conclusion
* the unstacked box denotes exactly the unstackings of the members
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

theorem Interval.unvec_exact (I : Interval (Vec 𝕋 (n * m))) : -- --- CONCL ---
    I.unvec.construct = matVecEquiv.symm '' I.construct := by -- --- PROOF ---
  -- stacking the unstacked box gives the box back
  have h : I.unvec.vec = I := by
    cases I
    simp only [Interval.vec, Interval.unvec, Equiv.apply_symm_apply, Prod.mk.eta]
  -- so its members are the stackings of the unstacked ones
  have h2 := Interval.vec_exact I.unvec
  rw [h] at h2
  rw [h2, Set.image_image]
  simp

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
