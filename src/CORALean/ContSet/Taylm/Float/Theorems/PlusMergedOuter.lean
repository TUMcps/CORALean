module

public import CORALean.ContSet.Taylm.Float.Operations.PlusMerged
public import CORALean.ContSet.Taylm.Float.Theorems.AccumTermsLe

@[expose] public section

/-!
# `Taylm.plusMerged` encloses the sum

## Inputs
* `T₁` – first Taylor model
* `T₂` – second Taylor model
* `f` – function the first encloses
* `g` – function the second encloses

## Hypotheses
* `h₁` – `T₁` encloses `f`
* `h₂` – `T₂` encloses `g`

## Conclusion
* the sum model encloses `f + g`
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.plusMerged_outer {T₁ T₂ : Taylm 𝕋 n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g) : -- --- CONCL ---
    (T₁.plusMerged T₂).Encloses fun t => f t + g t := by -- --- PROOF ---
  intro t ht
  have a₁ := h₁ t ht
  have a₂ := h₂ t ht
  -- the merged terms are the two term lists up to the rounding bound
  have hS := abs_le.1 (Taylm.accumTerms_le T₁.terms T₂.terms ht)
  have := addDown_le_add T₁.rem.inf T₂.rem.inf
  have := add_le_addUp T₁.rem.sup T₂.rem.sup
  have := addDown_le_add T₁.I_error.inf T₂.I_error.inf
  have := add_le_addUp T₁.I_error.sup T₂.I_error.sup
  have := addDown_le_add (addDown T₁.I_error.inf T₂.I_error.inf)
    (neg (Taylm.accumTerms T₁.terms T₂.terms).2)
  have := add_le_addUp (addUp T₁.I_error.sup T₂.I_error.sup)
    (Taylm.accumTerms T₁.terms T₂.terms).2
  simp only [Taylm.plusMerged, Taylm.inflated, Real.Taylm.poly, subDown, toReal_neg] at *
  constructor <;> linarith [a₁.1, a₁.2, a₂.1, a₂.2, hS.1, hS.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
