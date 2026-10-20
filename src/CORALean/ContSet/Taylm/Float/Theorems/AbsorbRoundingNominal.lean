module

public import CORALean.ContSet.Taylm.Float.Operations.Basic

@[expose] public section

/-!
# `Taylm.absorbRounding` puts the error box into the remainder

The stored remainder of the result is the sum of the remainder and the box, each end rounded
outward, so whatever the remainder and the box held together the result's remainder alone holds:
its nominal model, the remainder without a box, encloses what the input encloses. A product, whose
cross terms multiply the remainders, starts from this (`Taylm.times`).

## Inputs
* `T` – Taylor model
* `f` – enclosed function

## Hypotheses
* `h` – the model encloses the function

## Conclusion
* the nominal part of the absorbed model encloses it too
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The model with its box absorbed encloses, by its remainder alone, what the model encloses. -/
theorem Taylm.absorbRounding_nominal {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.absorbRounding.nominal.Encloses f := by -- --- PROOF ---
  intro t ht
  have a := h t ht
  have h₁ := addDown_le_add T.rem.inf T.I_error.inf
  have h₂ := add_le_addUp T.rem.sup T.I_error.sup
  simp only [Taylm.absorbRounding, Taylm.nominal, Taylm.inflated, Real.Taylm.poly] at a ⊢
  constructor <;> linarith [a.1, a.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
