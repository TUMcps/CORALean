module

public import CORALean.ContSet.Taylm.Float.Theorems.AbsorbRoundingNominal

@[expose] public section

/-!
# `Taylm.absorbRounding` loses nothing

Read back through `Encloses`: `absorbRounding_nominal` puts everything in the remainder, and the
result's box is exactly `[0, 0]`, which adds nothing, so nothing of the absorption step's rounding
is left outside the remainder.

## Inputs
* `T` – Taylor model
* `f` – enclosed function

## Hypotheses
* `h` – the model encloses the function

## Conclusion
* the absorbed model encloses the function
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

/-- `absorbRounding` encloses what the model encloses. -/
theorem Taylm.absorbRounding_outer {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ}
    (h : T.Encloses f) : -- --- CONCL ---
    T.absorbRounding.Encloses f := by -- --- PROOF ---
  intro t ht
  have a := Taylm.absorbRounding_nominal h t ht
  simp only [Taylm.absorbRounding, Taylm.nominal, Taylm.inflated, toReal_zero,
    add_zero] at a ⊢
  exact a

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
