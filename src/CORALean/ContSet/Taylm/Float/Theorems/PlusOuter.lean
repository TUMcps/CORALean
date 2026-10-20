module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfAppend
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil

@[expose] public section

/-!
# `Taylm.plus` encloses the sum

## Inputs
* `T₁` – first model
* `T₂` – second model
* `f` – first function
* `g` – second function

## Hypotheses
* `h₁` – the first model encloses its function
* `h₂` – the second model encloses its function

## Conclusion
* the sum model encloses the sum of the functions
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.plus_outer {T₁ T₂ : Taylm 𝕋 n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g) : (T₁.plus T₂).Encloses fun t => f t + g t := by -- --- PROOF ---
  intro t ht
  have a₁ := h₁ t ht
  have a₂ := h₂ t ht
  have := addDown_le_add T₁.rem.inf T₂.rem.inf
  have := add_le_addUp T₁.rem.sup T₂.rem.sup
  have := addDown_le_add T₁.I_error.inf T₂.I_error.inf
  have := add_le_addUp T₁.I_error.sup T₂.I_error.sup
  simp only [Taylm.plus, Taylm.inflated, Real.Taylm.poly, List.map_append,
    Real.Taylm.polyOf_append] at *
  constructor <;> linarith [a₁.1, a₁.2, a₂.1, a₂.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
