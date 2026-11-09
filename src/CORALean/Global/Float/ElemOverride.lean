module

public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

@[expose] public section

/-!
# The elementary functions a format computes itself are the real ones

A format may compute `sin`, `cos`, `exp`, `log`, `tan` and `atan` itself (`elemOverride`), as it
may the square root; the round-to-nearest bench baseline supplies the machine's. The law
`SoundFloatArithmetic.elemOverride_exact` is stated for an arbitrary reference `R : RealElem`,
six functions `ℝ → ℝ` as data, since the interface layer may not name `Real.sin` (its import
guards). This file reads it at Mathlib's functions, which `sinDown_le` and its siblings spend in
their override case.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* every elementary function a format supplies computes the real one exactly
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A format that supplies the functions supplies the real ones, exactly. -/
theorem SoundFloatArithmetic.elemOverride_std :
    ∀ e ∈ FloatOps.elemOverride (𝕋 := 𝕋), ElemOverride.IsExact SoundFloatArithmetic.toReal e
      ⟨Real.sin, Real.cos, Real.exp, Real.log, Real.tan, Real.arctan⟩ :=
  fun _ he => SoundFloatArithmetic.elemOverride_exact he _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
