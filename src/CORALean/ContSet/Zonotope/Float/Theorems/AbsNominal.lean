module

public import CORALean.ContSet.Zonotope.Float.Operations.Abs
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsCornerMem

@[expose] public section

/-!
# `Zonotope.abs` is exact on the nominal part

Absolute value rounds nothing, so the nominal part of the float `abs` is the real `abs` of the
nominal part of the input.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* nominal part of the absolute zonotope is the absolute of the nominal part
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `abs` is exact on the nominal part. -/
theorem Zonotope.abs_nominal (Z : Zonotope (Vec 𝕋 n)) :
    nominal Z.abs = CORALean.Real.Zonotope.abs (nominal Z) := by -- --- PROOF ---
  show (⟨Z.h, toRealVec fun i => absolute (Z.c i), fun j i => toReal (absolute (Z.G j i))⟩ :
      CORALean.Real.Zonotope (Vec ℝ n)) = _
  have hc : toRealVec (fun i => absolute (Z.c i)) = fun i => |toReal (Z.c i)| :=
    funext fun i => toReal_absolute _
  simp only [CORALean.Real.Zonotope.abs, toReal_absolute]
  rw [hc]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
