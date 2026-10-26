module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanTimesFloatSound

@[expose] public section

/-!
# `times` of a sound float tree and a number is sound

The node `times` of a sound float tree and a number second is sound: its interval encloses the `*`
of the operand and the number's point interval, and `funHanTimesFloat_sound` gives the `funHan`.

## Inputs
* `c` – number

## Hypotheses
* `h` – the operand tree is sound

## Conclusion
* the `times` tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
    {n : ℕ} {B : Float.Interval (Vec 𝕋 n)} {t : Float.SyntaxTree 𝕋 n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `times` node of a sound float tree and a number is sound. -/
theorem SyntaxTree.sound_timesNumRightFloat (c : 𝕋) (h : SyntaxTree.IsSoundFloat B t) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.timesNumRightFloat t c) :=
  ⟨h, fun x hx => SyntaxTree.contains_timesFloat (SyntaxTree.encloses_of_soundFloat h x hx)
    SyntaxTree.contains_intervalFloat, SyntaxTree.funHanTimesFloat_sound _ _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
