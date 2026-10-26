module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanMinusFloatSound

@[expose] public section

/-!
# `minus` of a number and a sound float tree is sound

The node `minus` of a number first and a sound float tree is sound: its interval encloses the `-` of
the number's point interval and the operand, and `funHanMinusFloat_sound` gives the `funHan`.

## Inputs
* `c` – number

## Hypotheses
* `h` – the operand tree is sound

## Conclusion
* the `minus` tree is sound
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

/-- The `minus` node of a number and a sound float tree is sound. -/
theorem SyntaxTree.sound_minusNumLeftFloat (c : 𝕋) (h : SyntaxTree.IsSoundFloat B t) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.minusNumLeftFloat c t) :=
  ⟨h, fun x hx => SyntaxTree.contains_minusFloat SyntaxTree.contains_intervalFloat
    (SyntaxTree.encloses_of_soundFloat h x hx), SyntaxTree.funHanMinusFloat_sound _ _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
