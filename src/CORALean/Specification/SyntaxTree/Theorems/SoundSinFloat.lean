module

public import CORALean.ContSet.Interval.Float.Theorems.SinOuter
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSoundFloat
public import CORALean.Specification.SyntaxTree.Theorems.FunHanSinFloatSound

@[expose] public section

/-!
# `sin` of a sound float tree is sound

The node `sin` builds over a sound float tree is sound: its interval encloses the sine:
`Interval.sin` encloses the sine of the operand and `funHanSinFloat_sound` gives the `funHan`.

## Inputs
* `p` – precision of `pi` and of the sine
* `k` – Newton steps

## Hypotheses
* `h` – the operand tree is sound

## Conclusion
* the `sin` tree is sound
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

/-- The `sin` node over a sound float tree is sound. -/
theorem SyntaxTree.isSound_sinFloat [Float.ToRat 𝕋] (p k : ℕ) (h : SyntaxTree.IsSoundFloat B t) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.sinFloat p k t) :=
  ⟨h, fun x hx => SyntaxTree.contains_of_outerFloat
    (Float.Interval.sin_outer p _)
    (SyntaxTree.encloses_of_soundFloat h x hx),
    SyntaxTree.funHanSinFloat_sound p k _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
